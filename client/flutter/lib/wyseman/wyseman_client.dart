// @dart=2.9
//// A module to connect a dart client to a MYCHIPs server via websocket
// see an implementation in test.dart

import 'dart:convert';
import 'dart:async';
import 'dart:io';
import 'dart:math';
import 'dart:typed_data';
import 'package:path_provider/path_provider.dart';
import 'package:web_socket_channel/io.dart';
// import 'package:web_socket_channel/status.dart' as status;
// import 'package:web_socket_channel/web_socket_channel.dart';
import 'package:webcrypto/webcrypto.dart';

class WysemanCredential {
  String host;
  int wsPort;
  String token;
  String key;
  int keyLength;
  String user;
}

class WysemanRequestObject {
  String id = 'list_cmd';
  String action = 'select';
  String view = 'mychips.users_v';
  List<String> fields = ['id', 'std_name', 'peer_endp'];
}

// class WysemanConfig {
//   List<String> dbInfo;
//   int httpPort;
//   String ca;

//   WysemanConfig(List<String> dbInfo, int httpPort, String ca) {
//     this.dbInfo = dbInfo;
//     this.httpPort = httpPort;
//     this.ca = ca;
//   }
// }

class WysemanMessage {
  String ip;
  String cookie;
  String userAgent;
  String date;

  Map<String, dynamic> toJson() =>
      {'ip': ip, 'cookie': cookie, 'userAgent': userAgent, 'date': date};
}

class Client {
  int httpPort;
  List<String> dbInfo;
  int keyLength;
  String ca;
  IOWebSocketChannel ws;
  //WysemanConfig config;

// keylength, dbinfo, & http_port
  Client(List<String> db, int port, String ca) {
    httpPort = port;
    dbInfo = db;
    this.ca = ca;
    //this.keyLength = keyLength;
  }

//host port, user token/key
  connect(WysemanCredential credential, var openCB) async {
    int wsport = credential.wsPort;
    String token = credential.token;
    String key = credential.key;
    int keyLength = credential.keyLength != null ? credential.keyLength : 2048;
    String user = credential.user;
    String host = credential.host;
    var rand = new Random();
    String authString;
    JsonEncoder js = new JsonEncoder();
    Map<String, dynamic> socketHeaders = new Map();
    var connectArray;

    openWebSocket(authString, socketHeaders) {
      //db codes to base64
      String encodedString = js.convert(dbInfo);
      List<int> bytes = utf8.encode(encodedString);
      String dbHex = base64.encode(bytes);
      //form query string with authstring parameter
      String query = 'user=$user&db=$dbHex&$authString';
      //form full connection url
      String url = 'wss://$host:$wsport/?$query';
      print("URL " + url);
      //send connect array
      //connectArray = [url, socketHeaders];
      //open websocket connection
      final channel = IOWebSocketChannel.connect(Uri.parse(url), headers: socketHeaders);
      // String toSend =
      //     "{ id: 'list_cmd', action: 'select', view: 'mychips.users_v', fields: ['id', 'std_name', 'peer_endp']}";
      // channel.sink.add(toSend);
      // print(channel.stream);
    }

    ;

    if (token != null) {
      print('has token');

      //Generate key pair

      BigInt pe = BigInt.from(65537);

      KeyPair keyPair = await RsaPssPrivateKey.generateKey(keyLength, pe, Hash.sha256);
      RsaPssPrivateKey myPrivKey = keyPair.privateKey;
      RsaPssPublicKey myPubKey = keyPair.publicKey;

      var exPub = await myPubKey.exportJsonWebKey();
      var exPriv = await myPrivKey.exportJsonWebKey();

      //Build login object

      var loginTest = {
        'login': {
          'host': '$host',
          'port': '$wsport',
          'user': '${user}',
          'privateKey': '${js.convert(exPriv)}'
        }
      };

      final directory = await getApplicationDocumentsDirectory();
      File myFile = await new File((directory.path + '/key.txt'));
      myFile.writeAsString(jsonEncode(loginTest));

      //build token auth string
      authString = 'token=' + token + '&pub=' + base64.encode(utf8.encode(js.convert(exPub)));

      openWebSocket(authString, null);
      key = loginTest['login']['privateKey'];
    }

    if (key != null) {
      Map<String, dynamic> keyJson = jsonDecode(key);
      print(keyJson);
      RsaPssPrivateKey myKey = await RsaPssPrivateKey.importJsonWebKey(keyJson, Hash.sha256);

      String origin = "https://" + host.toString() + ":" + httpPort.toString();
      String endpoint = "/clientinfo";

      print('making call to ${origin + endpoint}');
      HttpClient client = new HttpClient();
      //magic line that just accepts all cert stuff
      client.badCertificateCallback = ((X509Certificate cert, String host, int port) => true);

      await client.getUrl(Uri.parse(origin + endpoint)).then((HttpClientRequest request) {
        request.headers.add('user-agent', 'Wyseman Websocket Client API');
        request.headers.add('cookie', rand.nextDouble().toString());
        // print('headers set');
        // print(request.headers);
        return request.close();
      }).then((HttpClientResponse response) {
        final completer = Completer<void>();
        response.transform(utf8.decoder).listen((contents) async {
          print(contents);
          Map<String, dynamic> data = jsonDecode(contents);
          WysemanMessage message = new WysemanMessage();

          message.ip = data['ip'];
          message.cookie = data['cookie'];
          message.userAgent = data['userAgent'];
          message.date = data['date'];

          //Printing to verify connection string

          List<int> newMessage = utf8.encode(js.convert(message));
          File newMessageFile =
              await new File('/tmp/.key.txt'); //remember this is in the Docker container
          newMessageFile.writeAsBytesSync(newMessage, flush: true);

          // sign bytes

          Uint8List sign = await myKey.signBytes(newMessage, 128);

          socketHeaders['user-agent'] = 'Wyseman Websocket Client API';
          socketHeaders['cookie'] = message.cookie;
          authString =
              'sign=' + base64Url.encode(sign).replaceAll('==', '') + '&date=' + message.date;

          print("Auth String: " + authString);
          openWebSocket(authString, socketHeaders);
          completer.complete();
        });
        return completer.future;
      });
    }
    return connectArray;
  }
}
