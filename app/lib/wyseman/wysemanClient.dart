import 'dart:convert';
import 'dart:convert' show utf8;
import 'dart:io';
import 'dart:math';
import 'dart:typed_data';
import 'package:path_provider/path_provider.dart';
import 'package:pointycastle/api.dart';
import 'package:pointycastle/export.dart';
import 'package:pointycastle/key_generators/api.dart';
import 'package:pointycastle/key_generators/rsa_key_generator.dart';
import 'package:pointycastle/random/fortuna_random.dart';
import 'package:web_socket_channel/io.dart';
import 'package:web_socket_channel/status.dart' as status;
import 'package:string_to_hex/string_to_hex.dart';
// import 'package:http/http.dart' as http;

class WysemanCredential {
  String host;
  int port;
  String token;
  String key;
  int keyLength;
}

class WysemanRequestObject {
  String id = 'list_cmd';
  String action = 'select';
  String view = 'mychips.users_v';
  List<String> fields = ['id', 'std_name', 'peer_endp'];
}

class WysemanConfig {
  List<String> DBInfo;
  int port;
  String CaFile;
}

class WysemanMessage {
  String ip;
  double cookie;
  String userAgent;
  String date;

  Map<String, dynamic> toJson() =>
      {'ip': ip, 'cookie': cookie, 'userAgent': userAgent, 'date': date};
}

class Client {
  String host;
  int port;
  int keyLength;
  File ca;
  IOWebSocketChannel ws;
  WysemanConfig config;

  void connect(WysemanCredential credential, var openCB) async {
    print('connect called');
    this.host = credential.host;
    this.port = credential.port;
    String token = credential.token;
    String key = credential.key;
    int keyLength = credential.keyLength != null ? credential.keyLength : 2048;
    var rand = new Random();
    var dbinfo = ['mychips_user', 'wylib'];
    this.config = new WysemanConfig();
    this.config.DBInfo = dbinfo;
    this.config.port = credential.port;

    if (token != null) {
      print('has token');
    } else if (key != null) {
      //implement later
    } else {
      //throw error
    }

    String origin = "https://" + this.host + ":" + this.port.toString();
    String endpoint = "/clientinfo";

    // print('making call to ${origin + endpoint}');
    String current = await _localPath;
    print(current);
    String local = await _localPath;

    // try {
    //   print('finding file');
    //   File f = new File(local + '/spa_ca.crt');
    //   print('file found');
    //   String contents = await f.readAsString();
    //   this.config.CaFile = contents;
    //   print('contents there');
    // } catch (e) {
    //   print('err');
    // }

    HttpClient client = new HttpClient();
    //magic line that just accepts all cert stuff
    client.badCertificateCallback =
    ((X509Certificate cert, String host, int port) => true);

    try {
      client
          .getUrl(Uri.parse(origin + endpoint))
          .then((HttpClientRequest request) {
        request.headers.add('user-agent', 'Wyseman Websocket Client API');
        request.headers.add('cookie', rand.nextDouble().toString());
        // print('headers set');
        // print(request.headers);

        return request.close();
      }).then((HttpClientResponse response) {
        response.transform(utf8.decoder).listen((contents) async {
          print(contents);
          Map<String, dynamic> data = jsonDecode(contents);
          WysemanMessage message = new WysemanMessage();
          JsonEncoder js = new JsonEncoder();
          String hexString =
          StringToHex.toHexString(js.convert(this.config.DBInfo))
              .substring(3);

          // print('data');
          // print(data);

          message.ip = data['ip'];
          message.cookie = double.parse(data['cookie']);
          message.userAgent = data['userAgent'];
          message.date = data['date'];

          Uint8List utf8Thing = utf8.encode(js.convert(message));

          // print('hexstring:');
          // print(hexString);
          // print('uft8:');
          // print(utf8Thing);

          final keyGen = RSAKeyGenerator();

          var secureRandom = new FortunaRandom();
          var random = new Random.secure();

          List<int> seeds = [];
          for (int i = 0; i < 32; i++) {
            seeds.add(random.nextInt(255));
          }

          secureRandom.seed(new KeyParameter(new Uint8List.fromList(seeds)));

          keyGen.init(ParametersWithRandom(
              RSAKeyGeneratorParameters(BigInt.parse('65537'), keyLength, 64),
              secureRandom));

          var keyPair = keyGen.generateKeyPair();

          // print('key pairs genereated');

          final signer = RSASigner(SHA256Digest(), '0609608648016503040201');
          signer.init(
              true, PrivateKeyParameter<RSAPrivateKey>(keyPair.privateKey));

          RSASignature sig = signer.generateSignature(utf8Thing);
          String sigString = '';
          for (int i in sig.bytes) {
            sigString += i.toString();
          }

          String user = 'admin';
          String db = hexString;
          DateTime NOW = new DateTime.now();
          String authString = 'sign=' +
              sigString +
              '&date=' +
              NOW.year.toString() +
              '-' +
              NOW.month.toString() +
              '-' +
              NOW.day.toString() +
              'T' +
              NOW.hour.toString() +
              ':' +
              NOW.minute.toString() +
              '.' +
              (NOW.second + NOW.millisecond).toString() +
              'Z';

          String queryString = 'user=$user&db=$db&$authString';
          String url = 'wss://$host:$port?$queryString';
          print('url');
          print(url);

          Map<String, dynamic> socketHeaders = new Map();
          socketHeaders['user-agent'] = 'Wyseman Websocket Client API';
          socketHeaders['cookie'] = message.cookie;

          try {
            print('finding file');
            File f = new File(local + '/spa_ca.crt');
            String contents = await f.readAsString();
            this.config.CaFile = contents;
            socketHeaders['ca'] = contents;
          } catch (e) {
            print('err');
            await writeSPA();
          }

          try {
            // final channel = IOWebSocketChannel.connect(Uri.parse(url),
            //     headers: socketHeaders);
            // channel.stream.listen((event) {
            //   channel.sink.add('recieved');
            //   channel.sink.close(status.goingAway);
            // });
            //
            SecurityContext wsContext = new SecurityContext();
            AsciiDecoder asciiBoi = new AsciiDecoder();
            wsContext.setTrustedCertificates(local + '/spa_ca.crt');
            SecureSocket s = await SecureSocket.connect(this.host, this.port,
                context: wsContext,
                onBadCertificate: ((X509Certificate cert) => true));

            s.listen((event) {
              print('event recived!');
              print(asciiBoi.convert(event));
            });

            String toSend =
                "{ id: 'list_cmd', action: 'select', view: 'mychips.users_v', fields: ['id', 'std_name', 'peer_endp']}";

            // Uint8List encodedMessage = utf8.encode(toSend);
            print(toSend.toString());
            s.write(toSend);
            print('write sent');
            // WebSocket webSocket =
            //     WebSocket.fromUpgradedSocket(s, serverSide: false);

            // webSocket.listen((event) {
            //   print('upgraded');
            // });

            // webSocket.add(toSend);
            print('it was sent');
          } catch (exception) {
            print('error');
            print(exception);
          }
        });
      });
    } catch (error) {
      print('there was an error');
      print(error);
    }
  }
}

Future<String> get _localPath async {
  final directory = await getApplicationDocumentsDirectory();
  return directory.path;
}

Future<File> writeSPA() async {
  print("writing spa");
  final String spaFile = "-----BEGIN CERTIFICATE-----\n" +
      "MIIEVDCCAzygAwIBAgIUReJB6W/Rvy1WALi3IxrqCOF2JHUwDQYJKoZIhvcNAQEL\n" +
      "BQAwgbIxHTAbBgoJkiaJk/IsZAQNDA1jaGlwcGllcy5jaGlwMRkwFwYDVQQKDBBD\n" +
      "aGlwcGllcyBTZXJ2aWNlMRAwDgYDVQQLDAdteWNoaXBzMSEwHwYJKoZIhvcNAQkB\n" +
      "FhJteW5hbWVAbXllbWFpbC5jb20xDzANBgNVBAcMBk15dG93bjELMAkGA1UECAwC\n" +
      "TlkxCzAJBgNVBAYTAlVTMRYwFAYDVQQDDA1jaGlwcGllcy5jaGlwMB4XDTIxMDIx\n" +
      "NTIwMDYzOFoXDTIzMDMwNzIwMDYzOFowgbIxHTAbBgoJkiaJk/IsZAQNDA1jaGlw\n" +
      "cGllcy5jaGlwMRkwFwYDVQQKDBBDaGlwcGllcyBTZXJ2aWNlMRAwDgYDVQQLDAdt\n" +
      "eWNoaXBzMSEwHwYJKoZIhvcNAQkBFhJteW5hbWVAbXllbWFpbC5jb20xDzANBgNV\n" +
      "BAcMBk15dG93bjELMAkGA1UECAwCTlkxCzAJBgNVBAYTAlVTMRYwFAYDVQQDDA1j\n" +
      "aGlwcGllcy5jaGlwMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAxop5\n" +
      "EjutXKFdOlNGNuAXbC9hDs+YWtf++FL4fm/xcrnKfGceSZ0EDA0fdrPydpLIGcax\n" +
      "7chHGZC27RlRhvTGpjaCQB6ALh11e/yTG5dvt12ENoqPe9QHn6kY+63jLLOHofBW\n" +
      "AyeNkZRtSdMbqo02I2mKAZmWjnPSjHdEliHEuk/iS5AeyeLc2Ua/jloGhK2hR7Ly\n" +
      "rLozwGt6PN1iCrzaVWwTa7nvsjar2XcTGFORRM3McKm1n/Xxfvjy6aAz01rXD3ml\n" +
      "WUZKOPV1KWFdLQnJBALohxQeYrLowIKdT8XNmpcgS+U7JY3TIqBHipuSceXGPeFY\n" +
      "y4QTJqt62iRLXcYrYwIDAQABo2AwXjAdBgNVHQ4EFgQUnmXqnlSfELxqiRaUn45S\n" +
      "sZIA2s8wHwYDVR0jBBgwFoAUnmXqnlSfELxqiRaUn45SsZIA2s8wDwYDVR0TAQH/\n" +
      "BAUwAwEB/zALBgNVHQ8EBAMCAQYwDQYJKoZIhvcNAQELBQADggEBAIdXLG/41EzC\n" +
      "v+plU1sRZVuIIfWzxNN49KkgRYD3tOTULKT0PIEwReWNcwEBZ3yAUV2t/3C5K70m\n" +
      "TfD0xU3Ak4Wv2Tvte9cqvY3IOVdbUDG0anv5L8YLuaB0xhjzug2rDcmRGg6PsZft\n" +
      "pXN67LrhHfICmXDDngj6upKX//2qJLq/4l0TkYK6lcRXEOi14IyOUu6m1hwfvVUv\n" +
      "g5Fua9txjuYd5fUA9SKZR2jQdjo8T2+8uNKCVcoh55tfIZbfOV6OjNIZe8lBdaWm\n" +
      "6iZVOUOOIYhB8TBcOChl3oy1om/T+f3O0yU0RIiw+fBAsXs20aPJKF7BR6yRu2gi\n" +
      "6Y+80z9ZF20=\n" +
      "-----END CERTIFICATE-----\n";

  String dir = await _localPath;
  File f = new File('$dir/spa_ca.crt');
  var temp = await f.writeAsString(spaFile);

  print('spa written');
  return temp;
}