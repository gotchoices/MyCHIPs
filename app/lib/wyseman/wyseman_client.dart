import 'dart:convert';
import 'dart:convert' show utf8;
import 'dart:io';
import 'dart:math';
import 'dart:typed_data';
import 'package:flutter/cupertino.dart';
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

@immutable
class WysemanCredential {
  final String host;
  final int port;
  final String token;
  final String key;
  final int keyLength;
  const WysemanCredential(
      this.host, this.port, this.token, this.key, this.keyLength);
}

class WysemanRequestObject {
  String id = 'list_cmd';
  String action = 'select';
  String view = 'mychips.users_v';
  List<String> fields = ['id', 'std_name', 'peer_endp'];
}

class WysemanConfig {
  final List<String> DBInfo;
  final int port;
  final String? CaFile;
  WysemanConfig(this.DBInfo, this.port, this.CaFile);
}

class WysemanMessage {
  final String ip;
  final double cookie;
  final String userAgent;
  final String date;
  const WysemanMessage(this.ip, this.cookie, this.userAgent, this.date);

  Map<String, dynamic> toJson() =>
      {'ip': ip, 'cookie': cookie, 'userAgent': userAgent, 'date': date};
}

class Connection {
  final String host;
  final int port;
  final int keyLength;
  final Socket ws;
  final WysemanConfig config;

  const Connection(this.host, this.port, this.keyLength, this.ws, this.config);
}

class Client {
  Future<Connection> connect(WysemanCredential credential, var openCB) async {
    print('connect called');
    final host = credential.host;
    final port = credential.port;
    String token = credential.token;
    String key = credential.key;
    int keyLength = credential.keyLength != null ? credential.keyLength : 2048;
    var rand = Random();
    var dbinfo = ['mychips_user', 'wylib'];
    final config = WysemanConfig(dbinfo, credential.port, null);

    if (token != null) {
      print('has token');
    } else if (key != null) {
      //implement later
    } else {
      //throw error
    }

    String origin = "https://" + host + ":" + port.toString();
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

    HttpClient client = HttpClient();
    //magic line that just accepts all cert stuff
    client.badCertificateCallback =
        ((X509Certificate cert, String host, int port) => true);
    try {
      final request = await client.getUrl(Uri.parse(origin + endpoint));
      request.headers.add('user-agent', 'Wyseman Websocket Client API');
      request.headers.add('cookie', rand.nextDouble().toString());
      // print('headers set');
      // print(request.headers);

      final response = await request.close();
      final contents = await response.transform(utf8.decoder).first;
      print(contents);
      Map<String, dynamic> data = jsonDecode(contents);
      JsonEncoder js = JsonEncoder();
      String hexString =
          StringToHex.toHexString(js.convert(dbinfo)).substring(3);

      // print('data');
      // print(data);

      final message = WysemanMessage(data['ip'], double.parse(data['cookie']),
          data['userAgent'], data['date']);

      final utf8Thing = Uint8List.fromList(utf8.encode(js.convert(message)));

      // print('hexstring:');
      // print(hexString);
      // print('uft8:');
      // print(utf8Thing);

      final keyGen = RSAKeyGenerator();

      final secureRandom = FortunaRandom();
      final random = Random.secure();

      List<int> seeds = [];
      for (int i = 0; i < 32; i++) {
        seeds.add(random.nextInt(255));
      }

      secureRandom.seed(KeyParameter(Uint8List.fromList(seeds)));

      keyGen.init(ParametersWithRandom(
          RSAKeyGeneratorParameters(BigInt.parse('65537'), keyLength, 64),
          secureRandom));

      var keyPair = keyGen.generateKeyPair();

      // print('key pairs genereated');

      final signer = RSASigner(SHA256Digest(), '0609608648016503040201');
      signer.init(true, PrivateKeyParameter<RSAPrivateKey>(keyPair.privateKey));

      RSASignature sig = signer.generateSignature(utf8Thing);
      String sigString = '';
      for (int i in sig.bytes) {
        sigString += i.toString();
      }

      String user = 'admin';
      String db = hexString;
      DateTime NOW = DateTime.now();
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

      Map<String, dynamic> socketHeaders = Map();
      socketHeaders['user-agent'] = 'Wyseman Websocket Client API';
      socketHeaders['cookie'] = message.cookie;

      String? caFile;
      try {
        print('finding file');
        File f = File(local + '/spa_ca.crt');
        String contents = await f.readAsString();
        caFile = contents;
        socketHeaders['ca'] = contents;
      } catch (e) {
        print('err');
        await writeSPA();
      }

      // final channel = IOWebSocketChannel.connect(Uri.parse(url),
      //     headers: socketHeaders);
      // channel.stream.listen((event) {
      //   channel.sink.add('recieved');
      //   channel.sink.close(status.goingAway);
      // });
      //
      SecurityContext wsContext = SecurityContext();
      AsciiDecoder asciiBoi = AsciiDecoder();
      wsContext.setTrustedCertificates(local + '/spa_ca.crt');
      /*
        TODO:
        THIS IS THE FINAL SECTION, WHERE THE CONNECTION ULTIMATELY FAILS
        */
      SecureSocket s = await SecureSocket.connect(host, port,
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
      return Connection(
          host, port, keyLength, s, WysemanConfig(dbinfo, port, caFile));
    } catch (error) {
      print('there was an error: $error');
      rethrow;
    }
  }
}

Future<String> get _localPath async {
  final directory = await getApplicationDocumentsDirectory();
  return directory.path;
}

Future<File> writeSPA() async {
  print("writing spa");
  const String spaFile = "-----BEGIN CERTIFICATE-----\n" +
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
  File f = File('$dir/spa_ca.crt');
  var temp = await f.writeAsString(spaFile);

  print('spa written');
  return temp;
}
