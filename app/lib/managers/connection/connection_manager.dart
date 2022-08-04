import 'dart:convert';
import 'dart:io';
import 'dart:math';
import 'dart:typed_data';
import 'package:mychips/managers/connection/wyseman_message.dart';
import 'package:web_socket_channel/io.dart';
import 'package:webcrypto/webcrypto.dart';
import 'package:mychips/managers/host/host_config.dart';
import 'package:rxdart/rxdart.dart';
import 'package:flutter_secure_storage/flutter_secure_storage.dart';
import 'connection.dart';
import 'ticket.dart';
import 'key.dart';

class ConnectionManager {
  static final ConnectionManager _instance = ConnectionManager._internal();
  factory ConnectionManager() {
    return _instance;
  }
  ConnectionManager._internal();

  Future<void> initialize(ValueStream<HostConfig> configStream) async {
    _configStream = configStream;
    _configStream.doOnData((event) {
      clearConnection();
    });

    _key = await _loadKeyIfExists();
  }

  late final ValueStream<HostConfig> _configStream;
  static const dbInfo = ['mychips_user', 'wylib'];
  static final BigInt pe = BigInt.from(65537);

  final _connectionSubject = BehaviorSubject<Connection?>();
  get connectionStream => _connectionSubject.stream;

  late Ticket? ticket = null;
  late Key? _key = null;
  get hasKey => _key != null;

  get canConnect => ticket != null || _key != null;

  get connection async {
    if (!_connectionSubject.hasValue || _connectionSubject.value == null) {
      final newConnection = await _establishConnection();
      _connectionSubject.sink.add(newConnection);
      return newConnection;
    }
    return _connectionSubject.value;
  }

  void clearConnection() {
    if (_connectionSubject.valueOrNull != null) {
      _connectionSubject.sink.add(null);
    }
  }

  Future<Connection> _establishConnection() async {
    assert(canConnect, "AppConfig: key or token must be provided before attempting to connect.");

    Connection connection;
    final localKey = _key;
    if (localKey == null) {
      connection = await _connectWithTicket(ticket!);
      await _storeKey(connection.key);
      _key = connection.key;
    } else {
      // TODO: error handling... on certain errors connecting, toss out key and revert to token
      connection = await _connectWithKey(localKey);
    }
    //connection.channel.innerWebSocket!.doOnCancel(clearConnection);
    return connection;
  }

  Future<Connection> _connectWithTicket(Ticket ticket) async {
    final keyPair = await RsaPssPrivateKey.generateKey(2048, pe, Hash.sha256);
    final exPub = await keyPair.publicKey.exportJsonWebKey();
    final exPriv = await keyPair.privateKey.exportJsonWebKey();
    final privateKey = const JsonEncoder().convert(exPriv);

    return Connection(
        await _openChannel(
            {'token': ticket.token, 'pub': _mapToBase64Json(exPub)}, ticket.user!, {}),
        Key(_configStream.value.host, _configStream.value.port, ticket.user!, privateKey));
  }

  String _mapToBase64Json(Map input) {
    return base64.encode(utf8.encode(JsonEncoder().convert(input)));
  }

  Future<Connection> _connectWithKey(Key key) async {
    RsaPssPrivateKey myKey =
        await RsaPssPrivateKey.importJsonWebKey(jsonDecode(key.privateKey), Hash.sha256);
    final cookie = Random().nextDouble().toString(); // TODO: make this cryptographically random
    return await (HttpClient()..badCertificateCallback = ((cert, host, port) => true))
        .getUrl(Uri.parse(
            "https://${_configStream.value.host}:${_configStream.value.httpPort}/clientinfo"))
        .then((HttpClientRequest request) => (request
              ..headers.add('user-agent', 'Wyseman Websocket Client API')
              ..headers.add('cookie', cookie))
            .close())
        .then((HttpClientResponse response) async {
      // TODO: this code assumes the entire message will be received in one response; this isn't true in general
      final message =
          WysemanMessage.fromJson(jsonDecode(await response.transform(utf8.decoder).first));
      return Connection(
          await _openChannel(
              {
                'sign': base64.encode(
                    await myKey.signBytes(utf8.encode(const JsonEncoder().convert(message)), 128)),
                'date': message.date
              },
              key.user,
              {'user-agent': 'Wyseman Websocket Client API', 'cookie': message.cookie}),
          key);
    });
  }

  static const _keyStorageKey = "key";

  Future<void> _storeKey(Key key) async =>
      await const FlutterSecureStorage().write(key: _keyStorageKey, value: jsonEncode(key));

  static Future<Key?> _loadKeyIfExists() async {
    final keyString = await const FlutterSecureStorage().read(key: _keyStorageKey);
    return keyString != null ? Key.fromJson(jsonDecode(keyString)) : null;
  }

  Future<void> clearKey() async {
    await const FlutterSecureStorage().delete(key: _keyStorageKey);
    _key = null;
  }

  static String _urlQueryFromMap(Map data) =>
      (data.isNotEmpty ? "?" : "") +
      data.keys
          .map((key) => "${Uri.encodeComponent(key)}=${Uri.encodeComponent(data[key])}")
          .join("&");

  static String _encodeDbInfo(List<String> dbInfo) =>
      base64.encode(utf8.encode(const JsonEncoder().convert(dbInfo)));

  Future<IOWebSocketChannel> _openChannel(
          Map<String, dynamic> authAttributes, String user, Map<String, dynamic> headers) async =>
      IOWebSocketChannel.connect(
          Uri.parse(
              "wss://${_configStream.value.host}:${_configStream.value.port}/${_urlQueryFromMap({
            "user": user,
            "db": _encodeDbInfo(_configStream.value.dbInfo)
          }..addAll(authAttributes))}"),
          headers: headers);
}
