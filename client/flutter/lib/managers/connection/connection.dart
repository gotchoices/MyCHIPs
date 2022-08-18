import 'package:web_socket_channel/io.dart';
import 'key.dart';

class Connection {
  final IOWebSocketChannel channel;
  final Key key;

  const Connection(this.channel, this.key);
}
