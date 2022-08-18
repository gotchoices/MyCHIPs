class HostConfig {
  final String host;
  final int httpPort;
  final int port;
  final List<String> dbInfo;
  const HostConfig(
      {required this.host, required this.httpPort, required this.port, required this.dbInfo});
}
