import 'host_config.dart';
import 'package:rxdart/rxdart.dart';

class HostManager {
  static final HostManager _instance = HostManager._internal();
  factory HostManager() {
    return _instance;
  }
  HostManager._internal();

  final _configSubject = BehaviorSubject<HostConfig>.seeded(const HostConfig(
      host: "mychips0", httpPort: 8000, port: 54320, dbInfo: ['mychips_user', 'wylib']));
  get configStream => _configSubject.stream;

  void changeConfig(HostConfig newConfig) {
    _configSubject.sink.add(newConfig);
  }
}
