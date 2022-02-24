import 'package:flutter/material.dart';
import './view/home_page.dart';
import 'managers/connection/connection_manager.dart';
import 'managers/host/host_manager.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  ConnectionManager().initialize(HostManager().configStream);
  runApp(MyChips());
}
