import 'package:flutter/material.dart';
import './view/home_page.dart';
import 'objects/singletons.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  initiateSingletons();
  runApp(MyChips());
}
