// @dart=2.9

import 'package:flutter/material.dart';
import './view/home_page.dart';
import 'objects/singletons.dart';
import './view/test.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  initiateSingletons();
  runApp(MyChipsTest()); //change back to MyChips()
}
