import 'package:flutter/material.dart';

void main() {
  runApp(MyApp());
}

class MyApp extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
        theme: ThemeData(primaryColor: Color(0xff53ab77)),
        home: Scaffold(appBar: AppBar(title: Text("MyCHIPs"),
        ))
    );
  }
}
