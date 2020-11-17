import 'package:flutter/material.dart';
import 'main.dart';

class TallyPage extends StatefulWidget {
  final String friend;
  final int balance;
  TallyPage(this.friend, this.balance, {Key key}): super(key: key);

  @override
  TallyPageState createState() => new TallyPageState();
}

class TallyPageState extends State<TallyPage> {

  @override
  Widget build(BuildContext context) {
    return Scaffold(
        appBar: AppBar(title: Text("Tally with " + widget.friend)),
        body: buildPage(),
        drawer: MainDrawer()
    );
  }

  Widget buildPage() {
    return Center(
      child: new Text(widget.balance.toString(),  style: TextStyle(fontSize: 32))
    );
  }
}