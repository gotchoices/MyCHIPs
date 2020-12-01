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
        appBar: AppBar(
          title: Text("Tally with " + widget.friend),
          actions: [
            CircleAvatar(backgroundImage: new NetworkImage("https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),)
          ],),
        body: buildPage(),
        drawer: MainDrawer()
    );
  }

  Widget buildPage() {
    return Stack(
      children: [
        buildBalance(),
        buildButtons()

      ]
    );
  }

  Widget buildBalance() {
    return Padding(
      padding: const EdgeInsets.all(15),
      child: Align(
        alignment: Alignment.topCenter,
        child: Column(
        children: [
          Text("₵" + widget.balance.toString(),  style: TextStyle(fontSize: 75)),
          Text("balance",  style: TextStyle(fontSize: 25)),
        ],
    )));
  }

  Widget buildHistory() {

  }

  Widget buildButtons() {
    var maxButtonWidth = (MediaQuery.of(context).size.width) / 2.25;
    return Row(children: [
    Padding(
    padding: const EdgeInsets.all(10),
    child: Align(
      alignment: Alignment.bottomLeft,
      child: MaterialButton(
        onPressed: () {
          print("pressed 'pay'");
        },
        child: const Text('PAY', style: TextStyle(fontSize: 20)),
        color: Colors.blue,
        textColor: Colors.white,
        elevation: 5,
        height: 50,
        minWidth: maxButtonWidth
      ))),
    Padding(
      padding: const EdgeInsets.all(10),
      child: Align(
        alignment: Alignment.bottomRight,
        child: MaterialButton(
          onPressed: () {
            print("pressed 'request'");
          },
          child: const Text('REQUEST', style: TextStyle(fontSize: 20)),
          color: Colors.blue,
          textColor: Colors.white,
          elevation: 5,
          height: 50,
          minWidth: maxButtonWidth
        )))
    ]);
  }
}