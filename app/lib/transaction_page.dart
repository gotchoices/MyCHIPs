import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'main.dart';

class TransactionPage extends StatefulWidget {
  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
        appBar: AppBar(
          title: Text("MyCHIPs Transaction"),
          actions: [
            CircleAvatar(backgroundImage:
            new NetworkImage("https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),)],
        ),
        body: buildPage(),
        drawer: MainDrawer()
    );
  }

  Widget buildPage() {
    return Column(
        children: [
          createPaymentTextFields(),
          Divider(
              thickness: 2,
              color: Colors.black
          ),
          Container(
              child: Padding(
                padding: EdgeInsets.only(bottom: 100, left: 5),
                child: TextField(
                  decoration: InputDecoration(
                      border: InputBorder.none,
                      hintText: "Purpose:",
                      hintStyle: TextStyle(color: Colors.grey)),
                  style: TextStyle(color: Colors.black),),)
          ),
          createButtons()
        ]);
  }

  Widget createButtons() {
    return Container(
        child: Padding(
            padding: EdgeInsets.all(10),
            child: Row(
                children: [
                  Expanded(
                      flex: 1,
                      child: MaterialButton(
                          onPressed: () {
                            print("pressed 'pay'");},
                          child: Text('PAY',
                              style: TextStyle(fontSize: 20)),
                          color: Colors.amber,
                          textColor: Colors.black,
                          elevation: 5,
                          height: 50,
                          minWidth: (MediaQuery.of(context).size.width) / 2.25)),
                  MaterialButton(
                      onPressed: () {
                        print("pressed 'request'");},
                      child: Text('REQUEST',
                          style: TextStyle(fontSize: 20)),
                      color: Colors.amber,
                      textColor: Colors.black,
                      elevation: 5,
                      height: 50,
                      minWidth: (MediaQuery.of(context).size.width) / 2.25)
                ])
        )
    );
  }

  Widget createPaymentTextFields() {
    return Container(
        child: Padding(
            padding: EdgeInsets.only(left: 5),
            child: Row(
                mainAxisSize: MainAxisSize.min,
                children: [
                  Expanded(
                      flex: 2,
                      child: TextField(
                          onChanged: (input) {
                            searchTallies(input);},
                          decoration: InputDecoration(
                              border: InputBorder.none,
                              hintText: "To Whom:",
                              hintStyle: TextStyle(color: Colors.grey)),
                          style: TextStyle(color: Colors.black))),
                  Expanded(
                      flex: 0,
                      child: Text("\$")),
                  Expanded(
                      child: TextField(
                          decoration: InputDecoration(
                              border: InputBorder.none,
                              hintText: "0",
                              hintStyle: TextStyle(color: Colors.grey)),
                          style: TextStyle(color: Colors.black),
                          keyboardType: TextInputType.number,
                          inputFormatters: [FilteringTextInputFormatter.digitsOnly]))
                ])
        )
    );
  }

  void searchTallies(input){
    //put logic to filter searched users here (probably the same as what's on the tally page)
    print(input);
  }
}