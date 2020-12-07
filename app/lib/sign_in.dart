import 'package:flutter/material.dart';
import 'package:flutter/rendering.dart';

import 'main.dart';

class SignInPage extends StatefulWidget {
  @override
  SignInPageState createState() => new SignInPageState();
}

class SignInPageState extends State<SignInPage> {
  String username = '';
  String password = '';

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: Text("MyChips")),
      body: buildPage(),
      drawer: MainDrawer(),
    );
  }

  Widget buildPage() {
    return Column(children: [createInputs(), createButtons()]);
  }

  Widget createInputs() {
    return Container(
        child: Padding(
            padding: EdgeInsets.only(top: 200, left: 10, right: 10),
            child: Column(
              children: [
                TextField(
                  decoration: InputDecoration(
                      border: InputBorder.none,
                      hintText: "Username",
                      hintStyle: TextStyle(color: Colors.grey)),
                  style: TextStyle(color: Colors.black),
                ),
                TextField(
                  decoration: InputDecoration(
                      border: InputBorder.none,
                      hintText: "Password",
                      hintStyle: TextStyle(color: Colors.grey)),
                  style: TextStyle(color: Colors.black),
                )
              ],
            )));
  }

  Widget createButtons() {
    return Container(
        child: Padding(
            padding: EdgeInsets.only(top: 150, left: 10, right: 10),
            child: Row(children: [
              Expanded(
                  flex: 1,
                  child: MaterialButton(
                      onPressed: () {
                        print("validating inputs");
                      },
                      child: Text('SIGN IN', style: TextStyle(fontSize: 20)),
                      color: Colors.amber,
                      textColor: Colors.black,
                      elevation: 5,
                      height: 50,
                      minWidth: (MediaQuery.of(context).size.width) / 2.25)),
              MaterialButton(
                  onPressed: () {
                    print("pressed 'request'");
                  },
                  child: Text('SIGN UP', style: TextStyle(fontSize: 20)),
                  color: Colors.amber,
                  textColor: Colors.black,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width) / 2.25)
            ])));
  }
}
