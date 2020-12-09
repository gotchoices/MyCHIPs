import 'package:flutter/material.dart';
import 'package:flutter/rendering.dart';
import 'package:flutter_app/user_info.dart';
import 'tally_list_page.dart';

import 'main.dart';

class SignInPage extends StatefulWidget {
  @override
  SignInPageState createState() => new SignInPageState();
}

class SignInPageState extends State<SignInPage> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: Text("MyChips")),
      body: buildPage(),
      drawer: MainDrawer(),
    );
  }

  Widget buildPage() {
    return Center(child: Column(children: [createInputs(), createButtons()]));
  }

  Widget createInputs() {
    return Container(
        child: Padding(
      padding: EdgeInsets.only(
        top: (MediaQuery.of(context).size.height / 4),
      ),
      child: Text(
        'A New Approach to Currency',
        style: TextStyle(fontSize: 48),
        textAlign: TextAlign.center,
      ),
    ));
  }

  Widget createButtons() {
    return Container(
        child: Padding(
            padding: EdgeInsets.only(top: 60, left: 10, right: 10),
            child: Column(children: [
              MaterialButton(
                  onPressed: () {
                    Navigator.push(
                        context,
                        new MaterialPageRoute(
                            builder: (BuildContext context) =>
                                new UserInfoPage()));
                  },
                  child: Text('Get Started', style: TextStyle(fontSize: 20)),
                  color: Colors.amber,
                  textColor: Colors.black,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width / 1.5)),
              Padding(
                padding: EdgeInsets.only(top: 10),
              ),
              MaterialButton(
                  onPressed: () {
                    Navigator.push(
                        context,
                        new MaterialPageRoute(
                            builder: (BuildContext context) =>
                                new TallyListPage()));
                  },
                  child: Text('Connect Device', style: TextStyle(fontSize: 20)),
                  color: Colors.amber,
                  textColor: Colors.black,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width / 1.5))
            ])));
  }
}
