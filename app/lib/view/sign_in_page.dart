import 'package:flutter/material.dart';
import 'package:flutter/rendering.dart';
import 'user_info_page.dart';
import 'home_page.dart';
import '../services.dart';

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
                                new UserInfoPage(true)));
                  },
                  child: Text('Get Started', style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
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
                                //TODO: figure out how reconnection works and create a reconnect page
                                new HomePage()));
                  },
                  child: Text('Reconnect', style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width / 1.5)),
              MaterialButton(
                onPressed: () {
                  Services.getUserTallies(1);
                },
                child: Text('Test Mock API'),
              )
            ])));
  }
}
