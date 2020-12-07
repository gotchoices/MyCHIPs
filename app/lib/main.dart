import 'package:flutter/material.dart';
import 'package:flutter_app/transaction_page.dart';
import 'tally_list_page.dart';
import 'sign_in.dart';

void main() {
  runApp(MyChips());
}

class MyChips extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      theme: ThemeData(primaryColor: Color(0xff53ab77)),
      home: SignInPage(),
      // Scaffold(appBar: AppBar(title: Text("MyCHIPs"),),
    );
  }
}

class HomePage extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return new Scaffold(
      appBar: AppBar(title: Text("MyCHIPs home")),
      drawer: MainDrawer(),
    );
  }
}

class MainDrawer extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return new Drawer(
        child: ListView(
      children: <Widget>[
        new UserAccountsDrawerHeader(
          accountName: new Text("myAccount"),
          accountEmail: new Text("myemail@gmail.com"),
          currentAccountPicture: new CircleAvatar(
            backgroundImage: new NetworkImage(
                "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),
          ),
        ),
        new ListTile(
            title: new Text("Home"),
            onTap: () {
              Navigator.push(
                  context,
                  new MaterialPageRoute(
                      builder: (BuildContext context) => new HomePage()));
            }),
        new ListTile(
            title: new Text("My Tallies"),
            onTap: () {
              Navigator.push(
                  context,
                  new MaterialPageRoute(
                      builder: (BuildContext context) => new TallyListPage()));
            }),
        new ListTile(
            title: new Text("New Transaction"),
            onTap: () {
              Navigator.push(
                  context,
                  new MaterialPageRoute(
                      builder: (BuildContext context) =>
                          new TransactionPage()));
            })
      ],
    ));
  }
}
