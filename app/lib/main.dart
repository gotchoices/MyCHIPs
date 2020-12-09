import 'package:flutter/material.dart';
import 'package:flutter_app/transaction_page.dart';
import 'package:flutter_app/user_info.dart';
import 'tally_list_page.dart';
import 'sign_in.dart';
import 'create_tally_page.dart';

void main() {
  runApp(MyChips());
}

class MyChips extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      theme: ThemeData(primaryColor: Color(0xff53ab77)),
      //TODO: Determine if a user is logged in already, if so go to HomePage instead of Login page
      home: SignInPage()
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
        child:ListView(
          children: <Widget>[
            UserAccountsDrawerHeader(
              accountName: Text("myAccount"),
              accountEmail: Text("myemail@gmail.com"),
              currentAccountPicture: GestureDetector (
                onTap: () {
                  Navigator.push(context,
                    MaterialPageRoute(
                      builder: (BuildContext context) => UserInfoPage(false)));
                },
                child: CircleAvatar(
                  backgroundImage: NetworkImage("https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),
              )),
            ),
            ListTile(
              title: Text("Home"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                    builder: (BuildContext context) => HomePage()
                ));
            }),
            ListTile(
              title: Text("My Tallies"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                    builder: (BuildContext context) => TallyListPage()
                ));
              }),
            ListTile(
              title: Text("Create a New Tally"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                  builder: (BuildContext context) => CreateTallyPage()
                ));
              }),
            ListTile(
                title: new Text("New Transaction"),
                onTap: () {
                  Navigator.push(context, new MaterialPageRoute(
                      builder: (BuildContext context) => new TransactionPage()
                  ));
                })
          ],
        )
    );
  }
}
