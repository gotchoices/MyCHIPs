import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/user_info_presenter.dart';
import 'package:flutter_app/view/pending_page.dart';
import 'package:flutter_app/view/tally_search_page.dart';
import 'package:flutter_app/view/user_info_page.dart';

import 'create_tally_page.dart';
import 'home_page.dart';

class MainDrawer extends StatefulWidget {
  const MainDrawer({Key key}) : super(key: key);

  @override
  MainDrawerState createState() => new MainDrawerState();
}

class MainDrawerState extends State<MainDrawer> {
  UserInfo userInfo = UserInfo();

  MainDrawerState() {
    if (userInfo.account == null)
      userInfo.account = UserInfoPresenter().getAccountData();
  }

  @override
  Widget build(BuildContext context) {
    return new Drawer(
        child: ListView(
          children: <Widget>[
            UserAccountsDrawerHeader(
              accountName: Text(userInfo.account.displayName, style: TextStyle(fontWeight: FontWeight.bold)),
              accountEmail: Text(userInfo.account.email),
              currentAccountPicture: GestureDetector(
                  onTap: () {
                    Navigator.push(
                        context,
                        MaterialPageRoute(
                            builder: (BuildContext context) =>
                                UserInfoPage(false)));
                  },
                  child: CircleAvatar(
                      child: new Text(userInfo.account.displayName.substring(0, 1), style: TextStyle(fontSize: 45, fontWeight: FontWeight.w700, color: Color(0xffffffff))),
                      backgroundColor: Color(0xfff3a43e)),
                ),
            ),
            ListTile(
                title: Text("Home", style: TextStyle(fontWeight: FontWeight.bold)),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => HomePage()));
                }),
            ListTile(
                title: Text("My Tallies", style: TextStyle(fontWeight: FontWeight.bold)),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => TallySearchPage(0)));
                }),
            ListTile(
                title: Text("Create a New Tally", style: TextStyle(fontWeight: FontWeight.bold)),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => CreateTallyPage()));
                }),
            ListTile(
                title: Text("Pending Transactions", style: TextStyle(fontWeight: FontWeight.bold)),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => PendingPage()));
                }),
          ],
        ));
  }
}