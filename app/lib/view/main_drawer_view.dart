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
              accountName: Text(userInfo.account.displayName),
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
                    backgroundImage: NetworkImage(
                        "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),
                  )),
            ),
            ListTile(
                title: Text("Home"),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => HomePage()));
                }),
            ListTile(
                title: Text("My Tallies"),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => TallySearchPage(0)));
                }),
            ListTile(
                title: Text("Create a New Tally"),
                onTap: () {
                  Navigator.push(
                      context,
                      MaterialPageRoute(
                          builder: (BuildContext context) => CreateTallyPage()));
                }),
            ListTile(
                title: Text("Pending Transactions"),
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