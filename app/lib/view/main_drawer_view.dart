import 'package:flutter/material.dart';
import '../objects/singletons.dart';
import '../presenter/user_info_presenter.dart';
import '../view/pending_page.dart';
import '../view/tally_search_page.dart';
import '../view/user_info_page.dart';

import 'create_tally_page.dart';
import 'home_page.dart';

class MainDrawer extends StatefulWidget {
  const MainDrawer({Key? key}) : super(key: key);

  @override
  MainDrawerState createState() => MainDrawerState();
}

class MainDrawerState extends State<MainDrawer> {
  UserInfo userInfo = UserInfo();

  MainDrawerState() {
    userInfo.account ??= UserInfoPresenter().getAccountData();
  }

  @override
  Widget build(BuildContext context) {
    return Drawer(
        child: ListView(
      children: <Widget>[
        UserAccountsDrawerHeader(
          accountName: Text(userInfo.account?.displayName ?? "-",
              style: const TextStyle(fontWeight: FontWeight.bold)),
          accountEmail: Text(userInfo.account?.email ?? "-"),
          currentAccountPicture: GestureDetector(
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => UserInfoPage(false)));
            },
            child: CircleAvatar(
                child: Text(
                    userInfo.account?.displayName.substring(0, 1) ?? "-",
                    style: const TextStyle(
                        fontSize: 45,
                        fontWeight: FontWeight.w700,
                        color: Color(0xffffffff))),
                backgroundColor: const Color(0xfff3a43e)),
          ),
        ),
        ListTile(
            title: const Text("Home",
                style: TextStyle(fontWeight: FontWeight.bold)),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => HomePage()));
            }),
        ListTile(
            title: const Text("My Tallies",
                style: TextStyle(fontWeight: FontWeight.bold)),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => TallySearchPage(0)));
            }),
        ListTile(
            title: const Text("Create a New Tally",
                style: TextStyle(fontWeight: FontWeight.bold)),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => CreateTallyPage()));
            }),
        ListTile(
            title: const Text("Pending Transactions",
                style: TextStyle(fontWeight: FontWeight.bold)),
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
