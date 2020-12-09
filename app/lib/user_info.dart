import 'package:flutter/cupertino.dart';
import 'package:flutter/material.dart';
import 'package:flutter_app/main.dart';
import 'package:flutter_app/tally_list_page.dart';

class UserInfoPage extends StatefulWidget {
  @override
  UserInfoPageState createState() => new UserInfoPageState();
}

class UserInfoPageState extends State<UserInfoPage> {
  bool showContact = false;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: Text("User Information")),
      body: buildPage(),
      drawer: MainDrawer(),
    );
  }

  Widget buildPage() {
    return (Container(
        alignment: Alignment.topCenter,
        child: Padding(
            padding: EdgeInsets.all(16),
            child: Column(
              children: [
                Icon(
                  Icons.person,
                  size: 128,
                ),
                Container(
                    child: Padding(
                  padding: EdgeInsets.only(top: 16),
                  child: Column(
                    children: [
                      TextField(
                        decoration: InputDecoration(
                            hintText: "Display Name",
                            border: InputBorder.none,
                            hintStyle: TextStyle(color: Colors.grey)),
                      ),
                      TextField(
                        decoration: InputDecoration(
                            hintText: "First Name",
                            border: InputBorder.none,
                            hintStyle: TextStyle(color: Colors.grey)),
                      ),
                      TextField(
                        decoration: InputDecoration(
                            hintText: "Last Name",
                            border: InputBorder.none,
                            hintStyle: TextStyle(color: Colors.grey)),
                      ),
                      TextField(
                        decoration: InputDecoration(
                            hintText: "Email",
                            border: InputBorder.none,
                            hintStyle: TextStyle(color: Colors.grey)),
                      ),
                      TextField(
                        decoration: InputDecoration(
                            hintText: "Phone",
                            border: InputBorder.none,
                            hintStyle: TextStyle(color: Colors.grey)),
                      ),
                      Row(
                        children: [
                          Switch(
                              value: showContact,
                              onChanged: (value) {
                                setState(() {
                                  showContact = !showContact;
                                });
                              }),
                          Text("Display Contact Info on public profile?  "),
                          Text(showContact ? "Yes" : "No")
                        ],
                      ),
                      MaterialButton(
                          onPressed: () {
                            Navigator.push(
                                context,
                                new MaterialPageRoute(
                                    builder: (BuildContext context) =>
                                        new TallyListPage()));
                          },
                          child: Text('Save Changes',
                              style: TextStyle(fontSize: 20)),
                          color: Colors.amber,
                          textColor: Colors.black,
                          elevation: 5,
                          height: 50,
                          minWidth: (MediaQuery.of(context).size.width))
                    ],
                  ),
                ))
              ],
            ))));
  }
}
