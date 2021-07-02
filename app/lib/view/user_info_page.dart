import 'package:flutter/cupertino.dart';
import 'package:flutter/material.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/user_info_presenter.dart';
import 'main_drawer_view.dart';
import 'scanner_page.dart';

class UserInfoPage extends StatefulWidget {
  final bool registering;
  UserInfoPage(this.registering, {Key key}): super(key: key);
  @override
  UserInfoPageState createState() => new UserInfoPageState();
}

class UserInfoPageState extends State<UserInfoPage> {
  bool showContact;
  bool firstUpdate = true;
  var presenter = new UserInfoPresenter();
  UserInfo userInfo = UserInfo();
  TextEditingController displayNameController;
  TextEditingController firstNameController;
  TextEditingController lastNameController;
  TextEditingController emailController;
  TextEditingController phoneController;
  @override
  Widget build(BuildContext context) {
    showContact = UserInfo().showContact;
    return Scaffold(
      appBar: AppBar(title: Text("User Information")),
      body: buildPage(),
      drawer: (widget.registering) ? null : MainDrawer(),
    );
  }

  Widget buildPage() {
    createControllers();
    return (
        Container(
            alignment: Alignment.topCenter,
            child: Padding(
                padding: EdgeInsets.all(16),
                child: ListView(
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
                                controller: displayNameController,
                                decoration: InputDecoration(
                                    hintText: "Display Name",
                                    border: InputBorder.none,
                                    hintStyle: TextStyle(color: Colors.grey))
                              ),
                              TextField(
                                controller: firstNameController,
                                decoration: InputDecoration(
                                    hintText: "First Name",
                                    border: InputBorder.none,
                                    hintStyle: TextStyle(color: Colors.grey))
                              ),
                              TextField(
                                controller: lastNameController,
                                decoration: InputDecoration(
                                    hintText: "Last Name",
                                    border: InputBorder.none,
                                    hintStyle: TextStyle(color: Colors.grey))
                              ),
                              TextField(
                                controller: emailController,
                                decoration: InputDecoration(
                                    hintText: "Email",
                                    border: InputBorder.none,
                                    hintStyle: TextStyle(color: Colors.grey))
                              ),
                              TextField(
                                controller: phoneController,
                                decoration: InputDecoration(
                                    hintText: "Phone",
                                    border: InputBorder.none, hintStyle: TextStyle(color: Colors.grey))
                              ),
                              Row(
                                children: [
                                  Switch(
                                      value: showContact,
                                      onChanged: (value) {
                                        setState(() {
                                          showContact = !showContact;
                                          UserInfo().showContact = showContact;
                                        });
                                      },
                                      activeColor: Color(0xfff3a43e),
                                  ),
                                  Text("Display Contact Info Publicly?  "),
                                  Text(showContact ? "Yes" : "No")
                                ],
                              ),
                              MaterialButton(
                                  onPressed: () {
                                    presenter.setAccountData(new Account(displayNameController.text, firstNameController.text,
                                        lastNameController.text, emailController.text, phoneController.text));
                                    // TODO: Instead of jumping into scanner if registering, give the option for them to connect to a bot for their first tally.\
                                    (widget.registering) ?
                                    Navigator.push(
                                        context,
                                        new MaterialPageRoute(
                                            builder: (BuildContext context) =>
                                                Scanner()))
                                        : Navigator.pop(context);
                                    },
                                  child: Text((widget.registering) ? "Continue" : "Save Changes",
                                      style:
                                      TextStyle(fontSize: 16, fontWeight: FontWeight.bold)),
                                  color: Colors.white,
                                  textColor: Theme.of(context).primaryColor,
                                  elevation: 5,
                                  height: 50,
                                  minWidth: (MediaQuery.of(context).size.width) / 1.75,
                              )],
                          ),
                        ))
                  ],
                ))));
  }

  void createControllers () {
    Account userInfoAccount = userInfo.account;
    if (firstUpdate) {
      displayNameController = TextEditingController(
          text: (widget.registering) ? null : userInfoAccount.displayName);
      firstNameController = TextEditingController(
          text: (widget.registering) ? null : userInfoAccount.firstName);
      lastNameController = TextEditingController(
          text: (widget.registering) ? null : userInfoAccount.lastName);
      emailController = TextEditingController(
          text: (widget.registering) ? null : userInfoAccount.email);
      phoneController = TextEditingController(
          text: (widget.registering) ? null : userInfoAccount.phone);
    }
    firstUpdate = false;
  }
}
