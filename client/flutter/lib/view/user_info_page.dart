import 'package:flutter/cupertino.dart';
import 'package:flutter/material.dart';
import '../managers/user/account.dart';
import '../objects/singletons.dart';
import '../presenter/user_info_presenter.dart';
import 'main_drawer_view.dart';
import 'scanner_page.dart';

class UserInfoPage extends StatefulWidget {
  final bool registering;
  const UserInfoPage(this.registering, {Key? key}) : super(key: key);
  @override
  UserInfoPageState createState() => UserInfoPageState();
}

class UserInfoPageState extends State<UserInfoPage> {
  late bool showContact;
  bool firstUpdate = true;
  var presenter = UserInfoPresenter();
  UserInfo userInfo = UserInfo();
  late TextEditingController displayNameController;
  late TextEditingController firstNameController;
  late TextEditingController lastNameController;
  late TextEditingController emailController;
  late TextEditingController phoneController;
  @override
  Widget build(BuildContext context) {
    showContact = UserInfo().showContact;
    return Scaffold(
      appBar: AppBar(title: const Text("User Information")),
      body: buildPage(),
      drawer: (widget.registering) ? null : const MainDrawer(),
    );
  }

  Widget buildPage() {
    createControllers();
    return (Container(
        alignment: Alignment.topCenter,
        child: Padding(
            padding: const EdgeInsets.all(16),
            child: ListView(
              children: [
                const Icon(
                  Icons.person,
                  size: 128,
                ),
                Padding(
                  padding: const EdgeInsets.only(top: 16),
                  child: Column(
                    children: [
                      TextField(
                          controller: displayNameController,
                          decoration: const InputDecoration(
                              hintText: "Display Name",
                              border: InputBorder.none,
                              hintStyle: TextStyle(color: Colors.grey))),
                      TextField(
                          controller: firstNameController,
                          decoration: const InputDecoration(
                              hintText: "First Name",
                              border: InputBorder.none,
                              hintStyle: TextStyle(color: Colors.grey))),
                      TextField(
                          controller: lastNameController,
                          decoration: const InputDecoration(
                              hintText: "Last Name",
                              border: InputBorder.none,
                              hintStyle: TextStyle(color: Colors.grey))),
                      TextField(
                          controller: emailController,
                          decoration: const InputDecoration(
                              hintText: "Email",
                              border: InputBorder.none,
                              hintStyle: TextStyle(color: Colors.grey))),
                      TextField(
                          controller: phoneController,
                          decoration: const InputDecoration(
                              hintText: "Phone",
                              border: InputBorder.none,
                              hintStyle: TextStyle(color: Colors.grey))),
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
                            activeColor: const Color(0xfff3a43e),
                          ),
                          const Text("Display Contact Info Publicly?  "),
                          Text(showContact ? "Yes" : "No")
                        ],
                      ),
                      MaterialButton(
                        onPressed: () {
                          presenter.setAccountData(Account(
                              displayNameController.text,
                              firstNameController.text,
                              lastNameController.text,
                              phone: phoneController.text,
                              email: emailController.text));
                          // TODO: Instead of jumping into scanner if registering, give the option for them to connect to a bot for their first tally.\
                          (widget.registering)
                              ? Navigator.push(
                                  context,
                                  MaterialPageRoute(
                                      builder: (BuildContext context) =>
                                          const Scanner()))
                              : Navigator.pop(context);
                        },
                        child: Text(
                            (widget.registering) ? "Continue" : "Save Changes",
                            style: const TextStyle(
                                fontSize: 16, fontWeight: FontWeight.bold)),
                        color: Colors.white,
                        textColor: Theme.of(context).primaryColor,
                        elevation: 5,
                        height: 50,
                        minWidth: (MediaQuery.of(context).size.width) / 1.75,
                      )
                    ],
                  ),
                )
              ],
            ))));
  }

  void createControllers() {
    final userInfoAccount = userInfo.account;
    if (firstUpdate && userInfoAccount != null) {
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
