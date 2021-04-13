import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/tally_search_presenter.dart';
import 'package:flutter_app/objects/tally.dart';
import 'main_drawer_view.dart';
import 'tally_page.dart';
import 'create_tally_page.dart';
import 'transaction_page.dart';

// ignore: must_be_immutable
class TallySearchPage extends StatefulWidget {
  int searchResultType;
  TallySearchPage(this.searchResultType);

  @override
  TallySearchPageState createState() => new TallySearchPageState();
}

class TallySearchPageState extends State<TallySearchPage> {
  UserTallies userTallies = UserTallies();
  UserTransactions userTransactions = UserTransactions();
  List tallyList;
  final List searchList = <Tally>[];
  bool searching = false;
  var presenter = new TallySearchPresenter();

  @override
  Widget build(BuildContext context) {
    if (userTallies.tallyList.length == 0) presenter.getUserTallies();
    tallyList = userTallies.tallyList;
    return Scaffold(
      appBar: AppBar(
          title: TextField(
            onChanged: (input) {
              if (input.isNotEmpty) {
                searchList.clear();
                searchList.addAll(presenter.filterUsers(input, tallyList));
                setState(() {
                  searching = true;
                });
              } else {
                searchList.clear();
                setState(() {
                  searching = false;
                });
              }
              },
            decoration: InputDecoration(
                icon: Icon(
                  Icons.search,
                  color: Colors.white,
                ),
                hintText: "type user here",
                hintStyle: TextStyle(color: Colors.white, fontWeight: FontWeight.w500)),
            autofocus: !(widget.searchResultType == 0),
            style: TextStyle(color: Colors.white),
            cursorColor: Colors.white,
          )),
      body: Container(
          height: MediaQuery.of(context).size.height,
          width: MediaQuery.of(context).size.width,
          child: Column(
              children: [
                Expanded(flex: 7, child:Container(
                    height: MediaQuery.of(context).size.height * 0.8,
                    width: MediaQuery.of(context).size.width,
                    child: buildTallyList())),
                Expanded(flex: 1, child: Container(child: widget.searchResultType == 0 ? buildButton() : null))
              ])),
      drawer: MainDrawer(),
    );
  }

  Widget buildTallyList() {
    return ListView.builder(
        padding:
        const EdgeInsets.only(top: 16, right: 16, bottom: 75, left: 16),
        itemCount: searching ? (searchList.length * 2) : (tallyList.length * 2),
        itemBuilder: (context, item) {
          if (item == 0 && searching)
            return buildRow(searchList[0]);
          else if (item == 0 && !searching) return buildRow(tallyList[0]);

          if (item.isOdd) return Divider();

          if (searching)
            return buildRow(searchList[item ~/ 2]);
          else
            return buildRow(tallyList[item ~/ 2]);
        });
  }

  Widget buildRow(Tally t) {
    return ListTile(
        title: Text(t.friend.displayName, style: TextStyle(fontSize: 18, fontWeight: FontWeight.w500)),
        onTap: () {
          if (widget.searchResultType == 0) {
            Navigator.push(
                context,
                MaterialPageRoute(
                    settings: RouteSettings(name: "tally-page"),
                    builder: (BuildContext context) =>
                        TallyPage(Tally(t.friend, t.balance))));
          } else if (widget.searchResultType == 1) {
            Navigator.push(
                context,
                MaterialPageRoute(
                    builder: (BuildContext context) =>
                        TransactionPage(t.friend, true)));
          }
        });
  }

  Widget buildButton() {
    var maxButtonWidth = (MediaQuery.of(context).size.width) / 1.75;
    return Align(
        alignment: Alignment.bottomCenter,
        child: Padding(
            padding: const EdgeInsets.all(15),
            child: MaterialButton(
                onPressed: () {
                  Navigator.push(
                      context,
                      new MaterialPageRoute(
                          builder: (BuildContext context) =>
                              new CreateTallyPage()));
                },
                child: const Text("CREATE NEW TALLY",
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: maxButtonWidth)));
  }
}
