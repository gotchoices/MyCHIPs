import 'package:flutter/material.dart';
import 'package:flutter_app/model/singletons.dart';
import 'package:flutter_app/presenter/tally_search_presenter.dart';
import 'home_page.dart';
import '../objects/tally.dart';
import 'tally_page.dart';
import 'create_tally_page.dart';
import 'transaction_page.dart';

class TallySearchPage extends StatefulWidget {
  int searchResultType;
  TallySearchPage(this.searchResultType);

  @override
  TallySearchPageState createState() => new TallySearchPageState();
}

class TallySearchPageState extends State<TallySearchPage> {
  UserTallies userTallies = UserTallies();
  List tallyList;
  final List searchList = <Tally>[];
  bool searching = false;
  var presenter = new TallySearchPresenter();

  @override
  Widget build(BuildContext context) {
    if (userTallies.tallyList.length == 0)
      userTallies.tallyList = presenter.getUserTallies();
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
            hintStyle: TextStyle(color: Colors.white)),
        autofocus: !(widget.searchResultType == 0),
        style: TextStyle(color: Colors.white),
        cursorColor: Colors.white,
      )
          // actions: <Widget>[
          //   searching
          //       ? IconButton(
          //           icon: Icon(Icons.cancel_outlined),
          //           onPressed: () {
          //             setState(() {
          //               searchList.clear();
          //               searching = !searching;
          //             });
          //           })
          //       : IconButton(
          //           icon: Icon(Icons.search),
          //           onPressed: () {
          //             setState(() {
          //               searching = !searching;
          //             });
          //           }),
          // ]
          ),
      body: Container(
          child: Stack(children: [
        Container(child: buildTallyList()),
        Container(child: widget.searchResultType == 0 ? buildButton() : null)
      ])),
      drawer: MainDrawer(),
    );
  }

  Widget buildTallyList() {
    return ListView.builder(
        padding: const EdgeInsets.all(16),
        itemCount: searching ? searchList.length : tallyList.length,
        itemBuilder: (context, item) {
          int index = item ~/ 2;
          if (item.isOdd) return Divider();
          if (index >= tallyList.length && !searching)
            //if we've reached the end of the list, query the presenter for more, providing the last tally in the list for reference
            userTallies.tallyList = tallyList;
          else if (searching && searchList.length > 0) {
            if (index >= searchList.length) {
              return SizedBox();
            }
            return buildRow(searchList[index]);
          }
          if (index >= tallyList.length) {
            return SizedBox();
          }
          return buildRow(tallyList[index]);
        });
  }

  Widget buildRow(Tally t) {
    return ListTile(
        title: Text(t.friend, style: TextStyle(fontSize: 18)),
        trailing:
            Text("₵" + t.balance.toString(), style: TextStyle(fontSize: 18)),
        onTap: () {
          if (widget.searchResultType == 0) {
            Navigator.push(
                context,
                new MaterialPageRoute(
                    builder: (BuildContext context) =>
                        new TallyPage(Tally(t.friend, t.balance))));
          } else if (widget.searchResultType == 1) {
            showDialog(
                context: context,
                builder: (BuildContext context) {
                  return AlertDialog(
                      scrollable: true,
                      content:
                          buildTransactionWidget(context, 'BOTH', t.friend));
                });
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
                child: const Text("Create a New Tally",
                    style: TextStyle(fontSize: 20)),
                color: Colors.blue,
                textColor: Colors.white,
                elevation: 5,
                height: 50,
                minWidth: maxButtonWidth)));
  }
}
