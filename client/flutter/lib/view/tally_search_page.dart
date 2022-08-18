import 'package:flutter/material.dart';
import '../objects/singletons.dart';
import '../presenter/tally_search_presenter.dart';
import '../objects/tally.dart';
import 'main_drawer_view.dart';
import 'tally_page.dart';
import 'create_tally_page.dart';
import 'transaction_page.dart';

// ignore: must_be_immutable
class TallySearchPage extends StatefulWidget {
  final int searchResultType;
  const TallySearchPage(this.searchResultType);

  @override
  TallySearchPageState createState() => TallySearchPageState();
}

class TallySearchPageState extends State<TallySearchPage> {
  var userTallies = AppContext().user?.tallyList;
  var userTransactions = AppContext().user?.transactionList;
  final List searchList = <Tally>[];
  bool searching = false;
  var presenter = TallySearchPresenter();

  @override
  Widget build(BuildContext context) {
    userTallies ??= presenter.getUserTallies();
    return Scaffold(
      appBar: AppBar(
          title: TextField(
            onChanged: (input) {
              final ut = userTallies;
              if (input.isNotEmpty && ut != null) {
                searchList.clear();
                searchList.addAll(presenter.filterUsers(input, ut));
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
            decoration: const InputDecoration(
                icon: Icon(
                  Icons.search,
                  color: Colors.white,
                ),
                hintText: "type user here",
                hintStyle: TextStyle(
                    color: Colors.white, fontWeight: FontWeight.w500)),
            autofocus: !(widget.searchResultType == 0),
            style: TextStyle(color: Colors.white),
            cursorColor: Colors.white,
          ),
          automaticallyImplyLeading:
              widget.searchResultType == 1 ? false : true,
          leading: widget.searchResultType == 1
              ? BackButton(color: Colors.white)
              : null),
      body: SizedBox(
          height: MediaQuery.of(context).size.height,
          width: MediaQuery.of(context).size.width,
          child: Stack(children: [buildTallyList(), buildButton()])),
      drawer: MainDrawer(),
    );
  }

  Widget buildTallyList() {
    return ListView.builder(
        padding:
            const EdgeInsets.only(top: 16, right: 16, bottom: 75, left: 16),
        itemCount: searching
            ? (searchList.length * 2)
            : ((userTallies?.length ?? 0) * 2),
        itemBuilder: (context, item) {
          final ut = userTallies;
          if (item == 0 && searching)
            return buildRow(searchList[0]);
          else if (item == 0 && !searching)
            return Row(
                children: [if (ut != null && ut.isNotEmpty) buildRow(ut[0])]);

          if (item.isOdd) return Divider();

          if (searching)
            return buildRow(searchList[item ~/ 2]);
          else
            return Row(children: [
              if (ut != null && ut.isNotEmpty) buildRow(ut[item ~/ 2])
            ]);
        });
  }

  Widget buildRow(Tally t) {
    return ListTile(
        title: Text(t.friend?.displayName ?? "-",
            style: TextStyle(fontSize: 18, fontWeight: FontWeight.w500)),
        onTap: () {
          final friend = t.friend;
          if (widget.searchResultType == 0) {
            Navigator.push(
                context,
                MaterialPageRoute(
                    settings: RouteSettings(name: "tally-page"),
                    builder: (BuildContext context) => TallyPage(t)));
          } else if (widget.searchResultType == 1) {
            Navigator.push(
                context,
                MaterialPageRoute(
                    builder: (BuildContext context) => Row(children: [
                          if (friend != null) TransactionPage(friend, true)
                        ])));
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
                      MaterialPageRoute(
                          builder: (BuildContext context) =>
                              CreateTallyPage()));
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
