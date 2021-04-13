import 'package:flutter/cupertino.dart';
import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/tally_page_presenter.dart';
import '../objects/transaction.dart';
import '../objects/tally.dart';
import 'package:date_format/date_format.dart';
import 'main_drawer_view.dart';
import 'transaction_page.dart';
import 'dart:math';

class TallyPage extends StatefulWidget {
  final Tally tally;
  TallyPage(this.tally, {Key key}) : super(key: key);

  @override
  TallyPageState createState() => new TallyPageState();
}

class TallyPageState extends State<TallyPage> {
  UserTransactions userTransactions = UserTransactions();
  Map transactionMap;
  var presenter = TallyPagePresenter();
  var rng = new Random();

  @override
  Widget build(BuildContext context) {
    transactionMap = userTransactions.transactionList;

    return Scaffold(
        appBar: AppBar(
          // title: Text("Tally with " + widget.tally.friend.displayName),
          title: Text("Tally History"),
        ),
        body: buildPage(),
        drawer: MainDrawer());
  }

  Widget buildPage() {
    return Stack(children: [
      Column(children: [
        buildUserHeader(),
        Padding(
          padding: const EdgeInsets.only(top: 16, right: 32, bottom:8, left: 32),
          child: Align(
            alignment: Alignment.centerLeft,
            child: Text("Tally History",
                    style:
                    TextStyle(fontSize: 15, fontWeight: FontWeight.w700),
                  )
          ),
        ),
        Divider(),
        buildHistory()
      ]),
    ]);
  }

  Widget buildUserHeader() {
      return Container(
        color: Color(0xff171825),
        child: Padding(
          padding: const EdgeInsets.only(top: 26, bottom: 16),
          child: Align(
            alignment: Alignment.topCenter,
            child: Column(
            children: [
              CircleAvatar(
                child: new Text(widget.tally.friend.displayName.substring(0, 1), style: TextStyle(fontSize: 20, fontWeight: FontWeight.w700, color: Color(0xffffffff))),
              backgroundColor: Color(0xfff3a43e),),
              Padding(
                padding: const EdgeInsets.only(top: 6, bottom: 16),
                child: Text(widget.tally.friend.displayName,  style: TextStyle(fontSize: 35, color: Color(0xffffffff)))),
              Padding(
                padding: const EdgeInsets.only(top: 5),
                child: Text("Tally Balance:",  style: TextStyle(fontSize: 15, color: Color(0xffffffff), fontWeight: FontWeight.w600)),
              ),
              Padding(
                padding: const EdgeInsets.only(top: 2, bottom: 10),
                child: (widget.tally.balance > 0) ?
                  Text("₵" + widget.tally.balance.toString(), style: TextStyle(fontSize: 30, color: Color(0xff53AB77), fontWeight: FontWeight.w500)) :
                  Text(widget.tally.balance.toString().substring(0,1) + "₵" + widget.tally.balance.toString().substring(1), style: TextStyle(fontSize: 30, color: Color(0xffD54040), fontWeight: FontWeight.w500)),
              ),
              buildButtons()
            ],
      ))));
  }

  Widget buildHistory() {
    return Expanded(child: buildHistoryList());
  }

  Widget buildHistoryList() {
    List<Transaction> transactionList = transactionMap[widget.tally.personID];
    transactionList.sort();
    if (transactionList.length == 0)
      return Center(
          child: Text(
              "Click Pay or Request to begin a transaction history with this person",
              style: TextStyle(fontSize: 25, fontStyle: FontStyle.italic)));
    return ListView.builder(
        itemCount: (transactionList.length * 2),
        padding: const EdgeInsets.only(left: 16, right: 16),
        itemBuilder: (context, item) {
          if (item.isOdd) return Divider();
          return buildRow(transactionList[item ~/ 2]);
        });
  }

  Widget buildRow(Transaction t) {
    return ListTile(
      title: (t.amount < 0) ? Text("You paid " + widget.tally.friend.displayName, style: TextStyle(fontWeight: FontWeight.w600)) : Text(widget.tally.friend.displayName + " paid You", style: TextStyle(fontWeight: FontWeight.w600)),
      subtitle: Text(formatDate(t.date, [M, ' ', d, ", ", yyyy]),
          style: TextStyle(fontSize: 14, fontWeight: FontWeight.w600)),
      trailing: (t.amount > 0) ?
        Text("₵" + t.amount.toStringAsFixed(2), style: TextStyle(fontSize: 20, color: Color(0xff53AB77), fontWeight: FontWeight.w600)) :
        Text(t.amount.toStringAsFixed(2).substring(0, 1) + "₵" + t.amount.toStringAsFixed(2).substring(1), style: TextStyle(fontSize: 20, color: Color(0xffD54040), fontWeight: FontWeight.w600)),

    );

  //  t.amount.toStringAsFixed(2),
  }

  Widget buildButtons() {
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
                              TransactionPage(widget.tally.friend, false)));
                },
                child: const Text("PAY/REQUEST",
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: maxButtonWidth)));
  }
}
