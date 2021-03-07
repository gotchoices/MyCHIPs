import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/tally_page_presenter.dart';
import '../objects/transaction.dart';
import '../objects/tally.dart';
import 'package:date_format/date_format.dart';
import 'main_drawer_view.dart';
import 'transaction_page.dart';

class TallyPage extends StatefulWidget {
  final Tally tally;
  TallyPage(this.tally, {Key key}): super(key: key);

  @override
  TallyPageState createState() => new TallyPageState();
}

class TallyPageState extends State<TallyPage> {
  UserTransactions userTransactions = UserTransactions();
  Map transactionMap;
  var presenter = TallyPagePresenter();

  @override
  Widget build(BuildContext context) {
    transactionMap = userTransactions.transactionList;
    return Scaffold(
        appBar: AppBar(
          title: Text("Tally with " + widget.tally.friend),
          actions: [
            //TODO: Where is the user profile image URL stored? How and when is it fetched?
            CircleAvatar(backgroundImage: new NetworkImage("https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),)
          ],),
        body: buildPage(),
        drawer: MainDrawer()
    );
  }

  Widget buildPage() {
    return Stack(
      children: [
        Column(children: [
          //buildBalance(), FOR NOW
          buildHistory(),
          buildButtons()
        ]),
      ]
    );
  }

  //May use this function later
  // Widget buildBalance() {
  //   return Container(
  //     height:150,
  //     child: Padding(
  //       padding: const EdgeInsets.all(15),
  //       child: Align(
  //         alignment: Alignment.topCenter,
  //         child: Column(
  //         children: [
  //           Text("₵" + widget.tally.balance.toString(),  style: TextStyle(fontSize: 75)),
  //           Text("balance",  style: TextStyle(fontSize: 25)),
  //         ],
  //   ))));
  // }

  Widget buildHistory() {
    return Expanded(child: buildHistoryList());
  }

  Widget buildHistoryList() {
    List<Transaction> transactionList = transactionMap[widget.tally.personID];
    if (transactionList.length == 0)
      return Center(child: Text("Click Pay or Request to begin a transaction history with this person", style: TextStyle(fontSize: 25, fontStyle:FontStyle.italic)));
    return ListView.builder(
        itemCount: (transactionList.length * 2),
        padding: const EdgeInsets.all(16),
        itemBuilder:(context, item) {
          if(item == 0) 
            return ListTile(title: Text("History:", style: TextStyle(fontSize: 25, decoration: TextDecoration.underline),));
          item--;
          if(item == 0)
            return buildRow(transactionList[0]);
          if(item.isOdd) return Divider();
          return buildRow(transactionList[item~/2]);
        }
    );
  }
  Widget buildRow(Transaction t) {
    return ListTile(
        title : Text(formatDate(t.date, [d, '-', M, '-', yy]), style: TextStyle(fontSize: 18)),
        trailing: Text("₵" + t.amount.toStringAsFixed(2), style: TextStyle(fontSize: 18)),
    );
  }

  Widget buildButtons() {
    var maxButtonWidth = (MediaQuery.of(context).size.width) / 2.25;
    return Container(
      child: Row(children: [
      Padding(
      padding: const EdgeInsets.all(10),
      child: Align(
        alignment: Alignment.bottomLeft,
        child: MaterialButton(
          onPressed: () {
            showDialog(context: context, builder: (BuildContext context){
              return AlertDialog(
                scrollable: true,
                content: buildTransactionWidget(context, 'PAY', widget.tally.friend));});
          },
          child: const Text('PAY', style: TextStyle(fontSize: 20)),
          color: Colors.blue,
          textColor: Colors.white,
          elevation: 5,
          height: 50,
          minWidth: maxButtonWidth
        ))),
      Padding(
        padding: const EdgeInsets.all(10),
        child: Align(
          alignment: Alignment.bottomRight,
          child: MaterialButton(
            onPressed: () {
              showDialog(context: context, builder: (BuildContext context){
                return AlertDialog(
                  scrollable: true,
                  content: buildTransactionWidget(context, 'REQUEST', widget.tally.friend));});
            },
            child: const Text('REQUEST', style: TextStyle(fontSize: 20)),
            color: Colors.blue,
            textColor: Colors.white,
            elevation: 5,
            height: 50,
            minWidth: maxButtonWidth
    )))]));
  }
}