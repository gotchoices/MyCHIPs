import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/presenter/tally_search_presenter.dart';
import 'package:flutter_app/presenter/transaction_presenter.dart';
import 'error_popup.dart';
import 'main_drawer_view.dart';
import 'success_popup.dart';

const BOTH = 'BOTH';
const PAY = 'PAY';
const REQUEST = 'REQUEST';

class TransactionPage extends StatefulWidget {
  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
        appBar: AppBar(
          title: Text("MyCHIPs Transaction"),
        ),
        body: buildTransactionWidget(context, BOTH),
        drawer: MainDrawer());
  }
}

/* TODO: This widget needs a major rework. It's ugly. It's so ugly.
  and when it brings up the keyboard it destroys the formatting of everything behind it.
  It needs an "X" button, or some easy way for users to get off of this popup if they hit it by accident
  Additionally, if they're on the main page, we need to put a function that searches through all the tallies they
  have and auto fills/suggests the names of people they might be attempting to reach.
  The boxes are all wrong. And after the error message pops up, it still is focused on wherever you typed last. dumb.
  Also, there has to be a better way to make the widget in its 3 different forms than the "BOTH" if statement.
* */
Widget buildTransactionWidget(context, transactionType, [friend]) {
  return Column(children: [
    createPaymentTextFields(friend),
    Divider(thickness: 2, color: Colors.black),
    Container(
        child: Padding(
      padding: EdgeInsets.only(bottom: 100, left: 5),
      //TODO: Make the text in this textField wrap
          child: TextField(
        decoration: InputDecoration(
            border: InputBorder.none,
            hintText: "Purpose:",
            hintStyle: TextStyle(color: Colors.grey)),
        style: TextStyle(color: Colors.black),
      ),
    )),
    createButtons(context, transactionType)
  ]);
}

Widget createButtons(context, transactionType) {
  var presenter = TransactionPresenter();
  //TODO: Verify valid input before allowing button logic to be executed.
  //TODO: tie input to a transaction object to send through the presenter
  if (transactionType == BOTH) {
    return Container(
        child: Padding(
            padding: EdgeInsets.all(10),
            child: Row(children: [
              Expanded(
                  child: MaterialButton(
                      onPressed: () {
                        //TODO:
                        if (presenter.sendPayment(null)) {
                          Navigator.pop(context);
                          succPop(context, "Payment sent successfully");
                        } else {
                          errPop(context, "Payment failed. Try again?");
                        }
                      },
                      child: Text('PAY', style: TextStyle(fontSize: 20)),
                      color: Colors.blue,
                      textColor: Colors.white,
                      elevation: 5,
                      height: 50,
                      minWidth: (MediaQuery.of(context).size.width) / 2.25)),
              MaterialButton(
                  onPressed: () {
                    //TODO:
                    if (presenter.requestPayment(null)) {
                      //successful transaction
                      Navigator.pop(context);
                      succPop(context, 'great work mate. request sent');
                    } else {
                      //something went wrong...
                      errPop(context, 'request failed.');
                    }
                  },
                  child: Text('REQUEST', style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width) / 2.25)
            ])));
  }
  return Container(
      child: Padding(
          padding: EdgeInsets.all(10),
          child: Row(children: [
            Expanded(
                flex: 1,
                child: MaterialButton(
                  onPressed: () {
                    //TODO:
                    if (transactionType == PAY) {
                      if (presenter.sendPayment(null)) {
                        Navigator.pop(context);
                        succPop(context, 'Payment sent successfully.');
                      } else {
                        errPop(context, 'payment failed. try again?');
                      }
                    } else if (transactionType == REQUEST) {
                      if (presenter.requestPayment(null)) {
                        Navigator.pop(context);
                        succPop(context, 'Request sent successfully.');
                      } else {
                        errPop(context,
                            'Failed to send request. Maybe try again?');
                      }
                    } else {
                      // the transaction type was neither pay or request, what is going on
                      //this is a
                      print("BIG BOY ERROR");
                    }
                    print("pressed " + transactionType);
                  },
                  child: Text(transactionType, style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  // height:50
                ))
          ])));
}

Widget createPaymentTextFields(friend) {
  final List searchList = <Tally>[];
  TallySearchPresenter presenter = TallySearchPresenter();
  searchList.addAll(presenter.getUserTallies());
  return Container(
      child: Padding(
          padding: EdgeInsets.only(left: 5),
          child: Row(mainAxisSize: MainAxisSize.min, children: [
            Expanded(
                flex: 2,
                child: friend != null
                    ? Text(friend)
                    : TextField(
                        onChanged: (input) {
                          searchList.clear();
                          searchList
                              .addAll(presenter.filterUsers(input, searchList));
                        },
                        decoration: InputDecoration(
                            border: InputBorder.none,
                            hintText: "To Whom:",
                            hintStyle: TextStyle(color: Colors.grey)),
                        style: TextStyle(color: Colors.black))),
            Expanded(flex: 0, child: Text("\$")),
            Expanded(
                child: TextField(
                    decoration: InputDecoration(
                        border: InputBorder.none,
                        hintText: "0",
                        hintStyle: TextStyle(color: Colors.grey)),
                    style: TextStyle(color: Colors.black),
                    keyboardType: TextInputType.number,
                    inputFormatters: [FilteringTextInputFormatter.digitsOnly]))
          ])));
}
