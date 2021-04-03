import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/tally.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'package:flutter_app/presenter/tally_search_presenter.dart';
import 'package:flutter_app/presenter/transaction_presenter.dart';
import 'error_popup.dart';
import 'main_drawer_view.dart';
import 'success_popup.dart';
import 'package:keyboard_actions/keyboard_actions.dart';

const BOTH = 'BOTH';
const PAY = 'PAY';
const REQUEST = 'REQUEST';

class TransactionPage extends StatefulWidget {
  final bool fromHome;
  final Account transactionPartner;
  TransactionPage(this.fromHome, this.transactionPartner, {Key key})
      : super(key: key);

  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> {
  TextEditingController amtController = TextEditingController();
  TextEditingController msgController = TextEditingController();
  final FocusNode amtNode = FocusNode();
  final FocusNode msgNode = FocusNode();
  Transaction curTransaction;

  @override
  void dispose() {
    amtController.dispose();
    msgController.dispose();
    super.dispose();
  }

  KeyboardActionsConfig buildConfig(BuildContext context) {
    return KeyboardActionsConfig(
        keyboardActionsPlatform: KeyboardActionsPlatform.ALL,
        keyboardBarColor: Colors.grey[200],
        nextFocus: true,
        actions: [
          KeyboardActionsItem(
            focusNode: amtNode,
          ),
          KeyboardActionsItem(
            focusNode: msgNode,
            onTapAction: () {
              showDialog(
                  context: context,
                  builder: (context) {
                    return AlertDialog(
                      content: Text("Custom Action"),
                      actions: <Widget>[
                        FlatButton(
                          child: Text("OK"),
                          onPressed: () => Navigator.of(context).pop(),
                        )
                      ],
                    );
                  });
            },
          )
        ]);
  }

  @override
  Widget build(BuildContext context) {
    return
        // KeyboardActions(
        // config: buildConfig(context),
        // child:
        Scaffold(
            appBar: AppBar(
                title: Text("Payment Details"),
                automaticallyImplyLeading: false,
                leading: Builder(
                    builder: (BuildContext context) => IconButton(
                          icon: const Icon(Icons.clear_rounded),
                          onPressed: () => Navigator.popUntil(
                              context,
                              widget.fromHome
                                  ? ModalRoute.withName("home-page")
                                  : ModalRoute.withName("tally-page")),
                        ))),
            body: buildPage(),
            drawer: MainDrawer())
        // )
        ;
  }

  Widget buildPage() {
    return Stack(children: [
      Column(children: [
        Padding(
            padding: EdgeInsets.fromLTRB(20, 15, 6, 8),
            child: Row(children: [
              buildAccountTitle() //currently the name is on a separate line from the payment textfield, but thanks to the row this can easily change
            ])),
        Divider(
          thickness: 2,
          indent: 20,
          endIndent: 20,
        ),
        Padding(
            padding: EdgeInsets.fromLTRB(20, 8, 6, 8),
            child: Row(children: [
              Expanded(flex: 0, child: Text("₵")),
              Expanded(
                  child: TextField(
                      controller: amtController,
                      focusNode: amtNode,
                      onSubmitted: (String amt) =>
                          curTransaction.amount = double.parse(amt),
                      decoration: InputDecoration(
                          border: InputBorder.none,
                          hintText: "0.00",
                          hintStyle: TextStyle(color: Colors.grey)),
                      style: TextStyle(color: Colors.black),
                      keyboardType: TextInputType.number))
            ])),
        Divider(
          thickness: 2,
          indent: 20,
          endIndent: 20,
        ),
        Padding(
            padding: EdgeInsets.fromLTRB(20, 0, 0, 0),
            child: TextField(
                keyboardType: TextInputType.multiline,
                maxLines: null,
                controller: msgController,
                focusNode: msgNode,
                onSubmitted: (String msg) => curTransaction.message = msg,
                decoration: InputDecoration(
                    border: InputBorder.none,
                    hintText: "Please enter a payment message",
                    hintStyle: TextStyle(color: Colors.grey, fontSize: 18)),
                style: TextStyle(fontSize: 18))),
      ]),
      Positioned(
        bottom: 10,
        width: (MediaQuery.of(context).size.width),
        child: createButtons(context),
      ),
    ]);
  }

  Widget buildAccountTitle() {
    return Container(
        decoration: BoxDecoration(
            borderRadius: BorderRadius.circular(40), color: Colors.white),
        child: Row(children: [
          CircleAvatar(
              backgroundImage: new NetworkImage(
                  "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png")),
          Padding(
              padding: EdgeInsets.all(8.0),
              child: Text(
                widget.transactionPartner.displayName,
                style: TextStyle(fontWeight: FontWeight.bold),
              ))
        ]));
  }

  Widget createButtons(context) {
    var presenter = TransactionPresenter();
    //TODO: Verify valid input before allowing button logic to be executed.
    //TODO: tie input to a transaction object to send through the presenter
    return Container(
        child: Padding(
            padding: EdgeInsets.all(10),
            child: Row(mainAxisAlignment: MainAxisAlignment.center, children: [
              MaterialButton(
                onPressed: () {
                  //TODO:
                  if (presenter.requestPayment(null)) {
                    Navigator.pop(context);
                    succPop(context, "Payment sent successfully");
                  } else {
                    errPop(context, "Payment failed. Try again?");
                  }
                },
                child: Text('REQUEST',
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: (MediaQuery.of(context).size.width) / 2.5,
              ),
              Padding(
                padding: EdgeInsets.all(10),
              ),
              MaterialButton(
                onPressed: () {
                  //TODO:
                  if (presenter.sendPayment(null)) {
                    //successful transaction
                    Navigator.pop(context);
                    succPop(context, 'great work mate. request sent');
                  } else {
                    //something went wrong...
                    errPop(context, 'request failed.');
                  }
                },
                child: Text('PAY',
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: (MediaQuery.of(context).size.width) / 2.5,
              ),
            ])));
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
    //createButtons(context)
  ]);
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
