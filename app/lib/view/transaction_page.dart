import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_svg/flutter_svg.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'package:flutter_app/presenter/transaction_presenter.dart';
import 'error_popup.dart';
import 'main_drawer_view.dart';
import 'package:animated_check/animated_check.dart';

const BOTH = 'BOTH';
const PAY = 'PAY';
const REQUEST = 'REQUEST';

class TransactionPage extends StatefulWidget {
  final Account transactionPartner;
  final bool fromHome;
  final String chipSVG = 'assets/chip.svg';
  TransactionPage(this.transactionPartner, this.fromHome, {Key key})
      : super(key: key);

  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> with SingleTickerProviderStateMixin {
  TextEditingController amtController = TextEditingController();
  TextEditingController msgController = TextEditingController();
  Transaction curTransaction;
  AnimationController _animationController;
  Animation<double> _animation;
  TransactionPresenter presenter = TransactionPresenter();

  @override
  void initState() {
    super.initState();

    _animationController = AnimationController(vsync: this, duration: Duration(seconds: 1));
    _animation = new Tween<double>(begin: 0, end: 1.5).animate(new CurvedAnimation(parent: _animationController, curve: Curves.easeInOutCirc));
  }

  @override
  void dispose() {
    amtController.dispose();
    msgController.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
            appBar: AppBar(
                title: Text("Payment Details"),
                automaticallyImplyLeading: false,
                leading: Builder(
                    builder: (BuildContext context) => IconButton(
                          icon: const Icon(Icons.clear_rounded),
                          onPressed: () => Navigator.popUntil(context,
                              widget.fromHome
                                  ? ModalRoute.withName("home-page")
                                  : ModalRoute.withName("tally-page")),
                        ))),
            body: buildPage(),
            drawer: MainDrawer());
  }

  Widget buildPage() {
    return Stack(children: [
      Column(children: [
        Padding(
            padding: EdgeInsets.fromLTRB(20, 15, 6, 8),
            child: Row(children: [
              buildAccountTitle()
            ])),
        Divider(
          thickness: 2,
          indent: 20,
          endIndent: 20,
        ),
        Padding(
            padding: EdgeInsets.fromLTRB(20, 8, 6, 8),
            child: Row(children: [
              Expanded(flex: 0, child: SvgPicture.asset(widget.chipSVG, height: 16,)),
              Expanded(
                  child: TextField(
                      controller: amtController,
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
                decoration: InputDecoration(
                    border: InputBorder.none,
                    hintText: "Please enter a payment message",
                    hintStyle: TextStyle(color: Colors.grey, fontSize: 18)),
                style: TextStyle(fontSize: 18))),
        AnimatedCheck(
          progress: _animation,
          size: 200,)
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
            child: new Text(widget.transactionPartner.displayName.substring(0, 1), style: TextStyle(fontSize: 16, fontWeight: FontWeight.w700, color: Color(0xffffffff))),
            backgroundColor: Color(0xfff3a43e)),
          Padding(
              padding: EdgeInsets.only(top: 8, right: 24, bottom: 8, left: 16),
              child: Text(
                widget.transactionPartner.displayName,
                style: TextStyle(fontWeight: FontWeight.bold, fontSize: 14),
              ))
        ]));
  }
  void runCheckAnim() async{
    _animationController.forward();
    await Future.delayed(const Duration(seconds: 2), (){});
    _animationController.reverse();
    await Future.delayed(const Duration(seconds: 1), (){});
    Navigator.popUntil(context,
        widget.fromHome
            ? ModalRoute.withName("home-page")
            : ModalRoute.withName("tally-page"));
  }

  Widget createButtons(context) {
    return Container(
        child: Padding(
            padding: EdgeInsets.all(10),
            child: Row(mainAxisAlignment: MainAxisAlignment.center, children: [
              MaterialButton(
                onPressed: () {
                  unfocusFields();
                  Transaction t = Transaction(DateTime.now(), msgController.text, widget.transactionPartner.displayName, "curUser", amtController.text);
                  print(t.toString());
                  if (checkParameterFormat(t)) {
                    showDialog(context: context, barrierDismissible: false,
                      builder: (BuildContext context) => confirmPayRequestDialog(false, double.parse(t.amount), t));
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
                  unfocusFields();
                  Transaction t = Transaction(DateTime.now(), msgController.text, "curUser", widget.transactionPartner.displayName, amtController.text);
                  if (checkParameterFormat(t)) {
                    showDialog(context: context, barrierDismissible: false,
                        builder: (BuildContext context) => confirmPayRequestDialog(true, double.parse(t.amount), t));
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

  bool checkParameterFormat(Transaction t) {
    if (t.receiver == null || t.receiver == "") {
      errPop(context, 'Please specify a recipient.');
      return false;
    }
    else if (t.receiver == null || t.receiver == "") {
      errPop(context, 'Something went wrong specifying your user identity.');
      return false;
    }
    else if (t.message == null || t.message == "") {
      errPop(context, 'Please specify the type of transaction in the message field.');
      return false;
    } else if ((t.amount = convertDynamic(t.amount)) == null) {
      errPop(context, 'Please enter a valid amount.');
      return false;
    }

    return true;
  }

  void unfocusFields() {
    FocusScope.of(context).unfocus();
    SystemChannels.textInput.invokeMethod('TextInput.hide');
  }

  void clearFields() {
    amtController.clear();
    msgController.clear();
  }

  String convertDynamic(dynamic number) {
    try {
      return double.parse(number).toStringAsFixed(2);
    } catch (FormatException) {
      return null;
    }
  }

  Widget confirmPayRequestDialog(bool payment, double amt, Transaction t) {
    //if payment, it's a payment. else, it's a request
    String sendOrRequest = payment ? "send $amt to " + widget.transactionPartner.displayName : "request $amt from " + widget.transactionPartner.displayName;
    return AlertDialog(
      title: Text(payment ? "Paying " + widget.transactionPartner.displayName : "Requesting from " + widget.transactionPartner.displayName),
      content: SingleChildScrollView(
        child: ListBody(
          children: <Widget>[
            Image.asset("assets/thinking.png"),
            Text("Are you sure you want to $sendOrRequest?"),
          ],
        ),
      ),
      actions: <Widget>[
        TextButton(
            child: Text('Cancel'),
            onPressed: () {
              Navigator.of(context).pop();
              unfocusFields();
            }),
        TextButton(
            child: Text('Confirm'),
            onPressed: () {
              Navigator.of(context).pop();
              bool result;
              unfocusFields();
              if(payment) result = presenter.sendPayment(t);
              else result = presenter.requestPayment(t);
              if (result) {
                clearFields();
                unfocusFields();
                runCheckAnim();
              } else {
                errPop(context, "Transaction failed, please try again.");
              }
            }),
      ],
    );
  }
}
