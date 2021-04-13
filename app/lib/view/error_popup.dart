import 'package:flutter/material.dart';

const errorImageDir = "assets/access_denied.png";

Widget buildErrorWidget(context, [errMsg = "Try again later."]) {
  return ListBody(
    children:[
      Text("Something went wrong!"),
      Image.asset(errorImageDir),
      //TODO: Add specificity to this text. What went wrong? Was there no corresponding tally? Server error? Internet connection? Not enough funds?
      Text(errMsg),
    ]
  );
}

void errPop(context, [errMsg = "Try again later."]) {
  showDialog(context: context, builder: (BuildContext context){
    return AlertDialog(
        scrollable: false,
        content: SingleChildScrollView(
            child: ListBody(
                children:[
                  Text("Something went wrong!"),
                  Image.asset(errorImageDir),
                  //TODO: Add specificity to this text. What went wrong? Was there no corresponding tally? Server error? Internet connection? Not enough funds?
                  Text(errMsg),
                ]
            )
        ),
        actions: <Widget>[
          TextButton(
            child: Text('okay'),
            onPressed: () {
            Navigator.of(context).pop();
          })]
    );
  });
}