import 'package:flutter/material.dart';
import 'package:animated_check/animated_check.dart';
//TODO: FIX ANIMATED CHECKMARK PLEASE

/**
 * @param msg = message appearing at the bottom of the success notification
 */
Widget buildSuccessWidget(context, [msg = "congrats!"]) {
  var animeController = AnimationController(vsync: context, duration: Duration(seconds: 1));
  Animation animation = new Tween<double>(begin: 0, end: 1)
      .animate(new CurvedAnimation(
      parent: animeController,
      curve: Curves.easeInOutCirc)
  );
  return Column(
    children: [
      AnimatedCheck(
        progress: animation,
        size: 200,
      ),
      Text(msg),
      MaterialButton(
        onPressed: (){Navigator.pop(context);},
        child: Text('okay',
            style: TextStyle(fontSize: 20)),
        color: Colors.blue,
        textColor: Colors.white,
        elevation: 5,
      )
    ],

  );

}