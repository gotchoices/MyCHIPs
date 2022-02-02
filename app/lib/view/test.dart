// Dart client that implements the wysemanClient.dart module.

// steps to run:
// 1. generate token and paste into test.dart code (this will be done automatically via a QR code later
// 2. ensure that the key vault is empty (the code will check for a key to determine whether to connect via token or key)
// 3. click the "connect to server" link in the flutter UI and check the server logs for connection status (test/local/docker/mychips0.log/combined.log)

import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_svg/flutter_svg.dart';
import 'package:pie_chart/pie_chart.dart';
import 'main_drawer_view.dart';
import 'tally_search_page.dart';
import 'scanner_page.dart';
import '../presenter/home_presenter.dart';
import '../wyseman/wysemanClient.dart';
import 'dart:io';
import 'package:path_provider/path_provider.dart';
import 'package:convert/convert.dart';
import 'dart:convert';
import 'package:web_socket_channel/io.dart';

class MyChipsTest extends StatelessWidget {
  final dbInfo = ['mychips_user', 'wylib'];
  final httpPort = 8000;
  final presenter = new HomePresenter();
  var connectArray;

  @override
  Widget build(BuildContext context) {
    var myCredential = WysemanCredential();
    myCredential.host = 'mychips0';
    myCredential.wsPort = 54320;
    myCredential.token =
        '1abebac9aac0fa394a1720fcd0cfd72b'; //manually pasting in new ticket for now.
    myCredential.key = null;
    myCredential.keyLength = null;
    myCredential.user = 'admin';

    void connect() async {
      print(httpPort);
      var myClient = new Client(dbInfo, httpPort, null);
      final directory = await getApplicationDocumentsDirectory();
      //check if vault has a key
      File myKeyObj = new File((directory.path + '/key.txt'));
      bool keyExists = await myKeyObj.exists();
      if (keyExists) {
        String _returnLoginObject = await myKeyObj.readAsString();
        Map<String, dynamic> loginObj = jsonDecode(_returnLoginObject);
        //Pass login object values to connect method
        myCredential.host = loginObj['login']['host'];
        myCredential.user = loginObj['login']['user'];
        myCredential.wsPort = int.parse(loginObj['login']['port']);
        myCredential.key = loginObj['login']['privateKey'];
        myCredential.token = null;
        //connectArray = await myClient.connect(myCredential, null); //connect with key
        //print(connectArray);
        myClient.connect(myCredential, null);
      } else if (myCredential.token != '') {
        print("key doesn't exist");
        //print(connectArray);
        //connectArray = await myClient.connect(myCredential, null); //connect with token
        myClient.connect(myCredential, null);
      } else {
        print("You need a key or token to connect");
      }
      final channel = IOWebSocketChannel.connect(Uri.parse(connectArray[0]),
          headers: connectArray[1]);
    }

    return MaterialApp(
      home: Column(
        children: [
          TextButton(onPressed: connect, child: Text('Connect to Server'))
          // const SizedBox(height: 24),
          // StreamBuilder(
          //     stream: channel.stream,
          //     builder: (context, snapshot) {
          //       return Text(snapshot.hasData ? '${snapshot.data}' : '');
          //    })
        ],
      ),
    );
  }
}
