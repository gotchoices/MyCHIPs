import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/scanner_presenter.dart';
import 'package:flutter_app/view/error_popup.dart';
import '../objects/tally.dart';
import '../objects/tally_ticket.dart';
import 'package:qr_code_scanner/qr_code_scanner.dart';
import 'tally_page.dart';
import 'dart:convert';

const flashOn = 'FLASH ON';
const flashOff = 'FLASH OFF';
const frontCamera = 'FRONT CAMERA';
const backCamera = 'BACK CAMERA';

class Scanner extends StatefulWidget {
  const Scanner({Key key,}) : super(key: key);

  @override
  State<StatefulWidget> createState() => ScannerState();
}

class ScannerState extends State<Scanner> {
  var qrText = '';
  var flashState = flashOn;
  var cameraState = frontCamera;
  QRViewController controller;
  final GlobalKey qrKey = GlobalKey(debugLabel: 'QR');
  var presenter = new ScannerPresenter();

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      body: Column(
        children: <Widget>[
          Expanded(
            flex: 4,
            child: QRView(
              key: qrKey,
              onQRViewCreated: _onQRViewCreated,
              overlay: QrScannerOverlayShape(
                borderColor: Colors.red,
                borderRadius: 10,
                borderLength: 30,
                borderWidth: 10,
                cutOutSize: 300,
              ),
            ),
          ),
          Expanded(
            flex: 1,
            child: FittedBox(
              fit: BoxFit.contain,
              child: Column(
                mainAxisAlignment: MainAxisAlignment.spaceEvenly,
                children: <Widget>[
                  Row(
                    mainAxisAlignment: MainAxisAlignment.center,
                    crossAxisAlignment: CrossAxisAlignment.center,
                    children: <Widget>[
                      Container(
                        margin: EdgeInsets.all(8),
                        // ignore: deprecated_member_use
                        child: MaterialButton(
                            onPressed: () {
                              if (controller != null) {
                                controller.toggleFlash();
                                if (_isFlashOn(flashState)) {
                                  setState(() {
                                    flashState = flashOff;
                                  });
                                } else {
                                  setState(() {
                                    flashState = flashOn;
                                  });
                                }
                              }
                            },
                            child: Text(flashState,
                                style:
                                TextStyle(fontSize: 16, fontWeight: FontWeight.bold)),
                            color: Colors.white,
                            textColor: Theme.of(context).primaryColor,
                            elevation: 5,
                            height: 50,
                            minWidth: (MediaQuery.of(context).size.width) / 2.5,
                        ),
                      ),
                      Container(
                        margin: EdgeInsets.all(8),
                        // ignore: deprecated_member_use
                        child: MaterialButton(
                          onPressed: () {
                            if (controller != null) {
                              controller.flipCamera();
                              if (_isBackCamera(cameraState)) {
                                setState(() {
                                  cameraState = frontCamera;
                                });
                              } else {
                                setState(() {
                                  cameraState = backCamera;
                                });
                              }
                            }
                          },
                          child: Text(cameraState,
                              style:
                              TextStyle(fontSize: 16, fontWeight: FontWeight.bold)),
                          color: Colors.white,
                          textColor: Theme.of(context).primaryColor,
                          elevation: 5,
                          height: 50,
                          minWidth: (MediaQuery.of(context).size.width) / 2.5,
                        ),
                      )
                    ],
                  ),
                ],
              ),
            ),
          )
        ],
      ),
    );
  }

  bool _isFlashOn(String current) {
    return flashOn == current;
  }

  bool _isBackCamera(String current) {
    return backCamera == current;
  }

  void _onQRViewCreated(QRViewController controller) {
    this.controller = controller;
    controller.scannedDataStream.listen((scanData) {
      setState(() {
        print("scanned " + scanData);
        controller.pauseCamera();
        //pop this context so pushing the back button won't bring us back to the camera
        showDialog(
          context: context,
          barrierDismissible: false,
          builder: (BuildContext context) {
            return getTallyApprovalDialog(scanData);},);
      });
    });
  }

  Widget getTallyApprovalDialog(scanData) {
    TallyTicket ticket = TallyTicket.fromJson(jsonDecode(scanData));
    Tally tally = Tally.parseTallyTicket(ticket);
    //TODO: Check which version of the build this is so we can return a "CupertinoAlertDialog" if on iOS
    return AlertDialog(
      title: Text('Start a New Tally'),
      content: SingleChildScrollView(
        child: ListBody(
          children: <Widget>[
            Text('Would you like to start a tally with ' + tally.friend.displayName + "?"),
          ],
        ),
      ),
      actions: <Widget>[
        TextButton(
          child: Text('Cancel'),
          onPressed: () {
            Navigator.of(context).pop();
            controller.resumeCamera();
          }),
        TextButton(
          child: Text('Confirm'),
          onPressed: () {
            Navigator.of(context).pop();
            Navigator.pop(context);
            if (presenter.registerNewTally(ticket)) {
              UserTallies userTallies = UserTallies();
              userTallies.tallyList.add(tally);
              userTallies.tallyList.add(tally);
              UserTransactions().transactionList[tally.personID] = [];
              //TODO: Comment this out when succPop works
              // succPop(context, "Tally with " + tally.friend + " successfully established.");
              transitionToNewTally(tally);
            }
            else
              errPop(context, "Couldn't create a tally because [INSERT REASON HERE]");
          }),
      ],
    );
  }

  void transitionToNewTally(tally) {
    Navigator.push(context, new MaterialPageRoute(
        builder: (BuildContext context) => new TallyPage(tally)));
  }

  @override
  void dispose() {
    controller.dispose();
    super.dispose();
  }
}
