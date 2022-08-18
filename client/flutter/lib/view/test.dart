import 'dart:convert';

import 'package:flutter/material.dart';
import 'package:mychips/managers/connection/connection_manager.dart';
import 'package:mychips/managers/connection/ticket.dart';
import 'package:mychips/managers/host/host_manager.dart';

import '../managers/host/host_config.dart';

class MyChipsTestPage extends StatefulWidget {
  const MyChipsTestPage({Key? key}) : super(key: key);

  @override
  createState() => MyChipsTestState();
}

class MyChipsTestState extends State<MyChipsTestPage> {
  final _ticketInputController = TextEditingController();
  final _formKey = GlobalKey<FormState>();

  @override
  void dispose() {
    _ticketInputController.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) => MaterialApp(
        home: Scaffold(
            appBar: AppBar(title: Text("Test Connection")),
            body: Form(
                key: _formKey,
                child: Column(children: [
                  StreamBuilder(
                      stream: HostManager().configStream,
                      builder: (context, snapshot) {
                        final config = snapshot.data as HostConfig?;
                        return Text(snapshot.hasData ? '${config?.host}:${config?.port}' : '');
                      }),
                  Text("Has key: ${ConnectionManager().hasKey}"),
                  TextFormField(
                      enabled: !ConnectionManager().hasKey,
                      controller: _ticketInputController,
                      decoration:
                          const InputDecoration(border: OutlineInputBorder(), hintText: "Ticket")),
                  Padding(
                      padding: const EdgeInsets.symmetric(vertical: 16.0),
                      child: Row(mainAxisAlignment: MainAxisAlignment.spaceEvenly, children: [
                        ElevatedButton(
                            child: const Text('Connect'),
                            onPressed: () async {
                              if (!ConnectionManager().connectionStream.hasValue &&
                                  (ConnectionManager().hasKey ||
                                      _ticketInputController.text != "")) {
                                if (!ConnectionManager().hasKey) {
                                  setState(() {
                                    ConnectionManager().ticket =
                                        Ticket.fromJson(jsonDecode(_ticketInputController.text));
                                  });
                                }
                                await ConnectionManager().connection;
                                // TODO: do something with the socket
                              }
                            }),
                        ElevatedButton(
                            child: const Text('Clear Key'),
                            onPressed: () async {
                              await ConnectionManager().clearKey();
                              setState(() {});
                            }),
                        ElevatedButton(
                            child: const Text('Clear Connection'),
                            onPressed: () async {
                              setState(() {
                                ConnectionManager().clearConnection();
                              });
                            }),
                      ])),
                ]))),
      );

  // static Route<Object?> _userPromptDialog(BuildContext context, Object? arguments) {
  //   return DialogRoute<void>(
  //     context: context,
  //     builder: (BuildContext context) => const AlertDialog(
  //       title: Text('User needed for ticket'),
  //       content: TextField(
  //           controller: _ticketInputController,
  //           decoration: const InputDecoration(border: OutlineInputBorder(), hintText: "Ticket")),
  //     ),
  //   );
  // }
}
