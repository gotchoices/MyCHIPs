import 'dart:math';
import 'package:faker/faker.dart';
import 'package:flutter/cupertino.dart';
import 'package:flutter/material.dart';
import 'main_drawer_view.dart';

class ServerSelectPage extends StatefulWidget {
  @override
  ServerSelectPageState createState() => new ServerSelectPageState();
}

class ServerSelectPageState extends State<ServerSelectPage> {
  final List servers = <Server>[];

  @override
  Widget build(BuildContext context) {
    if (servers.length < 1)
      for (int i = 0; i < 5; i++) servers.add(Server.makeFakeServer());

    return Scaffold(
      appBar: AppBar(title: Text('Server Select')),
      body: buildPage(servers),
      drawer: MainDrawer(),
    );
  }
}

Widget buildPage(servers) {
  return Container(child: makeServerList(servers));
}

ExpansionPanelList makeServerList(servers) {
  return ExpansionPanelList(children: [
    servers.map<ExpansionPanel>((Server item) {
      return ExpansionPanel(
          headerBuilder: (BuildContext context, bool isExpanded) {
            return ListTile(title: Text(item.name));
          },
          body: ListTile(
            title: Text(item.ip.toString()),
            subtitle: Text('Active Users: ' + item.users.toString()),
          ));
    })
  ]);
}

class ExpansionItem {
  ExpansionItem(item) {
    item = item;
    header = item.name;
    isExpanded = false;
  }

  Server item;
  String header;
  bool isExpanded;
}

class Server {
  Server(this.name, this.ip, this.users);

  String name;
  String ip;
  int users;

  static Server makeFakeServer() {
    var rand = new Random();
    String newIp = "";

    for (int i = 0; i < 4; i++) {
      newIp += rand.nextInt(128).toString();
      if (i < 3) newIp += ".";
    }

    String name = faker.person.name() + "'s Server";

    return new Server(name, newIp, rand.nextInt(999999));
  }
}
