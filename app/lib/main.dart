import 'package:flutter/material.dart';
import 'package:pie_chart/pie_chart.dart';
import 'package:flutter_app/transaction_page.dart';
import 'package:flutter_app/user_info.dart';
import 'tally_list_page.dart';
import 'sign_in.dart';
import 'create_tally_page.dart';
import 'scanner.dart';

void main() {
  runApp(MyChips());
}

class MyChips extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      theme: ThemeData(primaryColor: Color(0xff53ab77)),
      //TODO: Determine if a user is logged in already, if so go to HomePage instead of Login page
      home: SignInPage()
      // Scaffold(appBar: AppBar(title: Text("MyCHIPs"),),
    );
  }
}

class HomePage extends StatefulWidget {
  @override
  PieChartWidget createState() => PieChartWidget();
}

class PieChartWidget extends State<HomePage> {
  Map<String, double> dataMap = {
    "House Mortgage": 1,
    "Company Investments": 1,
    "MyCHIPs Software Developer": 2,
    "T-Shirt Sales": 1,
  };

  List<Color> colorList = [
    Colors.red,
    Colors.orange,
    Colors.green,
    Colors.greenAccent
  ];

  @override
  Widget build(BuildContext context) {
      return new Scaffold(
        appBar: AppBar(title: Text("MyCHIPs home")),
        body: Stack(children: [Center(
            child: PieChart(
              dataMap: dataMap,
              animationDuration: Duration(milliseconds: 2500),
              chartLegendSpacing: 32,
              chartRadius: MediaQuery.of(context).size.width / 1.2,
              colorList: colorList,
              initialAngleInDegree: 0,
              chartType: ChartType.disc,
              ringStrokeWidth: 32,
              legendOptions: LegendOptions(
                showLegendsInRow: true,
                legendPosition: LegendPosition.top,
                showLegends: true,
                legendShape: BoxShape.circle,
                legendTextStyle: TextStyle(
                  fontWeight: FontWeight.bold,
                ),
              ),
              chartValuesOptions: ChartValuesOptions(
                showChartValueBackground: false,
                showChartValues: true,
                showChartValuesInPercentage: true,
                showChartValuesOutside: false,
              ),
            )
        ), buildButtons()]),
        drawer: MainDrawer(),
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
                        Navigator.push(context, MaterialPageRoute(
                            builder: (BuildContext context) => Scanner()));
                      },
                      child: Row(children: [Text('SCAN', style: TextStyle(fontSize: 20)), Icon(Icons.qr_code)]),
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
                              content: buildTransactionWidget(context, 'BOTH'));});
                      },
                      child: const Text('Pay/Request', style: TextStyle(fontSize: 20)),
                      color: Colors.blue,
                      textColor: Colors.white,
                      elevation: 5,
                      height: 50,
                      minWidth: maxButtonWidth
                  )))]));
  }
}

class MainDrawer extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return new Drawer(
        child:ListView(
          children: <Widget>[
            UserAccountsDrawerHeader(
              accountName: Text("myAccount"),
              accountEmail: Text("myemail@gmail.com"),
              currentAccountPicture: GestureDetector (
                onTap: () {
                  Navigator.push(context,
                    MaterialPageRoute(
                      builder: (BuildContext context) => UserInfoPage(false)));
                },
                child: CircleAvatar(
                  backgroundImage: NetworkImage("https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),
              )),
            ),
            ListTile(
              title: Text("Home"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                    builder: (BuildContext context) => HomePage()
                ));
            }),
            ListTile(
              title: Text("My Tallies"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                    builder: (BuildContext context) => TallyListPage()
                ));
              }),
            ListTile(
              title: Text("Create a New Tally"),
              onTap: () {
                Navigator.push(context, MaterialPageRoute(
                  builder: (BuildContext context) => CreateTallyPage()
                ));
              }),
          ],
        )
    );
  }
}