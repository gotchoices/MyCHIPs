import 'package:flutter/material.dart';
import 'package:flutter_app/presenter/user_info_presenter.dart';
import 'package:pie_chart/pie_chart.dart';
import 'user_info_page.dart';
import 'tally_search_page.dart';
import 'sign_in_page.dart';
import 'create_tally_page.dart';
import 'scanner_page.dart';
import '../presenter/home_presenter.dart';
import 'package:flutter_app/objects/account.dart';

//TODO: Observer and notifier for when someone else pays/requests payment to you
class MyChips extends StatelessWidget {
  var presenter = new HomePresenter();
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
        theme: ThemeData(primaryColor: Color(0xff53ab77)),
        //TODO: Determine if a user is logged in already, if so go to HomePage instead of Login page
        home: SignInPage());
  }
}

class HomePage extends StatefulWidget {
  @override
  PieChartWidget createState() => PieChartWidget();
}

class PieChartWidget extends State<HomePage> {
  var presenter = new HomePresenter();
  double userBalance;
  Map<String, double> dataMap;
  List<Color> colorList;

  //TODO: How do we choose the colors for the pie chart? Needs to be dynamic as number of colors could be
  // List<Color> colorList = [Colors.red, Colors.orange,Colors.green,Colors.greenAccent];
  void getUserChartData() {
    userBalance = presenter.getUserBalance();
    dataMap = presenter.getUserPieChart();
    colorList = presenter.getPieChartColors(dataMap);
  }

  @override
  Widget build(BuildContext context) {
    getUserChartData();
    return new Scaffold(
      appBar: AppBar(title: Text("MyCHIPs home")),
      body: Stack(children: [
        Center(
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
        )),
        buildButtons(),
        Padding(
            padding: const EdgeInsets.all(15),
            child: Align(
                alignment: Alignment.topCenter,
                child: Text("₵$userBalance", style: TextStyle(fontSize: 50))))
      ]),
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
                    Navigator.push(
                        context,
                        MaterialPageRoute(
                            builder: (BuildContext context) => Scanner()));
                  },
                  child: Row(children: [
                    Text('SCAN', style: TextStyle(fontSize: 20)),
                    Icon(Icons.qr_code)
                  ]),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  height: 50,
                  minWidth: maxButtonWidth))),
      Padding(
          padding: const EdgeInsets.all(10),
          child: Align(
              alignment: Alignment.bottomRight,
              child: MaterialButton(
                  onPressed: () {
                    Navigator.push(
                        context,
                        MaterialPageRoute(
                            builder: (BuildContext context) =>
                                TallySearchPage(1)));
                  },
                  child:
                      const Text('Pay/Request', style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  height: 50,
                  minWidth: maxButtonWidth)))
    ]));
  }
}

class MainDrawer extends StatefulWidget {
  @override
  MainDrawerState createState() {
    var presenter = new UserInfoPresenter();
    var state = MainDrawerState();
    state.setPresenter(presenter);

    return state;
  }

  const MainDrawer({Key key}) : super(key: key);
}

class MainDrawerState extends State<MainDrawer> {
  Account user;
  UserInfoPresenter presenter;

  void setUser(Account _user) {
    setState(() {
      user = _user;
    });
  }

  void setPresenter(UserInfoPresenter uip) {
    setState(() {
      presenter = uip;
    });
  }

  Account getUser() {
    return user;
  }

  UserInfoPresenter getPresenter() {
    return presenter;
  }

  @override
  Widget build(BuildContext context) {
    return new Drawer(
        child: ListView(
      children: <Widget>[
        UserAccountsDrawerHeader(
          accountName: Text(user.displayName),
          accountEmail: Text(user.email),
          currentAccountPicture: GestureDetector(
              onTap: () {
                Navigator.push(
                    context,
                    MaterialPageRoute(
                        builder: (BuildContext context) =>
                            UserInfoPage(false)));
              },
              child: CircleAvatar(
                backgroundImage: NetworkImage(
                    "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"),
              )),
        ),
        ListTile(
            title: Text("Home"),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => HomePage()));
            }),
        ListTile(
            title: Text("My Tallies"),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => TallySearchPage(0)));
            }),
        ListTile(
            title: Text("Create a New Tally"),
            onTap: () {
              Navigator.push(
                  context,
                  MaterialPageRoute(
                      builder: (BuildContext context) => CreateTallyPage()));
            }),
      ],
    ));
  }
}
