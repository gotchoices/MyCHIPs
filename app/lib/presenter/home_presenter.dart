import 'package:flutter_app/objects/debits_credits.dart';
import 'package:random_color/random_color.dart';
import 'package:flutter/material.dart';

class HomePresenter {
  var dc = new DebitsCredits();

  double getUserBalance() {
    return dc.getUserBalance();
  }

  Map<String, double> getUserPieChart() {
    return dc.getUserDebitsCredits();
  }

  List<Color> getPieChartColors(dataMap) {
    RandomColor rc = RandomColor();
    List<Color> colorList = [];
    for (int i = 0; i < dataMap.length; i++)
      colorList.add(rc.randomColor());
    return colorList;
  }
}