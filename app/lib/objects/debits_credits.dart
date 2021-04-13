import 'dart:math';

class DebitsCredits {
  double getUserBalance() {
    return 41.24;
  }

  double roundDouble(double value, int places){
    double mod = pow(10.0, places);
    return ((value * mod).round().toDouble() / mod);
  }

  Map<String, double> getUserDebitsCredits()
  {
    //TODO: fetch data dynamically
    return {
      "(D) American Express": 1,
      "(D) Robin Hood": 1,
      "(C) Kyle Bateman": 2,
      "(C) Ryan's T-Shirts": 1,
    };
  }
}