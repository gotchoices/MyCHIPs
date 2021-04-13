import 'dart:math';

class DebitsCredits {
  double getUserBalance() {
    return 50;
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
      "(D) Company Investments": 1,
      "(C) MyCHIPs Software Developer": 2,
      "(C) T-Shirt Sales": 1,
    };
  }
}