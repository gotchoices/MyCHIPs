import 'dart:math';

class DebitsCredits {
  double getUserBalance() {
    var rng = new Random();
    return roundDouble(rng.nextInt(200) + rng.nextDouble(), 2);
  }

  double roundDouble(double value, int places){
    double mod = pow(10.0, places);
    return ((value * mod).round().toDouble() / mod);
  }

  Map<String, double> getUserDebitsCredits()
  {
    //TODO: fetch data dynamically
    return {
      "(D) House Mortgage": 1,
      "(D) Company Investments": 1,
      "(C) MyCHIPs Software Developer": 2,
      "(C) T-Shirt Sales": 1,
    };
  }
}