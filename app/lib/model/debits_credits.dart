import 'dart:math';

class DebitsCredits {
  double roundDouble(double value, int places){
    double mod = pow(10.0, places);
    return ((value * mod).round().toDouble() / mod);
  }
  double getUserBalance() {
    var rng = new Random();
    return roundDouble(rng.nextInt(200) + rng.nextDouble(), 2);
  }
  Map<String, double> getUserDebitsCredits()
  {
    //TODO: fetch data dynamically
    return {
      "House Mortgage": 1,
      "Company Investments": 1,
      "MyCHIPs Software Developer": 2,
      "T-Shirt Sales": 1,
    };
  }
}