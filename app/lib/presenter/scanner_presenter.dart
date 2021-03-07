import 'package:flutter_app/objects/tally_registerar.dart';
class ScannerPresenter {
  var registrar = new TallyRegistrar();
  bool registerNewTally(tallyTicket) {
    try {
      registrar.registerNewTally(tallyTicket);
      return true;
    }
    catch (e) {return false;}
  }
}