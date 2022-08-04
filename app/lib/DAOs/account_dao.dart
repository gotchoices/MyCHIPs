import '../managers/user/account.dart';
//import '../services.dart';

class AccountDao {
  Future<Account> getAccountData() async {
    //connect to account
    // Account a = await Services.getUserData();
    // return a;
    return Account("Test Person", "Test", "Person",
        email: "test@person.com", phone: "555-555-5555");
  }

  void setAccountData(account) async {
    //establish persistence here
    // int check = await Services.setUserData(account);
  }
}
