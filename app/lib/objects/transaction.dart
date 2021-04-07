class Transaction {
  DateTime date;
  String sender;
  String receiver;
  String message;
  var amount;

  Transaction(date, message, sender, receiver, amount) {
    this.date = date;
    this.message = message;
    this.sender = sender;
    this.receiver = receiver;
    this.amount = amount;
  }

  @override
  String toString() {
    return this.sender + " is sending " + this.amount.toString() + " to " + this.receiver + "\nMessage: " + this.message + "\nDate: " + this.date.toString();
   }
}

