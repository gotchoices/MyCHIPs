class Transaction implements Comparable {
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
  int compareTo(other) {
    int i = this.date.compareTo(other.date);
    if (i > 0)
      return -1;
    if (i < 0)
      return 1;
    return 0;
  }

  @override
  String toString() {
    return this.sender + " is sending " + this.amount.toString() + " to " + this.receiver + "\nMessage: " + this.message + "\nDate: " + this.date.toString();
   }
}

