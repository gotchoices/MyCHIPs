class Transaction implements Comparable {
  DateTime date;
  String sender;
  String receiver;
  String message;
  double amount; // TODO: make this a scaled integer, or use currency package

  Transaction(this.date, this.message, this.sender, this.receiver, this.amount);

  @override
  int compareTo(other) {
    int i = date.compareTo(other.date);
    if (i > 0) return -1;
    if (i < 0) return 1;
    return 0;
  }

  @override
  String toString() {
    return sender +
        " is sending " +
        amount.toString() +
        " to " +
        receiver +
        "\nMessage: " +
        message +
        "\nDate: " +
        date.toString();
  }
}
