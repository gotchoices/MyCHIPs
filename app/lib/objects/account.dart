class Account {
  String displayName;
  String firstName;
  String lastName;
  String? email;
  String? phone;
  String profilePictureURL;

  Account(this.displayName, this.firstName, this.lastName,
      {this.email,
      this.phone,
      this.profilePictureURL =
          "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"});
}
