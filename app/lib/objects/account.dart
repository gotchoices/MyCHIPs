class Account {
  String displayName;
  String firstName;
  String lastName;
  String email;
  String phone;
  String profilePictureURL;

  Account ([String displayName, String firstName, String lastName, String email, String phone, String URL = "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png"]) {
    this.displayName = displayName;
    this.firstName = firstName;
    this.lastName = lastName;
    this.email = email;
    this.phone = phone;
    this.profilePictureURL = URL;
  }
}