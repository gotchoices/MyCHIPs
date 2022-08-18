import 'package:json_annotation/json_annotation.dart';
part 'account.g.dart';

@JsonSerializable()
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

  factory Account.fromJson(Map<String, dynamic> json) =>
      _$AccountFromJson(json);
  Map<String, dynamic> toJson() => _$AccountToJson(this);
}
