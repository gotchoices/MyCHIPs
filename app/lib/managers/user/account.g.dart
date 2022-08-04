// GENERATED CODE - DO NOT MODIFY BY HAND

part of 'account.dart';

// **************************************************************************
// JsonSerializableGenerator
// **************************************************************************

Account _$AccountFromJson(Map<String, dynamic> json) => Account(
      json['displayName'] as String,
      json['firstName'] as String,
      json['lastName'] as String,
      email: json['email'] as String?,
      phone: json['phone'] as String?,
      profilePictureURL: json['profilePictureURL'] as String? ??
          "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png",
    );

Map<String, dynamic> _$AccountToJson(Account instance) => <String, dynamic>{
      'displayName': instance.displayName,
      'firstName': instance.firstName,
      'lastName': instance.lastName,
      'email': instance.email,
      'phone': instance.phone,
      'profilePictureURL': instance.profilePictureURL,
    };
