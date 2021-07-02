import 'package:flutter/material.dart';

class QRPresenter {
  Image generateQRCode() {
    //TODO: does qr generator need to interface with the server or can we just generate it locally?
    return Image(image : NetworkImage('https://i.pinimg.com/originals/60/c1/4a/60c14a43fb4745795b3b358868517e79.png'));
  }
}