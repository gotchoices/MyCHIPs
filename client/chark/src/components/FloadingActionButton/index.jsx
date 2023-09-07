import React from "react";
import { View, TouchableOpacity, Text, StyleSheet } from "react-native";
import { AddIcon, ShareIcon } from "../SvgAssets/SvgAssets";

const FloatingActionButton = ({ onPress, type, disabled }) => {
  const getIcon = () => {
    switch (type){
      case 'add':
        return <AddIcon size={23} />;

        case 'share':
          return    (
            <View style={{marginBottom:5}}>
            <ShareIcon size={27}/>
            </View>)

          default :
          return   (<AddIcon size={23} />)
    }
  };

  return (
    <TouchableOpacity style={styles.fab} onPress={onPress} disabled={disabled}>
      <View style={styles.fabContent}>{getIcon()}</View>
    </TouchableOpacity>
  );
};

FloatingActionButton.defaultProps = {
  type: "add",
  disabled: false
};

const styles = StyleSheet.create({
  fab: {
    position: "absolute",
    bottom: 16,
    right: 16,
    width: 56,
    height: 56,
    borderRadius: 28,
    backgroundColor: "#155CEF",
    alignItems: "center",
    justifyContent: "center",
    elevation: 6,
  },
  fabContent: {
    alignItems: "center",
    justifyContent: "center",
  },
});

export default FloatingActionButton;
