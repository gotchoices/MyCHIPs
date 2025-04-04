import { Alert } from "react-native";
import React, { useEffect } from "react";
import { useDispatch, useSelector } from "react-redux";
import { createBottomTabNavigator } from "@react-navigation/bottom-tabs";
import { createNativeStackNavigator } from "@react-navigation/native-stack";

import useSocket from "../hooks/useSocket";
import {
  getFilter,
  fetchAvatar,
  getPreferredLanguage,
  fetchPersonalAndCurrency,
  setShowCreateSignatureModal,
} from "../redux/profileSlice";
import { getCurrencyRate } from '../redux/chipCurrencySlice';
import { hasNotification } from "../redux/activitySlice";
import { colors, toastVisibilityTime } from "../config/constants";
import { showError } from '../utils/error';
import useMessageText from '../hooks/useMessageText';

import Home from "../screens/Home";
import Invite from "../screens/Invite";
import Scanner from "../screens/Scanner";
import Setting from "../screens/Setting";
import Profile from "../screens/Profile";
import Receive from "../screens/Recieve";
import ShareTally from "../screens/ShareTally";
import CustomIcon from "../components/CustomIcon";
import ChitDetail from "../screens/Tally/ChitDetail";
import TallyReport from "../screens/Tally/TallyReport";
import ChitHistory from "../screens/Tally/ChitHistory";
import TallyPreview from "../screens/Tally/TallyPreview";
import ProfileEdit from "../screens/Profile/ProfileEdit";
import TallyRequest from "../screens/Tally/TallyRequest";
import PendingChits from "../screens/Tally/PendingChits";
import InviteProvider from "../components/InviteProvider";
import EditOpenTally from "../screens/Tally/EditOpenTally";
import TallyContract from "../screens/Tally/TallyContract";
import PaymentDetail from "../screens/Tally/PaymentDetail";
import RequestDetail from "../screens/Tally/RequestDetail";
import RequestShare from "../screens/Recieve/RequestShare";
// Removed FilterTallyScreen import - replaced by inline sorters in Banner
import TradingVariables from "../screens/Tally/TradingVariables";
import TallyCertificate from "../screens/Tally/TallyCertificate";
import PendingChitDetail from "../screens/Tally/PendingChits/Detail";
import { GenerateKeysAlertModal } from '../components/GenerateKeyAlertModal';
import KeyManagement from '../screens/KeyManagement';
import Activity from '../screens/Activity';
import Toast from 'react-native-toast-message';

const screenOptions = {
  headerTitleAlign: "center",
  headerShadowVisible: false,
  headerTintColor: colors.gray300,
  headerTitleStyle: {
    color: colors.gray300,
    fontSize: 18,
    fontFamily: "inter",
    fontWeight: "bold",
  },
};

const Tab = createBottomTabNavigator();

const HomeStack = createNativeStackNavigator();

function HomeStackScreen() {
  return (
    <HomeStack.Navigator screenOptions={screenOptions}>
      <HomeStack.Screen
        name="Home"
        component={Home}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="TallyRequest"
        component={TallyRequest}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="TallyReport"
        component={TallyReport}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="OpenTallyEdit"
        component={EditOpenTally}
        options={{ title: "Open Tally" }}
      />
      <HomeStack.Screen
        name="ChitHistory"
        component={ChitHistory}
        options={{ title: "Chit History" }}
      />
      <HomeStack.Screen
        name="ChitDetail"
        component={ChitDetail}
        options={{ title: "Chit Detail" }}
      />
      <HomeStack.Screen
        name="TradingVariables"
        component={TradingVariables}
        options={{ title: "Trading Variables" }}
      />
      <HomeStack.Screen
        name="PaymentDetail"
        component={PaymentDetail}
        options={{ title: "Payment Detail" }}
      />
      <HomeStack.Screen
        name="RequestDetail"
        component={RequestDetail}
        options={{ title: "Request Detail" }}
      />
      <HomeStack.Screen
        name="Activity"
        component={Activity}
        options={{ title: "Activity" }}
      />
      <HomeStack.Screen
        name="TallyPreview"
        component={TallyPreview}
        options={{ title: "Tally Preview" }}
      />
      <InviteStack.Screen
        name="TallyCertificate"
        component={TallyCertificate}
        options={{ title: "Tally Certificate" }}
      />
      <HomeStack.Screen
        name="PendingChits"
        component={PendingChits}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="PendingChitDetail"
        component={PendingChitDetail}
        options={{ headerShown: false }}
      />
      {/* FilterTallyScreen route removed - replaced by inline sorters in Banner */}
      <InviteStack.Screen
        name="TallyContract"
        component={TallyContract}
        options={{ title: "Tally Contract" }}
      />
    </HomeStack.Navigator>
  );
}

const InviteStack = createNativeStackNavigator();
function InviteStackScreen() {
  return (
    <InviteProvider>
      <InviteStack.Navigator screenOptions={screenOptions}>
        <InviteStack.Screen
          name="Invite"
          component={Invite}
          options={{ headerShown: false }}
        />
        <InviteStack.Screen
          name="TallyPreview"
          component={TallyPreview}
          options={{ title: "Tally Preview" }}
        />
        <InviteStack.Screen
          name="TallyShare"
          component={ShareTally}
          options={{ title: "Share Tally", headerShadowVisible: false }}
        />
        <InviteStack.Screen
          name="TallyContract"
          component={TallyContract}
          options={{ title: "Tally Contract" }}
        />
        <InviteStack.Screen
          name="TallyCertificate"
          component={TallyCertificate}
          options={{ title: "Tally Certificate" }}
        />
      </InviteStack.Navigator>
    </InviteProvider>
  );
}

const ReceiveStack = createNativeStackNavigator();
function ReceiveStackScreen() {
  return (
    <ReceiveStack.Navigator screenOptions={screenOptions}>
      <ReceiveStack.Screen name="Request" component={Receive} />
      <ReceiveStack.Screen name="RequestShare" component={RequestShare} />
    </ReceiveStack.Navigator>
  );
}

const SettingStack = createNativeStackNavigator();
function SettingStackScreen() {
  return (
    <SettingStack.Navigator screenOptions={screenOptions}>
      <SettingStack.Screen name="Setting" component={Setting} />
      <SettingStack.Screen
        name="Profile"
        component={Profile}
        options={{ title: "Profile" }}
      />
      <SettingStack.Screen
        name="ProfileEdit"
        component={ProfileEdit}
        options={{ title: "Edit Profile" }}
      />
      <SettingStack.Screen
        name="KeyManagement"
        component={KeyManagement}
        options={{ title: "Key Management" }}
      />
    </SettingStack.Navigator>
  );
}

const Navigator = () => {
  const { user } = useSelector((state) => state.currentUser);
  const { showCreateSignatureModal } = useSelector((state) => state.profile);
  const user_ent = user?.curr_eid;
  const { wm } = useSocket();
  const dispatch = useDispatch();
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  // Separate useEffect specifically for user-related data fetching
  // Get the current preferred currency from state
  const { preferredCurrency } = useSelector(state => state.profile);
  
  useEffect(() => {
    if (user_ent && wm) {
      dispatch(fetchAvatar({ wm, user_ent }));
      dispatch(fetchPersonalAndCurrency({ wm, user_ent }));
    }
  }, [user, wm, dispatch]); // Using the full user object ensures proper dependency tracking
  
  // Fetch currency rate when preferredCurrency changes
  useEffect(() => {
    if (wm && preferredCurrency?.code) {
      console.log('Fetching currency rate in Navigator for:', preferredCurrency.code);
      dispatch(getCurrencyRate({ 
        wm, 
        currencyCode: preferredCurrency.code 
      }));
    }
  }, [preferredCurrency?.code, wm, dispatch]);
  
  // Keep the original useEffect for other initialization tasks
  useEffect(() => {
    dispatch(getPreferredLanguage(wm));
    dispatch(getFilter());
    // Removed getTallyListFilter() - replaced by tallySortSlice
    dispatch(hasNotification({ wm }));
  }, [wm, dispatch]);

  const onDismissSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(false))
  }

  const onKeySaved = () => {
    dispatch(setShowCreateSignatureModal(false))
    Toast.show({
      type: 'success',
      text1: charkText?.success?.help,
      visibilityTime: toastVisibilityTime,
    });
  }

  return (
    <>
      <Tab.Navigator
        screenOptions={{ headerShown: false, tabBarShowLabel: false }}
      >
        <Tab.Screen
          name="Tally"
          component={HomeStackScreen}
          options={{
            tabBarIcon: (props) => (
              <CustomIcon name="home" {...{ ...props, size: 24 }} />
            ),
          }}
        />

        <Tab.Screen
          name="RequestScreen"
          component={ReceiveStackScreen}
          options={{
            title: "Request",
            tabBarIcon: (props) => (
              <CustomIcon name="receive" {...{ ...props, size: 26 }} />
            ),
          }}
        />

        <Tab.Screen
          name="Scan"
          component={Scanner}
          options={{
            unmountOnBlur: true,
            tabBarIcon: (props) => (
              <CustomIcon name="scan" {...{ ...props, size: 23 }} />
            ),
          }}
        />

        <Tab.Screen
          name="InviteScreen"
          component={InviteStackScreen}
          options={{
            tabBarTestID: "inviteBtn",
            tabBarIcon: (props) => (
              <CustomIcon name="invite" {...{ ...props, size: 26 }} />
            ),
          }}
        />

        <Tab.Screen
          name="Settings"
          component={SettingStackScreen}
          options={{
            tabBarIcon: (props) => (
              <CustomIcon name="settings" {...{ ...props, size: 25 }} />
            ),
          }}
        />
      </Tab.Navigator>
      <GenerateKeysAlertModal
        visible={showCreateSignatureModal}
        onDismiss={onDismissSignatureModal}
        onKeySaved={onKeySaved}
        onError={(err) => {
          showError(err)
        }}
      />
    </>
  );
};

export default Navigator;
