import React, { useEffect, useState, useMemo } from "react";
import {
  View,
  StyleSheet,
  FlatList,
  TouchableWithoutFeedback,
  Dimensions,
} from "react-native";
import { useSelector, useDispatch } from "react-redux";

import useSocket from '../../hooks/useSocket';
import { round } from '../../utils/common';
import { getCurrency } from '../../services/user';
import { useUserTalliesText } from '../../hooks/useLanguage';
import { fetchOpenTallies, updateTallyOnChitTransferred } from '../../redux/openTalliesSlice';
import { fetchImagesByDigest as fetchImages } from '../../redux/avatarSlice';

import TallyItem from "./TallyItem";
import TallyHeader from "./TallyHeader";
import PayModal from "../Pay";
import { colors } from "../../config/constants";

const Tally = (props) => {
  const { wm, tallyNegotiation, chitTrigger } = useSocket();
  const dispatch = useDispatch();
  const { preferredCurrency } = useSelector(state => state.profile);
  const { imageFetchTrigger, tallies: tallies, /*imagesByDigest,*/ fetching } = useSelector(state => state.openTallies);
  const { imagesByDigest } = useSelector(state => state.avatar);
  useUserTalliesText(wm);

  const [conversionRate, setConversionRate] = useState(0);

  const currencyCode = preferredCurrency.code;

  const [tally, setTally] = useState();

  const [isVisible,setIsVisible]= useState(false)

  const fetchTallies = () => {
    if (wm) {
      dispatch(fetchOpenTallies({ wm }));
    }
  };

  useEffect(() => {
    fetchTallies();
  }, [wm, dispatch, fetchOpenTallies, tallyNegotiation])

  useEffect(() => {
    if(wm) {
      dispatch(fetchImages({ wm, status: 'open' }))
    }
  }, [wm, imageFetchTrigger]);

  useEffect(() => {
    if (currencyCode) {
      getCurrency(wm, currencyCode)
        .then((data) => {
          setConversionRate(parseFloat(data?.rate ?? 0));
        })
        .catch((err) => {
          // TODO
        });
    }
  }, [currencyCode]);

  useEffect(() => {
    if(chitTrigger) {
      dispatch(
        updateTallyOnChitTransferred(chitTrigger)
      )
    }
  }, [chitTrigger])

  const totalNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + Number(current?.net ?? 0);
    }, 0);

    return round(total / 1000, 3);
  }, [tallies]);

  const totalPendingNet = useMemo(() => {
    let total = tallies.reduce((acc, current) => {
      return acc + Number(current?.net_pc ?? 0);
    }, 0);

    return round(total / 1000, 3);
  }, [tallies]);

  const totalNetDollar = useMemo(() => {
    if (conversionRate) {
      const total = totalNet * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [totalNet, conversionRate]);

  const onItemPress = ({ tally}) => {
    setTally(tally);
    setIsVisible(true)
  };


  const renderItem = ({ item, index }) => (
    <TouchableWithoutFeedback
      onPress={()=>{onItemPress({
tally:item
      })}}
    >
      <View
        style={[
          styles.item,
          index === tallies?.length - 1 ? styles.itemLast : null,
        ]}
      >
        <TallyItem
          tally={item}
          image={imagesByDigest?.[item?.part_cert?.file?.[0]?.digest]}
          conversionRate={conversionRate}
          currency={preferredCurrency?.code}
        />
      </View>
    </TouchableWithoutFeedback>
  );

  return (
    <View>
      <FlatList
        ListHeaderComponent={
          <TallyHeader
            totalNet={totalNet}
            totalPendingNet={totalPendingNet}
            totalNetDollar={totalNetDollar}
            currencyCode={preferredCurrency.code}
            navigation={props.navigation}
          />
        }
        ListFooterComponent={<View style={styles.footer} />}
        contentContainerStyle={styles.contentContainer}
        data={tallies}
        renderItem={renderItem}
        showsVerticalScrollIndicator={false}
        keyExtractor={(_, index) => index}
        refreshing={fetching}
        onRefresh={fetchTallies}
      />

      <PayModal
        tally={tally}
        visible={isVisible}
        navigation={props.navigation}
        onClose={()=>setIsVisible(false)}
        conversionRate={conversionRate}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  contentContainer: {
    paddingBottom: 16,
    backgroundColor: colors.white,
  },
  item: {
    width: "90%",
    paddingVertical: 18,
    alignSelf: "center",
    borderBottomWidth: 1,
    paddingHorizontal: 12,
    borderBottomColor: colors.lightgray,
  },
  itemLast: {
    borderBottomWidth: 0,
  },
  footer: {
    backgroundColor: colors.white,
    height: Dimensions.get("window").height*0.3,
  },
});

export default Tally;
