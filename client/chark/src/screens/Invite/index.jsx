import React, { useState, useEffect } from 'react';
import { View, Text, StyleSheet, TouchableOpacity, Animated } from 'react-native';
import Toast from 'react-native-toast-message';
import { colors } from '../../config/constants';
import { random } from '../../utils/common';
import useSocket from '../../hooks/useSocket';
import useInvite from '../../hooks/useInvite';
import { createTemplate } from '../../services/tally';
import TemplateItem from './TemplateItem';
import CustomTextInput from '../../components/CustomTextInput';
import { FilterSecondIcon, SearchIcon } from '../../components/SvgAssets/SvgAssets';
import FloatingActionButton from '../../components/FloadingActionButton';

const Header_Height = 120;

const useSearchData = (initialData) => {
  const [searchValue, setSearchValue] = useState('');
  const [filteredData, setFilteredData] = useState(initialData);

  useEffect(() => {
    if (searchValue) {
      const filtered = initialData.filter((item) => {
        const userName = item.part_cert?.name;
        const name = `${userName?.first}${userName?.middle ? ' ' + userName?.middle + ' ' : ''} ${userName?.surname}`
        return name.toLowerCase().includes(searchValue.toLowerCase());
      });
      setFilteredData(filtered);
    } else {
      setFilteredData(initialData);
    }
  }, [searchValue, initialData]);

  return { searchValue, setSearchValue, filteredData };
};

const TallyInvite = (props) => {
  const [data, setData] = useState([]);
  const { searchValue, setSearchValue, filteredData } = useSearchData(data);
  const [loading, setLoading] = useState(false);
  const { wm, ws } = useSocket();
  const { triggerInviteFetch } = useInvite();

  useEffect(() => {
    if (ws) {
      fetchTemplates();
    }
  }, [ws, triggerInviteFetch]);

  //Create a new template
  const newTemplate = () => {
    const payload = {
      contract: { terms: 'Some Terms' },
      comment: 'Test: ' + new Date(),
      hold_terms: {
        call: 30,
      }, part_terms: {
        call: 30,
      },
    }

    createTemplate(wm, payload).then((data) => {
      console.log("CREATE_RESULT ==> ", JSON.stringify(data));
      fetchTemplates()
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err?.message ?? 'Error creating new template',
      });
    })
  }

  const fetchTemplates = () => {
    setLoading(true);
    const spec = {
      fields: [
        'tally_ent',
        'tally_seq',
        'contract',
        'comment',
        'tally_uuid',
        'hold_terms',
        'part_terms',
        'tally_type',
        'status',
        'part_cid',
        'part_cert',
      ],
      view: 'mychips.tallies_v_me',
      // where: { left: "status", oper: "in", entry: "draft offer" },
      order: {
        field: 'crt_date',
        asc: false,
      }
    }

    wm.request('_inv_ref' + random(), 'select', spec, (data, err) => {
      const _data = data?.map(el => ({
        tally_ent: el.tally_ent,
        id: el.tally_seq,
        contract: el.contract,
        comment: el.comment,
        hold_terms: el.hold_terms,
        part_terms: el.part_terms,
        tally_type: el.tally_type,
        status: el.status,
        part_cid: el.part_cid,
        part_cert: el.part_cert,
      }));

      setData(_data);
      setLoading(false);
    });
  }

  const renderItem = ({ item, index }) => {
    return (
      <TemplateItem
        testID={`tally-${index}`}
        template={item}
        navigation={props.navigation}
      />
    )
  }
  const onFilter = () => {
    props.navigation.navigate("FilterScreen");
  }

  const scrollY = new Animated.Value(0);
  const diffClampScrollY = Animated.diffClamp(scrollY, 0, Header_Height);
  const headerY = diffClampScrollY.interpolate({
    inputRange: [0, Header_Height],
    outputRange: [0, -Header_Height],
    extrapolate: 'clamp'
  });

  return (
    <View style={styles.container}>
      <Animated.View style={[styles.header, { transform: [{ translateY: headerY }] }]}>
        <CustomTextInput
          placeholder="Search"
          value={searchValue}
          onChangeText={setSearchValue}
          leadingIcon={<SearchIcon size={16} />}
        />
        <View style={styles.row}>
          <Text style={styles.title}>Drafts</Text>
          <TouchableOpacity style={styles.filterContainer} onPress={onFilter}>
            <FilterSecondIcon />
            <Text style={styles.filterText}>Filters</Text>
          </TouchableOpacity>
        </View>
      </Animated.View>

      <Animated.FlatList
        bounces={false}
        ListHeaderComponent={<View style={{ height: Header_Height }} />}
        contentContainerStyle={{ paddingHorizontal: 16, paddingBottom: 16, backgroundColor: colors.white }}
        data={filteredData}
        renderItem={renderItem}
        refreshing={loading}
        onRefresh={() => fetchTemplates()}
        keyExtractor={(item, index) => `${item.tally_ent}${item?.tally_uuid}${item?.tally_seq}${index}`}
        ItemSeparatorComponent={() => <View style={{ height: 16 }} />}
        scrollEventThrottle={2}
        onScroll={Animated.event(
          [{
            nativeEvent: { contentOffset: { y: scrollY } }
          }],
          {
            useNativeDriver: false,
          }
        )}
        progressViewOffset={100}
      />
      <FloatingActionButton onPress={newTemplate} />
    </View>
  );
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    backgroundColor: colors.white,
  },
  listContainer: {
    flex: 1,
  },
  listHeading: {
    flexDirection: 'row',
    flexWrap: 'wrap',
    marginVertical: 10,
    alignItems: 'center',
  },
  webViewContainer: {
    flex: 1,
  },
  templateText: {
    marginVertical: 10,
    fontSize: 18,
    fontWeight: 'bold',
    color: colors.black,
  },
  regenerate: {
    marginBottom: 10,
  },
  title: {
    fontSize: 16,
    color: '#636363'
  },
  row: {
    flexDirection: 'row',
    marginTop: 16,
    justifyContent: 'space-between',
    alignItems: 'center'
  },
  headerContainer: {
    //padding: 16,
  },
  filterContainer: {
    borderWidth: 1,
    borderColor: "#F0F0F0",
    backgroundColor: '#E7E7E7',
    flexDirection: 'row',
    borderRadius: 16,
    paddingHorizontal: 8,
    paddingVertical: 4,
    justifyContent: 'center',
    alignItems: 'center'
  },
  filterText: {
    fontSize: 12,
    color: '#636363',
    marginStart: 4,
  },
  header: {
    position: 'absolute',
    left: 0,
    right: 0,
    top: 0,
    height: Header_Height,
    backgroundColor: colors.white,
    zIndex: 1000,
    justifyContent: 'center',
    paddingHorizontal: 16,
  }
})

export default TallyInvite;
