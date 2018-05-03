
select
	cd.cdt_sch
      , cd.cdt_tab
      , cd.cdt_col
      , vu.table_schema
      , vu.table_name
      , cd.cdt_col
      , cd.is_pkey

from	wm.column_data		cd
join	wm.view_column_usage	vu on vu.view_schema = cd.cdt_sch and vu.view_name = cd.cdt_tab and vu.column_name = cd.cdt_col

where	cd.cdt_tab = 'address';
