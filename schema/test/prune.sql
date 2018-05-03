select o.obj_typ, o.obj_nam, o.obj_ver, o.module, o.source
    from	wm.objects	o
    join	(select distinct module, source from wm.objects where obj_ver = 0) as od on od.module = o.module and od.source = o.source
    where 	wm.release() between o.min_rel and o.max_rel
    and		o.source != ''
    and		not exists (select obj_nam from wm.objects where obj_typ = o.obj_typ and obj_nam = o.obj_nam and obj_ver = 0)
;
