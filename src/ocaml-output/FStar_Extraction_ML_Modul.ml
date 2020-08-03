open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu____25 =
        let uu____26 =
          let uu____43 =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let uu____46 =
            let uu____57 = FStar_Syntax_Syntax.iarg t in
            let uu____66 =
              let uu____77 =
                let uu____86 =
                  let uu____87 =
                    let uu____88 =
                      let uu____89 =
                        let uu____94 =
                          let uu____95 = FStar_Syntax_Print.lid_to_string lid in
                          Prims.op_Hat "Not yet implemented:" uu____95 in
                        (uu____94, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____89 in
                    FStar_Syntax_Syntax.Tm_constant uu____88 in
                  FStar_Syntax_Syntax.mk uu____87 FStar_Range.dummyRange in
                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____86 in
              [uu____77] in
            uu____57 :: uu____66 in
          (uu____43, uu____46) in
        FStar_Syntax_Syntax.Tm_app uu____26 in
      FStar_Syntax_Syntax.mk uu____25 FStar_Range.dummyRange
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid ->
    fun t ->
      let imp =
        let uu____157 = FStar_Syntax_Util.arrow_formals t in
        match uu____157 with
        | ([], t1) ->
            let b =
              let uu____184 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____184 in
            let uu____191 = fail_exp lid t1 in
            FStar_Syntax_Util.abs [b] uu____191 FStar_Pervasives_Native.None
        | (bs, t1) ->
            let uu____212 = fail_exp lid t1 in
            FStar_Syntax_Util.abs bs uu____212 FStar_Pervasives_Native.None in
      let lb =
        let uu____216 =
          let uu____221 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____221 in
        {
          FStar_Syntax_Syntax.lbname = uu____216;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        } in
      lb
let as_pair : 'uuuuuu228 . 'uuuuuu228 Prims.list -> ('uuuuuu228 * 'uuuuuu228)
  =
  fun uu___0_239 ->
    match uu___0_239 with
    | a::b::[] -> (a, b)
    | uu____244 -> failwith "Expected a list with 2 elements"
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_257 ->
    match uu___1_257 with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____260 -> FStar_Pervasives_Native.None
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu____268 = FStar_Syntax_Subst.compress x in
    match uu____268 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____272;
        FStar_Syntax_Syntax.vars = uu____273;_} ->
        let uu____276 =
          let uu____277 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____277 in
        (match uu____276 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu____280 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____282;
             FStar_Syntax_Syntax.vars = uu____283;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu____285));
              FStar_Syntax_Syntax.pos = uu____286;
              FStar_Syntax_Syntax.vars = uu____287;_},
            uu____288)::[]);
        FStar_Syntax_Syntax.pos = uu____289;
        FStar_Syntax_Syntax.vars = uu____290;_} ->
        let uu____331 =
          let uu____332 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____332 in
        (match uu____331 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated s)
         | uu____335 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate", uu____336));
        FStar_Syntax_Syntax.pos = uu____337;
        FStar_Syntax_Syntax.vars = uu____338;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu____341));
        FStar_Syntax_Syntax.pos = uu____342;
        FStar_Syntax_Syntax.vars = uu____343;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu____346));
        FStar_Syntax_Syntax.pos = uu____347;
        FStar_Syntax_Syntax.vars = uu____348;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____352);
        FStar_Syntax_Syntax.pos = uu____353;
        FStar_Syntax_Syntax.vars = uu____354;_} -> extract_meta x1
    | uu____361 -> FStar_Pervasives_Native.None
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders :
  'uuuuuu379 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu379) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu____419 ->
             match uu____419 with
             | (bv, uu____429) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false in
                 let name =
                   let uu____432 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv in
                   match uu____432 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____434 -> failwith "Impossible" in
                 (env2, name)) env bs
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dname
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dtyp
type inductive_family =
  {
  ifv: FStar_Syntax_Syntax.fv ;
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
let (print_ifamily : inductive_family -> unit) =
  fun i ->
    let uu____623 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____624 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____625 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____626 =
      let uu____627 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu____638 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____639 =
                  let uu____640 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.op_Hat " : " uu____640 in
                Prims.op_Hat uu____638 uu____639)) in
      FStar_All.pipe_right uu____627 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____623 uu____624 uu____625
      uu____626
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        let uu____678 =
          FStar_Util.fold_map
            (fun env1 ->
               fun se ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l, us, bs, t, _mut_i, datas) ->
                     let uu____731 = FStar_Syntax_Subst.open_univ_vars us t in
                     (match uu____731 with
                      | (_us, t1) ->
                          let uu____744 = FStar_Syntax_Subst.open_term bs t1 in
                          (match uu____744 with
                           | (bs1, t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1 ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d, us1, t3, l', nparams,
                                              uu____790)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____795 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3 in
                                             (match uu____795 with
                                              | (_us1, t4) ->
                                                  let uu____804 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4 in
                                                  (match uu____804 with
                                                   | (bs', body) ->
                                                       let uu____819 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs' in
                                                       (match uu____819 with
                                                        | (bs_params, rest)
                                                            ->
                                                            let subst =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____910
                                                                   ->
                                                                   fun
                                                                    uu____911
                                                                    ->
                                                                    match 
                                                                    (uu____910,
                                                                    uu____911)
                                                                    with
                                                                    | 
                                                                    ((b',
                                                                    uu____937),
                                                                    (b,
                                                                    uu____939))
                                                                    ->
                                                                    let uu____960
                                                                    =
                                                                    let uu____967
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    (b',
                                                                    uu____967) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____960)
                                                                bs_params bs1 in
                                                            let t5 =
                                                              let uu____973 =
                                                                let uu____974
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____974 in
                                                              FStar_All.pipe_right
                                                                uu____973
                                                                (FStar_Syntax_Subst.subst
                                                                   subst) in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____977 -> [])) in
                               let metadata =
                                 let uu____981 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs in
                                 let uu____984 =
                                   FStar_List.choose flag_of_qual quals in
                                 FStar_List.append uu____981 uu____984 in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None in
                               let uu____988 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv in
                               (match uu____988 with
                                | (uu____999, env2) ->
                                    (env2,
                                      [{
                                         ifv = fv;
                                         iname = l;
                                         iparams = bs1;
                                         ityp = t2;
                                         idatas = datas1;
                                         iquals =
                                           (se.FStar_Syntax_Syntax.sigquals);
                                         imetadata = metadata
                                       }]))))
                 | uu____1003 -> (env1, [])) env ses in
        match uu____678 with
        | (env1, ifams) -> (env1, (FStar_List.flatten ifams))
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
let (__proj__Mkiface__item__iface_tydefs :
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
let (__proj__Mkiface__item__iface_type_names :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  }
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list
    -> iface)
  =
  fun fvs ->
    let uu___221_1205 = empty_iface in
    {
      iface_module_name = (uu___221_1205.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___221_1205.iface_tydefs);
      iface_type_names = (uu___221_1205.iface_type_names)
    }
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds ->
    let uu___224_1215 = empty_iface in
    let uu____1216 =
      FStar_List.map
        (fun td ->
           let uu____1231 = FStar_Extraction_ML_UEnv.tydef_fv td in
           let uu____1232 = FStar_Extraction_ML_UEnv.tydef_mlpath td in
           (uu____1231, uu____1232)) tds in
    {
      iface_module_name = (uu___224_1215.iface_module_name);
      iface_bindings = (uu___224_1215.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1216
    }
let (iface_of_type_names :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ->
    iface)
  =
  fun fvs ->
    let uu___228_1250 = empty_iface in
    {
      iface_module_name = (uu___228_1250.iface_module_name);
      iface_bindings = (uu___228_1250.iface_bindings);
      iface_tydefs = (uu___228_1250.iface_tydefs);
      iface_type_names = fvs
    }
let (iface_union : iface -> iface -> iface) =
  fun if1 ->
    fun if2 ->
      let uu____1261 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name in
      {
        iface_module_name = uu____1261;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs -> FStar_List.fold_right iface_union ifs empty_iface
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
let tscheme_to_string :
  'uuuuuu1295 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('uuuuuu1295 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm ->
    fun ts ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm ->
    fun e ->
      let uu____1324 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr in
      let uu____1325 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme in
      FStar_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1324 uu____1325
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm ->
    fun uu____1339 ->
      match uu____1339 with
      | (fv, exp_binding) ->
          let uu____1346 = FStar_Syntax_Print.fv_to_string fv in
          let uu____1347 = print_exp_binding cm exp_binding in
          FStar_Util.format2 "(%s, %s)" uu____1346 uu____1347
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm ->
    fun tydef ->
      let uu____1358 =
        let uu____1359 = FStar_Extraction_ML_UEnv.tydef_fv tydef in
        FStar_Syntax_Print.fv_to_string uu____1359 in
      let uu____1360 =
        let uu____1361 = FStar_Extraction_ML_UEnv.tydef_def tydef in
        tscheme_to_string cm uu____1361 in
      FStar_Util.format2 "(%s, %s)" uu____1358 uu____1360
let (iface_to_string : iface -> Prims.string) =
  fun iface1 ->
    let cm = iface1.iface_module_name in
    let print_type_name uu____1381 =
      match uu____1381 with
      | (tn, uu____1387) -> FStar_Syntax_Print.fv_to_string tn in
    let uu____1388 =
      let uu____1389 =
        FStar_List.map (print_binding cm) iface1.iface_bindings in
      FStar_All.pipe_right uu____1389 (FStar_String.concat "\n") in
    let uu____1398 =
      let uu____1399 = FStar_List.map (print_tydef cm) iface1.iface_tydefs in
      FStar_All.pipe_right uu____1399 (FStar_String.concat "\n") in
    let uu____1404 =
      let uu____1405 = FStar_List.map print_type_name iface1.iface_type_names in
      FStar_All.pipe_right uu____1405 (FStar_String.concat "\n") in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1388 uu____1398
      uu____1404
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env in
    let gamma =
      let uu____1427 = FStar_Extraction_ML_UEnv.bindings_of_uenv env in
      FStar_List.collect
        (fun uu___2_1437 ->
           match uu___2_1437 with
           | FStar_Extraction_ML_UEnv.Fv (b, e) -> [(b, e)]
           | uu____1454 -> []) uu____1427 in
    let uu____1459 =
      let uu____1460 = FStar_List.map (print_binding cm) gamma in
      FStar_All.pipe_right uu____1460 (FStar_String.concat "\n") in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1459
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let uu____1513 =
            let uu____1522 =
              let uu____1531 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
              FStar_TypeChecker_Env.open_universes_in uu____1531
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
            match uu____1522 with
            | (tcenv, uu____1541, def_typ) ->
                let uu____1547 = as_pair def_typ in (tcenv, uu____1547) in
          match uu____1513 with
          | (tcenv, (lbdef, lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant;
                  FStar_TypeChecker_Env.ForExtraction] tcenv lbtyp in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let def =
                let uu____1578 =
                  let uu____1579 = FStar_Syntax_Subst.compress lbdef1 in
                  FStar_All.pipe_right uu____1579 FStar_Syntax_Util.unmeta in
                FStar_All.pipe_right uu____1578 FStar_Syntax_Util.un_uinst in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1587 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1606 -> def in
              let uu____1607 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1618) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1643 -> ([], def1) in
              (match uu____1607 with
               | (bs, body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1662 ->
                          match uu___3_1662 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu____1663 -> false) quals in
                   let uu____1664 = binders_as_mlty_binders env bs in
                   (match uu____1664 with
                    | (env1, ml_bs) ->
                        let body1 =
                          let uu____1688 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body in
                          FStar_All.pipe_right uu____1688
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                        let metadata =
                          let uu____1692 = extract_metadata attrs in
                          let uu____1695 =
                            FStar_List.choose flag_of_qual quals in
                          FStar_List.append uu____1692 uu____1695 in
                        let tyscheme = (ml_bs, body1) in
                        let uu____1703 =
                          let uu____1716 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1720 ->
                                    match uu___4_1720 with
                                    | FStar_Syntax_Syntax.Assumption -> true
                                    | FStar_Syntax_Syntax.New -> true
                                    | uu____1721 -> false)) in
                          if uu____1716
                          then
                            let uu____1734 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv in
                            match uu____1734 with
                            | (mlp, env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu____1768 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme in
                             match uu____1768 with
                             | (td, mlp, env2) ->
                                 let uu____1790 = iface_of_tydefs [td] in
                                 (mlp, uu____1790, env2)) in
                        (match uu____1703 with
                         | (mlpath, iface1, env2) ->
                             let td =
                               (assumed,
                                 (FStar_Pervasives_Native.snd mlpath),
                                 FStar_Pervasives_Native.None, ml_bs,
                                 metadata,
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Extraction_ML_Syntax.MLTD_Abbrev
                                       body1))) in
                             let def2 =
                               let uu____1846 =
                                 let uu____1847 =
                                   let uu____1848 =
                                     FStar_Ident.range_of_lid lid in
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     uu____1848 in
                                 FStar_Extraction_ML_Syntax.MLM_Loc
                                   uu____1847 in
                               [uu____1846;
                               FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                             (env2, iface1, def2))))
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let lbtyp =
            let uu____1896 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.ForExtraction] uu____1896
              lb.FStar_Syntax_Syntax.lbtyp in
          let uu____1897 = FStar_Syntax_Util.arrow_formals lbtyp in
          match uu____1897 with
          | (bs, uu____1913) ->
              let uu____1918 = binders_as_mlty_binders env bs in
              (match uu____1918 with
               | (env1, ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top in
                   let metadata =
                     let uu____1947 = extract_metadata attrs in
                     let uu____1950 = FStar_List.choose flag_of_qual quals in
                     FStar_List.append uu____1947 uu____1950 in
                   let assumed = false in
                   let tscheme = (ml_bs, body) in
                   let uu____1959 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv tscheme in
                   (match uu____1959 with
                    | (tydef, mlp, env2) ->
                        let td =
                          (assumed, (FStar_Pervasives_Native.snd mlp),
                            FStar_Pervasives_Native.None, ml_bs, metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body))) in
                        let def =
                          let uu____2003 =
                            let uu____2004 =
                              let uu____2005 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____2005 in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____2004 in
                          [uu____2003;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                        let iface1 = iface_of_tydefs [tydef] in
                        (env2, iface1, def)))
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2069 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2069 in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____2076 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu____2076 with | (env2, uu____2092, b) -> (env2, (fvv, b)) in
      let extract_one_family env1 ind =
        let uu____2129 = binders_as_mlty_binders env1 ind.iparams in
        match uu____2129 with
        | (env_iparams, vars) ->
            let uu____2154 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____2154 with
             | (env2, ctors) ->
                 let env3 =
                   let uu____2206 =
                     FStar_Util.find_opt
                       (fun uu___5_2211 ->
                          match uu___5_2211 with
                          | FStar_Syntax_Syntax.RecordType uu____2212 -> true
                          | uu____2221 -> false) ind.iquals in
                   match uu____2206 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                       let g =
                         FStar_List.fold_right
                           (fun id ->
                              fun g ->
                                let uu____2240 =
                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                    g ((ind.iname), id) in
                                match uu____2240 with
                                | (uu____2245, g1) -> g1) ids env2 in
                       g
                   | uu____2247 -> env2 in
                 (env3, ctors)) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____2263, t, uu____2265, uu____2266, uu____2267);
            FStar_Syntax_Syntax.sigrng = uu____2268;
            FStar_Syntax_Syntax.sigquals = uu____2269;
            FStar_Syntax_Syntax.sigmeta = uu____2270;
            FStar_Syntax_Syntax.sigattrs = uu____2271;
            FStar_Syntax_Syntax.sigopts = uu____2272;_}::[],
          uu____2273),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____2292 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____2292 with
           | (env1, ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2324), quals) ->
          let uu____2338 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu____2338
          then (env, empty_iface)
          else
            (let uu____2344 = bundle_as_inductive_families env ses quals in
             match uu____2344 with
             | (env1, ifams) ->
                 let uu____2361 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu____2361 with
                  | (env2, td) ->
                      let uu____2402 =
                        let uu____2403 =
                          let uu____2404 =
                            FStar_List.map
                              (fun x ->
                                 let uu____2418 =
                                   FStar_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname in
                                 ((x.ifv), uu____2418)) ifams in
                          iface_of_type_names uu____2404 in
                        iface_union uu____2403
                          (iface_of_bindings (FStar_List.flatten td)) in
                      (env2, uu____2402)))
      | uu____2423 -> failwith "Unexpected signature element"
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.univ_name Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
                Prims.list))
  =
  fun g ->
    fun lid ->
      fun quals ->
        fun attrs ->
          fun univs ->
            fun t ->
              let uu____2496 =
                let uu____2497 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2501 ->
                          match uu___6_2501 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu____2502 -> false)) in
                Prims.op_Negation uu____2497 in
              if uu____2496
              then (g, empty_iface, [])
              else
                (let uu____2514 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2514 with
                 | (bs, uu____2530) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let lb =
                       let uu____2537 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2537;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       } in
                     extract_typ_abbrev g quals attrs lb)
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun ed ->
      let extend_iface lid mlp exp exp_binding =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let lb =
          {
            FStar_Extraction_ML_Syntax.mllb_name =
              (FStar_Pervasives_Native.snd mlp);
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.None;
            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
            FStar_Extraction_ML_Syntax.mllb_def = exp;
            FStar_Extraction_ML_Syntax.mllb_meta = [];
            FStar_Extraction_ML_Syntax.print_typ = false
          } in
        ((iface_of_bindings [(fv, exp_binding)]),
          (FStar_Extraction_ML_Syntax.MLM_Let
             (FStar_Extraction_ML_Syntax.NonRec, [lb]))) in
      let rec extract_fv tm =
        (let uu____2632 =
           let uu____2633 =
             let uu____2638 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_Env.debug uu____2638 in
           FStar_All.pipe_left uu____2633
             (FStar_Options.Other "ExtractionReify") in
         if uu____2632
         then
           let uu____2639 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2639
         else ());
        (let uu____2641 =
           let uu____2642 = FStar_Syntax_Subst.compress tm in
           uu____2642.FStar_Syntax_Syntax.n in
         match uu____2641 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2650) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             let uu____2657 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
             (match uu____2657 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2662;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2663;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;_} ->
                  let uu____2665 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                  (uu____2665, tysc))
         | uu____2666 ->
             let uu____2667 =
               let uu____2668 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos in
               let uu____2669 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2668 uu____2669 in
             failwith uu____2667) in
      let extract_action g1 a =
        (let uu____2695 =
           let uu____2696 =
             let uu____2701 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
             FStar_TypeChecker_Env.debug uu____2701 in
           FStar_All.pipe_left uu____2696
             (FStar_Options.Other "ExtractionReify") in
         if uu____2695
         then
           let uu____2702 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ in
           let uu____2703 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2702
             uu____2703
         else ());
        (let lbname =
           let uu____2710 =
             FStar_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
               FStar_Syntax_Syntax.tun in
           FStar_Util.Inl uu____2710 in
         let lb =
           FStar_Syntax_Syntax.mk_lb
             (lbname, (a.FStar_Syntax_Syntax.action_univs),
               FStar_Parser_Const.effect_Tot_lid,
               (a.FStar_Syntax_Syntax.action_typ),
               (a.FStar_Syntax_Syntax.action_defn), [],
               ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos)) in
         let lbs = (false, [lb]) in
         let action_lb =
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_let
                (lbs, FStar_Syntax_Util.exp_false_bool))
             (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
         let uu____2736 =
           FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
         match uu____2736 with
         | (a_let, uu____2752, ty) ->
             let uu____2754 =
               match a_let.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Let
                   ((uu____2775, mllb::[]), uu____2777) ->
                   (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStar_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None ->
                        failwith "No type scheme")
               | uu____2813 -> failwith "Impossible" in
             (match uu____2754 with
              | (exp, tysc) ->
                  let uu____2846 =
                    FStar_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc in
                  (match uu____2846 with
                   | (a_nm, a_lid, exp_b, g2) ->
                       ((let uu____2868 =
                           let uu____2869 =
                             let uu____2874 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu____2874 in
                           FStar_All.pipe_left uu____2869
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2868
                         then
                           let uu____2875 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2875
                         else ());
                        (let uu____2878 =
                           let uu____2879 =
                             let uu____2884 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu____2884 in
                           FStar_All.pipe_left uu____2879
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2878
                         then
                           ((let uu____2886 =
                               FStar_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc) in
                             FStar_Util.print1 "Extracted action type: %s\n"
                               uu____2886);
                            FStar_List.iter
                              (fun x ->
                                 FStar_Util.print1 "and binders: %s\n" x)
                              (FStar_Pervasives_Native.fst tysc))
                         else ());
                        (let uu____2894 = extend_iface a_lid a_nm exp exp_b in
                         match uu____2894 with
                         | (iface1, impl) -> (g2, (iface1, impl))))))) in
      let uu____2913 =
        let uu____2920 =
          let uu____2925 =
            let uu____2928 =
              let uu____2937 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
              FStar_All.pipe_right uu____2937 FStar_Util.must in
            FStar_All.pipe_right uu____2928 FStar_Pervasives_Native.snd in
          extract_fv uu____2925 in
        match uu____2920 with
        | (return_tm, ty_sc) ->
            let uu____3006 =
              FStar_Extraction_ML_UEnv.extend_with_monad_op_name g ed
                "return" ty_sc in
            (match uu____3006 with
             | (return_nm, return_lid, return_b, g1) ->
                 let uu____3025 =
                   extend_iface return_lid return_nm return_tm return_b in
                 (match uu____3025 with
                  | (iface1, impl) -> (g1, iface1, impl))) in
      match uu____2913 with
      | (g1, return_iface, return_decl) ->
          let uu____3049 =
            let uu____3056 =
              let uu____3061 =
                let uu____3064 =
                  let uu____3073 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                  FStar_All.pipe_right uu____3073 FStar_Util.must in
                FStar_All.pipe_right uu____3064 FStar_Pervasives_Native.snd in
              extract_fv uu____3061 in
            match uu____3056 with
            | (bind_tm, ty_sc) ->
                let uu____3142 =
                  FStar_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
                    "bind" ty_sc in
                (match uu____3142 with
                 | (bind_nm, bind_lid, bind_b, g2) ->
                     let uu____3161 =
                       extend_iface bind_lid bind_nm bind_tm bind_b in
                     (match uu____3161 with
                      | (iface1, impl) -> (g2, iface1, impl))) in
          (match uu____3049 with
           | (g2, bind_iface, bind_decl) ->
               let uu____3185 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions in
               (match uu____3185 with
                | (g3, actions) ->
                    let uu____3222 = FStar_List.unzip actions in
                    (match uu____3222 with
                     | (actions_iface, actions1) ->
                         let uu____3249 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface) in
                         (g3, uu____3249, (return_decl :: bind_decl ::
                           actions1)))))
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se ->
    fun env ->
      fun lbs ->
        let uu____3279 =
          FStar_Util.for_some
            (fun lb ->
               let uu____3283 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp in
               Prims.op_Negation uu____3283) lbs in
        if uu____3279
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3301 =
             FStar_List.fold_left
               (fun uu____3336 ->
                  fun lb ->
                    match uu____3336 with
                    | (env1, iface_opt, impls) ->
                        let uu____3377 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb in
                        (match uu____3377 with
                         | (env2, iface1, impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3411 = iface_union iface' iface1 in
                                   FStar_Pervasives_Native.Some uu____3411 in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs in
           match uu____3301 with
           | (env1, iface_opt, impls) ->
               let uu____3451 = FStar_Option.get iface_opt in
               let uu____3452 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten in
               (env1, uu____3451, uu____3452))
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3483 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3492 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3509 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3527 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs t in
          (match uu____3527 with | (env, iface1, uu____3542) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____3548) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3555 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb in
          (match uu____3555 with | (env, iface1, uu____3570) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____3576) when
          FStar_Util.for_some
            (fun lb ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3587 = extract_let_rec_types se g lbs in
          (match uu____3587 with | (env, iface1, uu____3602) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____3613 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3617 =
                 let uu____3618 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3618
                   t in
               Prims.op_Negation uu____3617) in
          if uu____3613
          then
            let uu____3623 =
              let uu____3634 =
                let uu____3635 =
                  let uu____3638 = always_fail lid t in [uu____3638] in
                (false, uu____3635) in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3634 in
            (match uu____3623 with
             | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____3661) ->
          let uu____3666 = FStar_Extraction_ML_Term.extract_lb_iface g lbs in
          (match uu____3666 with
           | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_assume uu____3695 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3702 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3703 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3716 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3727 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3738 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3749 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3765 =
            (let uu____3768 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_Env.is_reifiable_effect uu____3768
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders) in
          if uu____3765
          then
            let uu____3779 = extract_reifiable_effect g ed in
            (match uu____3779 with
             | (env, iface1, uu____3794) -> (env, iface1))
          else (g, empty_iface)
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____3814 = FStar_Options.interactive () in
      if uu____3814
      then (g, empty_iface)
      else
        (let uu____3820 = FStar_Options.restore_cmd_line_options true in
         let decls = modul.FStar_Syntax_Syntax.declarations in
         let iface1 =
           let uu___649_3823 = empty_iface in
           let uu____3824 = FStar_Extraction_ML_UEnv.current_module_of_uenv g in
           {
             iface_module_name = uu____3824;
             iface_bindings = (uu___649_3823.iface_bindings);
             iface_tydefs = (uu___649_3823.iface_tydefs);
             iface_type_names = (uu___649_3823.iface_type_names)
           } in
         let res =
           FStar_List.fold_left
             (fun uu____3842 ->
                fun se ->
                  match uu____3842 with
                  | (g1, iface2) ->
                      let uu____3854 = extract_sigelt_iface g1 se in
                      (match uu____3854 with
                       | (g2, iface') ->
                           let uu____3865 = iface_union iface2 iface' in
                           (g2, uu____3865))) (g, iface1) decls in
         (let uu____3867 = FStar_Options.restore_cmd_line_options true in
          FStar_All.pipe_left (fun uu____3868 -> ()) uu____3867);
         res)
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____3883 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____3895 ->
             let uu____3896 = FStar_Options.debug_any () in
             if uu____3896
             then
               let uu____3901 =
                 let uu____3902 =
                   FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                 FStar_Util.format1 "Extracted interface of %s" uu____3902 in
               FStar_Util.measure_execution_time uu____3901
                 (fun uu____3908 -> extract_iface' g modul)
             else extract_iface' g modul) in
      match uu____3883 with
      | (g1, iface1) ->
          let uu____3916 = FStar_Extraction_ML_UEnv.exit_module g1 in
          (uu____3916, iface1)
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____3987 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____3987 in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.ForExtraction] in
        let names =
          let uu____3994 =
            let uu____3995 =
              let uu____3998 =
                let uu____3999 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams in
                FStar_TypeChecker_Normalize.normalize steps uu____3999
                  ctor.dtyp in
              FStar_Syntax_Subst.compress uu____3998 in
            uu____3995.FStar_Syntax_Syntax.n in
          match uu____3994 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4003) ->
              FStar_List.map
                (fun uu____4035 ->
                   match uu____4035 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4043;
                        FStar_Syntax_Syntax.sort = uu____4044;_},
                      uu____4045) -> FStar_Ident.string_of_id ppname) bs
          | uu____4052 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____4059 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu____4059 with
        | (env2, mls, uu____4082) ->
            let uu____4083 =
              let uu____4094 =
                let uu____4101 = FStar_Extraction_ML_Util.argTypes mlt in
                FStar_List.zip names uu____4101 in
              (mls, uu____4094) in
            (env2, uu____4083) in
      let extract_one_family env1 ind =
        let uu____4153 = binders_as_mlty_binders env1 ind.iparams in
        match uu____4153 with
        | (env_iparams, vars) ->
            let uu____4190 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____4190 with
             | (env2, ctors) ->
                 let uu____4283 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____4283 with
                  | (indices, uu____4313) ->
                      let ml_params =
                        let uu____4321 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____4344 ->
                                    let uu____4351 =
                                      FStar_Util.string_of_int i in
                                    Prims.op_Hat "'dummyV" uu____4351)) in
                        FStar_List.append vars uu____4321 in
                      let uu____4352 =
                        let uu____4359 =
                          FStar_Util.find_opt
                            (fun uu___7_4364 ->
                               match uu___7_4364 with
                               | FStar_Syntax_Syntax.RecordType uu____4365 ->
                                   true
                               | uu____4374 -> false) ind.iquals in
                        match uu____4359 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu____4391 = FStar_List.hd ctors in
                            (match uu____4391 with
                             | (uu____4418, c_ty) ->
                                 let uu____4433 =
                                   FStar_List.fold_right2
                                     (fun id ->
                                        fun uu____4469 ->
                                          fun uu____4470 ->
                                            match (uu____4469, uu____4470)
                                            with
                                            | ((uu____4509, ty), (fields, g))
                                                ->
                                                let uu____4539 =
                                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id) in
                                                (match uu____4539 with
                                                 | (mlid, g1) ->
                                                     (((mlid, ty) :: fields),
                                                       g1))) ids c_ty
                                     ([], env2) in
                                 (match uu____4433 with
                                  | (fields, g) ->
                                      ((FStar_Pervasives_Native.Some
                                          (FStar_Extraction_ML_Syntax.MLTD_Record
                                             fields)), g)))
                        | uu____4598 when
                            (FStar_List.length ctors) = Prims.int_zero ->
                            (FStar_Pervasives_Native.None, env2)
                        | uu____4613 ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Extraction_ML_Syntax.MLTD_DType ctors)),
                              env2) in
                      (match uu____4352 with
                       | (tbody, env3) ->
                           let uu____4646 =
                             let uu____4665 =
                               let uu____4666 =
                                 FStar_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname in
                               FStar_Pervasives_Native.snd uu____4666 in
                             (false, uu____4665,
                               FStar_Pervasives_Native.None, ml_params,
                               (ind.imetadata), tbody) in
                           (env3, uu____4646)))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____4708, t, uu____4710, uu____4711, uu____4712);
            FStar_Syntax_Syntax.sigrng = uu____4713;
            FStar_Syntax_Syntax.sigquals = uu____4714;
            FStar_Syntax_Syntax.sigmeta = uu____4715;
            FStar_Syntax_Syntax.sigattrs = uu____4716;
            FStar_Syntax_Syntax.sigopts = uu____4717;_}::[],
          uu____4718),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____4737 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____4737 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____4783), quals) ->
          let uu____4797 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu____4797
          then (env, [])
          else
            (let uu____4807 = bundle_as_inductive_families env ses quals in
             match uu____4807 with
             | (env1, ifams) ->
                 let uu____4826 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu____4826 with
                  | (env2, td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4919 -> failwith "Unexpected signature element"
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t ->
             let uu____4973 = FStar_Syntax_Util.head_and_args t in
             match uu____4973 with
             | (head, args) ->
                 let uu____5020 =
                   let uu____5021 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head in
                   Prims.op_Negation uu____5021 in
                 if uu____5020
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s, uu____5034));
                         FStar_Syntax_Syntax.pos = uu____5035;
                         FStar_Syntax_Syntax.vars = uu____5036;_},
                       uu____5037)::[] ->
                        let uu____5074 =
                          let uu____5077 = FStar_Util.int_of_string s in
                          FStar_Pervasives_Native.Some uu____5077 in
                        FStar_Pervasives_Native.Some uu____5074
                    | uu____5080 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None)) in
      let uu____5093 =
        let uu____5094 = FStar_Options.codegen () in
        uu____5094 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin) in
      if uu____5093
      then []
      else
        (let uu____5102 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs in
         match uu____5102 with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                    let fv_lid =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
                    let ml_name_str =
                      let uu____5140 =
                        let uu____5141 = FStar_Ident.string_of_lid fv_lid in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5141 in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5140 in
                    let uu____5142 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str in
                    match uu____5142 with
                    | FStar_Pervasives_Native.Some
                        (interp, nbe_interp, arity, plugin) ->
                        let uu____5167 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp]) in
                        (match uu____5167 with
                         | (register, args) ->
                             let h =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register) in
                             let arity1 =
                               let uu____5199 =
                                 let uu____5200 =
                                   let uu____5211 =
                                     FStar_Util.string_of_int arity in
                                   (uu____5211, FStar_Pervasives_Native.None) in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5200 in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5199 in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args))) in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None -> [] in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____5235 -> []))
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun se ->
      let uu____5258 =
        let uu____5259 = FStar_Syntax_Print.sigelt_to_string_short se in
        FStar_Util.format1 "While extracting top-level definition `%s`"
          uu____5259 in
      FStar_Errors.with_ctx uu____5258
        (fun uu____5269 ->
           FStar_Extraction_ML_UEnv.debug g
             (fun u ->
                let uu____5274 = FStar_Syntax_Print.sigelt_to_string_short se in
                FStar_Util.print1 ">>>> extract_sig %s \n" uu____5274);
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_bundle uu____5281 ->
                extract_bundle g se
            | FStar_Syntax_Syntax.Sig_inductive_typ uu____5290 ->
                extract_bundle g se
            | FStar_Syntax_Syntax.Sig_datacon uu____5307 ->
                extract_bundle g se
            | FStar_Syntax_Syntax.Sig_new_effect ed when
                let uu____5323 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                FStar_TypeChecker_Env.is_reifiable_effect uu____5323
                  ed.FStar_Syntax_Syntax.mname
                ->
                let uu____5324 = extract_reifiable_effect g ed in
                (match uu____5324 with | (env, _iface, impl) -> (env, impl))
            | FStar_Syntax_Syntax.Sig_splice uu____5348 ->
                failwith "impossible: trying to extract splice"
            | FStar_Syntax_Syntax.Sig_fail uu____5361 ->
                failwith "impossible: trying to extract Sig_fail"
            | FStar_Syntax_Syntax.Sig_new_effect uu____5378 -> (g, [])
            | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
                FStar_Extraction_ML_Term.is_arity g t ->
                let uu____5384 =
                  extract_type_declaration g lid
                    se.FStar_Syntax_Syntax.sigquals
                    se.FStar_Syntax_Syntax.sigattrs univs t in
                (match uu____5384 with
                 | (env, uu____5400, impl) -> (env, impl))
            | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____5409) when
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp
                ->
                let uu____5416 =
                  extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
                    se.FStar_Syntax_Syntax.sigattrs lb in
                (match uu____5416 with
                 | (env, uu____5432, impl) -> (env, impl))
            | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____5441) when
                FStar_Util.for_some
                  (fun lb ->
                     FStar_Extraction_ML_Term.is_arity g
                       lb.FStar_Syntax_Syntax.lbtyp) lbs
                ->
                let uu____5452 = extract_let_rec_types se g lbs in
                (match uu____5452 with
                 | (env, uu____5468, impl) -> (env, impl))
            | FStar_Syntax_Syntax.Sig_let (lbs, uu____5477) ->
                let attrs = se.FStar_Syntax_Syntax.sigattrs in
                let quals = se.FStar_Syntax_Syntax.sigquals in
                let uu____5488 =
                  let uu____5497 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_extr_with attrs in
                  match uu____5497 with
                  | FStar_Pervasives_Native.None ->
                      (attrs, FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats, (tau, FStar_Pervasives_Native.None)::uu____5526)
                      -> (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats, args) ->
                      (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_for_extraction_with`");
                       (attrs, FStar_Pervasives_Native.None)) in
                (match uu____5488 with
                 | (attrs1, post_tau) ->
                     let postprocess_lb tau lb =
                       let lbdef =
                         let uu____5610 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                         FStar_TypeChecker_Env.postprocess uu____5610 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef in
                       let uu___912_5611 = lb in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___912_5611.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___912_5611.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___912_5611.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___912_5611.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___912_5611.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___912_5611.FStar_Syntax_Syntax.lbpos)
                       } in
                     let lbs1 =
                       let uu____5619 =
                         match post_tau with
                         | FStar_Pervasives_Native.Some tau ->
                             FStar_List.map (postprocess_lb tau)
                               (FStar_Pervasives_Native.snd lbs)
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.snd lbs in
                       ((FStar_Pervasives_Native.fst lbs), uu____5619) in
                     let uu____5633 =
                       let uu____5640 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_let
                              (lbs1, FStar_Syntax_Util.exp_false_bool))
                           se.FStar_Syntax_Syntax.sigrng in
                       FStar_Extraction_ML_Term.term_as_mlexpr g uu____5640 in
                     (match uu____5633 with
                      | (ml_let, uu____5656, uu____5657) ->
                          (match ml_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((flavor, bindings), uu____5666) ->
                               let flags =
                                 FStar_List.choose flag_of_qual quals in
                               let flags' = extract_metadata attrs1 in
                               let uu____5683 =
                                 FStar_List.fold_left2
                                   (fun uu____5709 ->
                                      fun ml_lb ->
                                        fun uu____5711 ->
                                          match (uu____5709, uu____5711) with
                                          | ((env, ml_lbs),
                                             {
                                               FStar_Syntax_Syntax.lbname =
                                                 lbname;
                                               FStar_Syntax_Syntax.lbunivs =
                                                 uu____5733;
                                               FStar_Syntax_Syntax.lbtyp = t;
                                               FStar_Syntax_Syntax.lbeff =
                                                 uu____5735;
                                               FStar_Syntax_Syntax.lbdef =
                                                 uu____5736;
                                               FStar_Syntax_Syntax.lbattrs =
                                                 uu____5737;
                                               FStar_Syntax_Syntax.lbpos =
                                                 uu____5738;_})
                                              ->
                                              let uu____5763 =
                                                FStar_All.pipe_right
                                                  ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                                  (FStar_List.contains
                                                     FStar_Extraction_ML_Syntax.Erased) in
                                              if uu____5763
                                              then (env, ml_lbs)
                                              else
                                                (let lb_lid =
                                                   let uu____5776 =
                                                     let uu____5779 =
                                                       FStar_Util.right
                                                         lbname in
                                                     uu____5779.FStar_Syntax_Syntax.fv_name in
                                                   uu____5776.FStar_Syntax_Syntax.v in
                                                 let flags'' =
                                                   let uu____5783 =
                                                     let uu____5784 =
                                                       FStar_Syntax_Subst.compress
                                                         t in
                                                     uu____5784.FStar_Syntax_Syntax.n in
                                                   match uu____5783 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu____5789,
                                                        {
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Comp
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____5790;
                                                              FStar_Syntax_Syntax.effect_name
                                                                = e;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = uu____5792;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____5793;
                                                              FStar_Syntax_Syntax.flags
                                                                = uu____5794;_};
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____5795;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____5796;_})
                                                       when
                                                       let uu____5831 =
                                                         FStar_Ident.string_of_lid
                                                           e in
                                                       uu____5831 =
                                                         "FStar.HyperStack.ST.StackInline"
                                                       ->
                                                       [FStar_Extraction_ML_Syntax.StackInline]
                                                   | uu____5832 -> [] in
                                                 let meta =
                                                   FStar_List.append flags
                                                     (FStar_List.append
                                                        flags' flags'') in
                                                 let ml_lb1 =
                                                   let uu___960_5837 = ml_lb in
                                                   {
                                                     FStar_Extraction_ML_Syntax.mllb_name
                                                       =
                                                       (uu___960_5837.FStar_Extraction_ML_Syntax.mllb_name);
                                                     FStar_Extraction_ML_Syntax.mllb_tysc
                                                       =
                                                       (uu___960_5837.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                     FStar_Extraction_ML_Syntax.mllb_add_unit
                                                       =
                                                       (uu___960_5837.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                     FStar_Extraction_ML_Syntax.mllb_def
                                                       =
                                                       (uu___960_5837.FStar_Extraction_ML_Syntax.mllb_def);
                                                     FStar_Extraction_ML_Syntax.mllb_meta
                                                       = meta;
                                                     FStar_Extraction_ML_Syntax.print_typ
                                                       =
                                                       (uu___960_5837.FStar_Extraction_ML_Syntax.print_typ)
                                                   } in
                                                 let uu____5838 =
                                                   let uu____5843 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_Util.for_some
                                                          (fun uu___8_5848 ->
                                                             match uu___8_5848
                                                             with
                                                             | FStar_Syntax_Syntax.Projector
                                                                 uu____5849
                                                                 -> true
                                                             | uu____5854 ->
                                                                 false)) in
                                                   if uu____5843
                                                   then
                                                     let uu____5859 =
                                                       let uu____5866 =
                                                         FStar_Util.right
                                                           lbname in
                                                       let uu____5867 =
                                                         FStar_Util.must
                                                           ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                       FStar_Extraction_ML_UEnv.extend_fv
                                                         env uu____5866
                                                         uu____5867
                                                         ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                     match uu____5859 with
                                                     | (env1, mls,
                                                        uu____5874) ->
                                                         (env1,
                                                           (let uu___972_5876
                                                              = ml_lb1 in
                                                            {
                                                              FStar_Extraction_ML_Syntax.mllb_name
                                                                = mls;
                                                              FStar_Extraction_ML_Syntax.mllb_tysc
                                                                =
                                                                (uu___972_5876.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                              FStar_Extraction_ML_Syntax.mllb_add_unit
                                                                =
                                                                (uu___972_5876.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                              FStar_Extraction_ML_Syntax.mllb_def
                                                                =
                                                                (uu___972_5876.FStar_Extraction_ML_Syntax.mllb_def);
                                                              FStar_Extraction_ML_Syntax.mllb_meta
                                                                =
                                                                (uu___972_5876.FStar_Extraction_ML_Syntax.mllb_meta);
                                                              FStar_Extraction_ML_Syntax.print_typ
                                                                =
                                                                (uu___972_5876.FStar_Extraction_ML_Syntax.print_typ)
                                                            }))
                                                   else
                                                     (let uu____5878 =
                                                        let uu____5885 =
                                                          FStar_Util.must
                                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                        FStar_Extraction_ML_UEnv.extend_lb
                                                          env lbname t
                                                          uu____5885
                                                          ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                      match uu____5878 with
                                                      | (env1, uu____5891,
                                                         uu____5892) ->
                                                          (env1, ml_lb1)) in
                                                 match uu____5838 with
                                                 | (g1, ml_lb2) ->
                                                     (g1, (ml_lb2 :: ml_lbs))))
                                   (g, []) bindings
                                   (FStar_Pervasives_Native.snd lbs1) in
                               (match uu____5683 with
                                | (g1, ml_lbs') ->
                                    let uu____5919 =
                                      let uu____5922 =
                                        let uu____5925 =
                                          let uu____5926 =
                                            FStar_Extraction_ML_Util.mlloc_of_range
                                              se.FStar_Syntax_Syntax.sigrng in
                                          FStar_Extraction_ML_Syntax.MLM_Loc
                                            uu____5926 in
                                        [uu____5925;
                                        FStar_Extraction_ML_Syntax.MLM_Let
                                          (flavor, (FStar_List.rev ml_lbs'))] in
                                      let uu____5929 =
                                        maybe_register_plugin g1 se in
                                      FStar_List.append uu____5922 uu____5929 in
                                    (g1, uu____5919))
                           | uu____5934 ->
                               let uu____5935 =
                                 let uu____5936 =
                                   let uu____5937 =
                                     FStar_Extraction_ML_UEnv.current_module_of_uenv
                                       g in
                                   FStar_Extraction_ML_Code.string_of_mlexpr
                                     uu____5937 ml_let in
                                 FStar_Util.format1
                                   "Impossible: Translated a let to a non-let: %s"
                                   uu____5936 in
                               failwith uu____5935)))
            | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5945, t) ->
                let quals = se.FStar_Syntax_Syntax.sigquals in
                let uu____5950 =
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                    &&
                    (let uu____5954 =
                       let uu____5955 =
                         FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                       FStar_TypeChecker_Util.must_erase_for_extraction
                         uu____5955 t in
                     Prims.op_Negation uu____5954) in
                if uu____5950
                then
                  let always_fail1 =
                    let uu___992_5963 = se in
                    let uu____5964 =
                      let uu____5965 =
                        let uu____5972 =
                          let uu____5973 =
                            let uu____5976 = always_fail lid t in
                            [uu____5976] in
                          (false, uu____5973) in
                        (uu____5972, []) in
                      FStar_Syntax_Syntax.Sig_let uu____5965 in
                    {
                      FStar_Syntax_Syntax.sigel = uu____5964;
                      FStar_Syntax_Syntax.sigrng =
                        (uu___992_5963.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___992_5963.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___992_5963.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___992_5963.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___992_5963.FStar_Syntax_Syntax.sigopts)
                    } in
                  let uu____5981 = extract_sig g always_fail1 in
                  (match uu____5981 with
                   | (g1, mlm) ->
                       let uu____6000 =
                         FStar_Util.find_map quals
                           (fun uu___9_6005 ->
                              match uu___9_6005 with
                              | FStar_Syntax_Syntax.Discriminator l ->
                                  FStar_Pervasives_Native.Some l
                              | uu____6009 -> FStar_Pervasives_Native.None) in
                       (match uu____6000 with
                        | FStar_Pervasives_Native.Some l ->
                            let uu____6017 =
                              let uu____6020 =
                                let uu____6021 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____6021 in
                              let uu____6022 =
                                let uu____6025 =
                                  FStar_Extraction_ML_Term.ind_discriminator_body
                                    g1 lid l in
                                [uu____6025] in
                              uu____6020 :: uu____6022 in
                            (g1, uu____6017)
                        | uu____6028 ->
                            let uu____6031 =
                              FStar_Util.find_map quals
                                (fun uu___10_6037 ->
                                   match uu___10_6037 with
                                   | FStar_Syntax_Syntax.Projector
                                       (l, uu____6041) ->
                                       FStar_Pervasives_Native.Some l
                                   | uu____6042 ->
                                       FStar_Pervasives_Native.None) in
                            (match uu____6031 with
                             | FStar_Pervasives_Native.Some uu____6049 ->
                                 (g1, [])
                             | uu____6052 -> (g1, mlm))))
                else (g, [])
            | FStar_Syntax_Syntax.Sig_assume uu____6060 -> (g, [])
            | FStar_Syntax_Syntax.Sig_sub_effect uu____6069 -> (g, [])
            | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6072 -> (g, [])
            | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6087 -> (g, [])
            | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____6100 ->
                (g, [])
            | FStar_Syntax_Syntax.Sig_pragma p ->
                (FStar_Syntax_Util.process_pragma p
                   se.FStar_Syntax_Syntax.sigrng;
                 (g, []))))
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      let uu____6137 = FStar_Options.restore_cmd_line_options true in
      let uu____6138 =
        FStar_Extraction_ML_UEnv.extend_with_module_name g
          m.FStar_Syntax_Syntax.name in
      match uu____6138 with
      | (name, g1) ->
          let g2 =
            let uu____6152 =
              let uu____6153 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
              FStar_TypeChecker_Env.set_current_module uu____6153
                m.FStar_Syntax_Syntax.name in
            FStar_Extraction_ML_UEnv.set_tcenv g1 uu____6152 in
          let g3 = FStar_Extraction_ML_UEnv.set_current_module g2 name in
          let uu____6155 =
            FStar_Util.fold_map
              (fun g4 ->
                 fun se ->
                   let uu____6174 =
                     let uu____6175 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Options.debug_module uu____6175 in
                   if uu____6174
                   then
                     let nm =
                       let uu____6183 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lids_of_sigelt se)
                           (FStar_List.map FStar_Ident.string_of_lid) in
                       FStar_All.pipe_right uu____6183
                         (FStar_String.concat ", ") in
                     (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                      (let uu____6193 =
                         FStar_Util.format1 "---Extracted {%s}" nm in
                       FStar_Util.measure_execution_time uu____6193
                         (fun uu____6201 -> extract_sig g4 se)))
                   else extract_sig g4 se) g3
              m.FStar_Syntax_Syntax.declarations in
          (match uu____6155 with
           | (g4, sigs) ->
               let mlm = FStar_List.flatten sigs in
               let is_kremlin =
                 let uu____6221 = FStar_Options.codegen () in
                 uu____6221 =
                   (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
               let uu____6226 =
                 (let uu____6229 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  uu____6229 <> "Prims") &&
                   (is_kremlin ||
                      (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)) in
               if uu____6226
               then
                 ((let uu____6237 =
                     let uu____6238 = FStar_Options.silent () in
                     Prims.op_Negation uu____6238 in
                   if uu____6237
                   then
                     let uu____6239 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Util.print1 "Extracted module %s\n" uu____6239
                   else ());
                  (g4,
                    (FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLLib
                          [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                             (FStar_Extraction_ML_Syntax.MLLib []))]))))
               else (g4, FStar_Pervasives_Native.None))
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      (let uu____6309 = FStar_Options.restore_cmd_line_options true in
       FStar_All.pipe_left (fun uu____6310 -> ()) uu____6309);
      (let uu____6312 =
         let uu____6313 =
           let uu____6314 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.should_extract uu____6314 in
         Prims.op_Negation uu____6313 in
       if uu____6312
       then
         let uu____6315 =
           let uu____6316 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6316 in
         failwith uu____6315
       else ());
      (let uu____6318 = FStar_Options.interactive () in
       if uu____6318
       then (g, FStar_Pervasives_Native.None)
       else
         (let nm = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          let uu____6329 =
            FStar_Syntax_Unionfind.with_uf_enabled
              (fun uu____6343 ->
                 FStar_Errors.with_ctx
                   (Prims.op_Hat "While extracting module " nm)
                   (fun uu____6353 ->
                      let uu____6354 = FStar_Options.debug_any () in
                      if uu____6354
                      then
                        let msg =
                          FStar_Util.format1 "Extracting module %s" nm in
                        FStar_Util.measure_execution_time msg
                          (fun uu____6369 -> extract' g m)
                      else extract' g m)) in
          match uu____6329 with
          | (g1, mllib) ->
              ((let uu____6384 = FStar_Options.restore_cmd_line_options true in
                FStar_All.pipe_left (fun uu____6385 -> ()) uu____6384);
               (let uu____6386 = FStar_Extraction_ML_UEnv.exit_module g1 in
                (uu____6386, mllib)))))