open Prims
type norm_cb =
  (FStar_Ident.lid, FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_16 ->
    match uu___0_16 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____23 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____23
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Embedding_failure -> true | uu____29 -> false
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembedding_failure -> true | uu____35 -> false
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s -> fun f -> FStar_Util.map_opt s (FStar_Thunk.map f)
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s -> FStar_Util.map_opt s FStar_Thunk.force
type embed_t =
  FStar_Range.range -> shadow_term -> norm_cb -> FStar_Syntax_Syntax.term
type 'a unembed_t =
  Prims.bool -> norm_cb -> 'a FStar_Pervasives_Native.option
type 'a raw_embedder = 'a -> embed_t
type 'a raw_unembedder = FStar_Syntax_Syntax.term -> 'a unembed_t
type 'a printer = 'a -> Prims.string
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ ;
  print: 'a printer ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> un
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> typ
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> print
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> emb_typ
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e -> e.emb_typ
let unknown_printer :
  'uuuuuu397 . FStar_Syntax_Syntax.term -> 'uuuuuu397 -> Prims.string =
  fun typ ->
    fun uu____407 ->
      let uu____408 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu____408
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu____414 =
      let uu____415 = FStar_Syntax_Subst.compress t in
      uu____415.FStar_Syntax_Syntax.n in
    match uu____414 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____419 ->
        let uu____420 =
          let uu____421 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____421 in
        failwith uu____420
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu____461 =
          let uu____462 =
            let uu____469 =
              let uu____470 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu____470 FStar_Ident.string_of_lid in
            (uu____469, []) in
          FStar_Syntax_Syntax.ET_app uu____462 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____461 }
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em ->
    fun un ->
      fun typ ->
        fun printer1 ->
          fun emb_typ -> { em; un; typ; print = printer1; emb_typ }
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e -> fun x -> e.em x
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e -> fun t -> e.un t
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____611 = unembed e t in uu____611 true n
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____650 = unembed e t in uu____650 false n
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___77_694 = e in
      {
        em = (uu___77_694.em);
        un = (uu___77_694.un);
        typ = ty;
        print = (uu___77_694.print);
        emb_typ = (uu___77_694.emb_typ)
      }
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) ->
          FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
            'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun o ->
          let uu____751 =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu____753 -> type_of ea in
          mk_emb_full (fun x -> let uu____759 = ba x in embed ea uu____759)
            (fun t ->
               fun w ->
                 fun cb ->
                   let uu____768 =
                     let uu____771 = unembed ea t in uu____771 w cb in
                   FStar_Util.map_opt uu____768 ab) uu____751
            (fun x ->
               let uu____781 = let uu____782 = ba x in ea.print uu____782 in
               FStar_Util.format1 "(embed_as>> %s)\n" uu____781) ea.emb_typ
let lazy_embed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.term
  =
  fun pa ->
    fun et ->
      fun rng ->
        fun ta ->
          fun x ->
            fun f ->
              (let uu____840 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____840
               then
                 let uu____847 = FStar_Syntax_Print.term_to_string ta in
                 let uu____848 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____849 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____847
                   uu____848 uu____849
               else ());
              (let uu____851 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____851
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  FStar_Syntax_Util.mk_lazy x FStar_Syntax_Syntax.tun
                    (FStar_Syntax_Syntax.Lazy_embedding (et, thunk))
                    (FStar_Pervasives_Native.Some rng)))
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa ->
    fun et ->
      fun x ->
        fun ta ->
          fun f ->
            let x1 = FStar_Syntax_Subst.compress x in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et', t);
                  FStar_Syntax_Syntax.ltyp = uu____931;
                  FStar_Syntax_Syntax.rng = uu____932;_}
                ->
                let uu____943 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____943
                then
                  let res =
                    let uu____955 = FStar_Thunk.force t in f uu____955 in
                  ((let uu____959 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____959
                    then
                      let uu____966 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____967 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____968 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____970 = pa x2 in
                            Prims.op_Hat "Some " uu____970 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____966 uu____967 uu____968
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu____975 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____975
                    then
                      let uu____982 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____983 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n" uu____982
                        uu____983
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____985 ->
                let aopt = f x1 in
                ((let uu____990 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____990
                  then
                    let uu____997 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____998 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____999 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1001 = pa a1 in
                          Prims.op_Hat "Some " uu____1001 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____997 uu____998 uu____999
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1034 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1034
       then
         let uu____1041 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1041
       else ());
      t in
    let un t _w _n =
      (let uu____1064 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1064
       then
         let uu____1071 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1071
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1118 =
    let uu____1119 =
      let uu____1126 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1126, []) in
    FStar_Syntax_Syntax.ET_app uu____1119 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1118
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1154 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___167_1154.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1154.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1180 ->
        (if w
         then
           (let uu____1182 =
              let uu____1187 =
                let uu____1188 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1188 in
              (FStar_Errors.Warning_NotEmbedded, uu____1187) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1182)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1190 =
    let uu____1191 =
      let uu____1198 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1198, []) in
    FStar_Syntax_Syntax.ET_app uu____1191 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1202 -> "()")
    uu____1190
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___187_1234 = t in
    {
      FStar_Syntax_Syntax.n = (uu___187_1234.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1234.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1263 ->
        (if w
         then
           (let uu____1265 =
              let uu____1270 =
                let uu____1271 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1271 in
              (FStar_Errors.Warning_NotEmbedded, uu____1270) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1265)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1273 =
    let uu____1274 =
      let uu____1281 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1281, []) in
    FStar_Syntax_Syntax.ET_app uu____1274 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1273
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___206_1310 = t in
    {
      FStar_Syntax_Syntax.n = (uu___206_1310.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1310.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1337 ->
        (if w
         then
           (let uu____1339 =
              let uu____1344 =
                let uu____1345 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1345 in
              (FStar_Errors.Warning_NotEmbedded, uu____1344) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1339)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1347 =
    let uu____1348 =
      let uu____1355 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1355, []) in
    FStar_Syntax_Syntax.ET_app uu____1348 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1347
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1362 =
      let uu____1369 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1369, []) in
    FStar_Syntax_Syntax.ET_app uu____1362 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1397 ->
         let uu____1398 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1398) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1430)) ->
             let uu____1443 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1443
         | uu____1444 ->
             (if w
              then
                (let uu____1446 =
                   let uu____1451 =
                     let uu____1452 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1452 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1451) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1446)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1457 =
      let uu____1464 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1464, []) in
    FStar_Syntax_Syntax.ET_app uu____1457 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1516)) -> FStar_Pervasives_Native.Some s
    | uu____1517 ->
        (if w
         then
           (let uu____1519 =
              let uu____1524 =
                let uu____1525 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1525 in
              (FStar_Errors.Warning_NotEmbedded, uu____1524) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1519)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1549 =
        let uu____1550 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1550] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1549 FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1576 =
        let uu____1583 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1583, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1576 in
    let printer1 uu___1_1593 =
      match uu___1_1593 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1597 =
            let uu____1598 = ea.print x in Prims.op_Hat uu____1598 ")" in
          Prims.op_Hat "(Some " uu____1597 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____1631 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____1632 =
                 let uu____1633 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1633
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1634 =
                 let uu____1635 =
                   let uu____1644 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1644 in
                 [uu____1635] in
               FStar_Syntax_Syntax.mk_Tm_app uu____1632 uu____1634 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu____1673 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____1673 in
                      let uu____1674 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu____1675 =
                        let uu____1676 =
                          let uu____1685 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu____1685 in
                        let uu____1686 =
                          let uu____1697 = FStar_Syntax_Syntax.as_arg t in
                          [uu____1697] in
                        uu____1676 :: uu____1686 in
                      FStar_Syntax_Syntax.mk_Tm_app uu____1674 uu____1675 rng) in
               let uu____1730 =
                 let uu____1731 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1731
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1732 =
                 let uu____1733 =
                   let uu____1742 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1742 in
                 let uu____1743 =
                   let uu____1754 =
                     let uu____1763 =
                       let uu____1764 = embed ea a1 in
                       uu____1764 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____1763 in
                   [uu____1754] in
                 uu____1733 :: uu____1743 in
               FStar_Syntax_Syntax.mk_Tm_app uu____1730 uu____1732 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____1832 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____1832 with
           | (hd, args) ->
               let uu____1873 =
                 let uu____1888 =
                   let uu____1889 = FStar_Syntax_Util.un_uinst hd in
                   uu____1889.FStar_Syntax_Syntax.n in
                 (uu____1888, args) in
               (match uu____1873 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1907) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____1931::(a1, uu____1933)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____1984 =
                      let uu____1987 = unembed ea a1 in uu____1987 w norm in
                    FStar_Util.bind_opt uu____1984
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____2000 ->
                    (if w
                     then
                       (let uu____2016 =
                          let uu____2021 =
                            let uu____2022 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2022 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2021) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2016)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2026 =
      let uu____2027 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2027 in
    mk_emb_full em un uu____2026 printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2066 =
          let uu____2067 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2076 =
            let uu____2087 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2087] in
          uu____2067 :: uu____2076 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2066
          FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2121 =
          let uu____2128 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2128, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2121 in
      let printer1 uu____2140 =
        match uu____2140 with
        | (x, y) ->
            let uu____2147 = ea.print x in
            let uu____2148 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2147 uu____2148 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2190 ->
             let proj i ab =
               let proj_1 =
                 let uu____2203 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu____2204 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2203
                   uu____2204 i in
               let proj_1_tm =
                 let uu____2206 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____2206 in
               let uu____2207 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2208 =
                 let uu____2209 =
                   let uu____2218 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2218 in
                 let uu____2219 =
                   let uu____2230 =
                     let uu____2239 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2239 in
                   let uu____2240 =
                     let uu____2251 = FStar_Syntax_Syntax.as_arg ab in
                     [uu____2251] in
                   uu____2230 :: uu____2240 in
                 uu____2209 :: uu____2219 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2207 uu____2208 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu____2294 =
               let uu____2295 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2295
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu____2296 =
               let uu____2297 =
                 let uu____2306 = type_of ea in
                 FStar_Syntax_Syntax.iarg uu____2306 in
               let uu____2307 =
                 let uu____2318 =
                   let uu____2327 = type_of eb in
                   FStar_Syntax_Syntax.iarg uu____2327 in
                 let uu____2328 =
                   let uu____2339 =
                     let uu____2348 =
                       let uu____2349 =
                         embed ea (FStar_Pervasives_Native.fst x) in
                       uu____2349 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2348 in
                   let uu____2356 =
                     let uu____2367 =
                       let uu____2376 =
                         let uu____2377 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu____2377 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu____2376 in
                     [uu____2367] in
                   uu____2339 :: uu____2356 in
                 uu____2318 :: uu____2328 in
               uu____2297 :: uu____2307 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2294 uu____2296 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2473 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2473 with
             | (hd, args) ->
                 let uu____2516 =
                   let uu____2529 =
                     let uu____2530 = FStar_Syntax_Util.un_uinst hd in
                     uu____2530.FStar_Syntax_Syntax.n in
                   (uu____2529, args) in
                 (match uu____2516 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2548::uu____2549::(a1, uu____2551)::(b1,
                                                                uu____2553)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2612 =
                        let uu____2615 = unembed ea a1 in uu____2615 w norm in
                      FStar_Util.bind_opt uu____2612
                        (fun a2 ->
                           let uu____2629 =
                             let uu____2632 = unembed eb b1 in
                             uu____2632 w norm in
                           FStar_Util.bind_opt uu____2629
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____2649 ->
                      (if w
                       then
                         (let uu____2663 =
                            let uu____2668 =
                              let uu____2669 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____2669 in
                            (FStar_Errors.Warning_NotEmbedded, uu____2668) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____2663)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____2675 =
        let uu____2676 = type_of ea in
        let uu____2677 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____2676 uu____2677 in
      mk_emb_full em un uu____2675 printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____2718 =
          let uu____2719 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2728 =
            let uu____2739 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2739] in
          uu____2719 :: uu____2728 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____2718
          FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____2773 =
          let uu____2780 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____2780, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2773 in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____2798 = ea.print a1 in
            FStar_Util.format1 "Inl %s" uu____2798
        | FStar_Util.Inr b1 ->
            let uu____2800 = eb.print b1 in
            FStar_Util.format1 "Inr %s" uu____2800 in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____2845 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu____2857 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____2857 in
                         let uu____2858 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____2859 =
                           let uu____2860 =
                             let uu____2869 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____2869 in
                           let uu____2870 =
                             let uu____2881 =
                               let uu____2890 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____2890 in
                             let uu____2891 =
                               let uu____2902 = FStar_Syntax_Syntax.as_arg t in
                               [uu____2902] in
                             uu____2881 :: uu____2891 in
                           uu____2860 :: uu____2870 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2858 uu____2859
                           rng) in
                  let uu____2943 =
                    let uu____2944 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____2944
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____2945 =
                    let uu____2946 =
                      let uu____2955 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____2955 in
                    let uu____2956 =
                      let uu____2967 =
                        let uu____2976 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____2976 in
                      let uu____2977 =
                        let uu____2988 =
                          let uu____2997 =
                            let uu____2998 = embed ea a1 in
                            uu____2998 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu____2997 in
                        [uu____2988] in
                      uu____2967 :: uu____2977 in
                    uu____2946 :: uu____2956 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____2943 uu____2945 rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3038 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu____3050 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3050 in
                         let uu____3051 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3052 =
                           let uu____3053 =
                             let uu____3062 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3062 in
                           let uu____3063 =
                             let uu____3074 =
                               let uu____3083 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3083 in
                             let uu____3084 =
                               let uu____3095 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3095] in
                             uu____3074 :: uu____3084 in
                           uu____3053 :: uu____3063 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3051 uu____3052
                           rng) in
                  let uu____3136 =
                    let uu____3137 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3137
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3138 =
                    let uu____3139 =
                      let uu____3148 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3148 in
                    let uu____3149 =
                      let uu____3160 =
                        let uu____3169 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3169 in
                      let uu____3170 =
                        let uu____3181 =
                          let uu____3190 =
                            let uu____3191 = embed eb b1 in
                            uu____3191 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu____3190 in
                        [uu____3181] in
                      uu____3160 :: uu____3170 in
                    uu____3139 :: uu____3149 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3136 uu____3138 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3277 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3277 with
             | (hd, args) ->
                 let uu____3320 =
                   let uu____3335 =
                     let uu____3336 = FStar_Syntax_Util.un_uinst hd in
                     uu____3336.FStar_Syntax_Syntax.n in
                   (uu____3335, args) in
                 (match uu____3320 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3356::uu____3357::(a1, uu____3359)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3426 =
                        let uu____3429 = unembed ea a1 in uu____3429 w norm in
                      FStar_Util.bind_opt uu____3426
                        (fun a2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3447::uu____3448::(b1, uu____3450)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3517 =
                        let uu____3520 = unembed eb b1 in uu____3520 w norm in
                      FStar_Util.bind_opt uu____3517
                        (fun b2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____3537 ->
                      (if w
                       then
                         (let uu____3553 =
                            let uu____3558 =
                              let uu____3559 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3559 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3558) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3553)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3565 =
        let uu____3566 = type_of ea in
        let uu____3567 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____3566 uu____3567 in
      mk_emb_full em un uu____3565 printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____3592 =
        let uu____3593 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____3593] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____3592 FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____3619 =
        let uu____3626 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____3626, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____3619 in
    let printer1 l =
      let uu____3639 =
        let uu____3640 =
          let uu____3641 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____3641 (FStar_String.concat "; ") in
        Prims.op_Hat uu____3640 "]" in
      Prims.op_Hat "[" uu____3639 in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____3678 ->
           let t =
             let uu____3680 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____3680 in
           match l with
           | [] ->
               let uu____3681 =
                 let uu____3682 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3682
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu____3681 [t] rng
           | hd::tl ->
               let cons =
                 let uu____3704 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3704
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____3719 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____3719 in
                 let uu____3720 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____3721 =
                   let uu____3722 =
                     let uu____3731 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____3731 in
                   let uu____3732 =
                     let uu____3743 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu____3743] in
                   uu____3722 :: uu____3732 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3720 uu____3721 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____3778 =
                 let uu____3779 =
                   let uu____3790 =
                     let uu____3799 =
                       let uu____3800 = embed ea hd in
                       uu____3800 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu____3799 in
                   let uu____3807 =
                     let uu____3818 =
                       let uu____3827 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu____3827 in
                     [uu____3818] in
                   uu____3790 :: uu____3807 in
                 t :: uu____3779 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu____3778 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____3897 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____3897 with
           | (hd, args) ->
               let uu____3938 =
                 let uu____3951 =
                   let uu____3952 = FStar_Syntax_Util.un_uinst hd in
                   uu____3952.FStar_Syntax_Syntax.n in
                 (uu____3951, args) in
               (match uu____3938 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____3968) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____3988, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3989))::(hd1,
                                                                 FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4030 =
                      let uu____4033 = unembed ea hd1 in uu____4033 w norm in
                    FStar_Util.bind_opt uu____4030
                      (fun hd2 ->
                         let uu____4045 = un tl w norm in
                         FStar_Util.bind_opt uu____4045
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4093 =
                      let uu____4096 = unembed ea hd1 in uu____4096 w norm in
                    FStar_Util.bind_opt uu____4093
                      (fun hd2 ->
                         let uu____4108 = un tl w norm in
                         FStar_Util.bind_opt uu____4108
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4123 ->
                    (if w
                     then
                       (let uu____4137 =
                          let uu____4142 =
                            let uu____4143 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4143 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4142) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4137)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4147 =
      let uu____4148 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4148 in
    mk_emb_full em un uu____4147 printer1 emb_t_list_a
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Simpl -> true | uu____4181 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4187 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4193 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4199 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4205 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4211 -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____4217 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4223 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4229 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4238 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4259 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4280 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4298 -> false
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_simpl
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_weak
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_hnf
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_primops
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_delta
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta
let (steps_ZetaFull : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta_full
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_iota
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_reify
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldattr
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_nbe
let (e_norm_step : norm_step embedding) =
  let t_norm_step =
    let uu____4302 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4302 in
  let emb_t_norm_step =
    let uu____4304 =
      let uu____4311 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4311, []) in
    FStar_Syntax_Syntax.ET_app uu____4304 in
  let printer1 uu____4319 = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____4344 ->
         match n with
         | Simpl -> steps_Simpl
         | Weak -> steps_Weak
         | HNF -> steps_HNF
         | Primops -> steps_Primops
         | Delta -> steps_Delta
         | Zeta -> steps_Zeta
         | ZetaFull -> steps_ZetaFull
         | Iota -> steps_Iota
         | NBE -> steps_NBE
         | Reify -> steps_Reify
         | UnfoldOnly l ->
             let uu____4348 =
               let uu____4349 =
                 let uu____4358 =
                   let uu____4359 =
                     let uu____4366 = e_list e_string in embed uu____4366 l in
                   uu____4359 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4358 in
               [uu____4349] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4348 rng
         | UnfoldFully l ->
             let uu____4394 =
               let uu____4395 =
                 let uu____4404 =
                   let uu____4405 =
                     let uu____4412 = e_list e_string in embed uu____4412 l in
                   uu____4405 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4404 in
               [uu____4395] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4394 rng
         | UnfoldAttr l ->
             let uu____4440 =
               let uu____4441 =
                 let uu____4450 =
                   let uu____4451 =
                     let uu____4458 = e_list e_string in embed uu____4458 l in
                   uu____4451 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4450 in
               [uu____4441] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4440 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu____4513 = FStar_Syntax_Util.head_and_args t1 in
         match uu____4513 with
         | (hd, args) ->
             let uu____4558 =
               let uu____4573 =
                 let uu____4574 = FStar_Syntax_Util.un_uinst hd in
                 uu____4574.FStar_Syntax_Syntax.n in
               (uu____4573, args) in
             (match uu____4558 with
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta_full
                  -> FStar_Pervasives_Native.Some ZetaFull
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4781)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____4816 =
                    let uu____4821 =
                      let uu____4830 = e_list e_string in
                      unembed uu____4830 l in
                    uu____4821 w norm in
                  FStar_Util.bind_opt uu____4816
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4845 ->
                            FStar_Pervasives_Native.Some uu____4845)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4848)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____4883 =
                    let uu____4888 =
                      let uu____4897 = e_list e_string in
                      unembed uu____4897 l in
                    uu____4888 w norm in
                  FStar_Util.bind_opt uu____4883
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4912 ->
                            FStar_Pervasives_Native.Some uu____4912)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4915)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____4950 =
                    let uu____4955 =
                      let uu____4964 = e_list e_string in
                      unembed uu____4964 l in
                    uu____4955 w norm in
                  FStar_Util.bind_opt uu____4950
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4979 ->
                            FStar_Pervasives_Native.Some uu____4979)
                         (UnfoldAttr ss))
              | uu____4980 ->
                  (if w
                   then
                     (let uu____4996 =
                        let uu____5001 =
                          let uu____5002 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5002 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5001) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____4996)
                   else ();
                   FStar_Pervasives_Native.None))) in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer1 emb_t_norm_step
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r)) rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____5055 ->
        (if w
         then
           (let uu____5057 =
              let uu____5062 =
                let uu____5063 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5063 in
              (FStar_Errors.Warning_NotEmbedded, uu____5062) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5057)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5065 =
    let uu____5066 =
      let uu____5073 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5073, []) in
    FStar_Syntax_Syntax.ET_app uu____5066 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5065
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None -> g ()
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let t_arrow =
        let uu____5139 =
          let uu____5140 =
            let uu____5155 =
              let uu____5164 =
                let uu____5171 = FStar_Syntax_Syntax.null_bv ea.typ in
                (uu____5171, FStar_Pervasives_Native.None) in
              [uu____5164] in
            let uu____5186 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu____5155, uu____5186) in
          FStar_Syntax_Syntax.Tm_arrow uu____5140 in
        FStar_Syntax_Syntax.mk uu____5139 FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____5254 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5259 ->
             let uu____5260 = force_shadow shadow_f in
             match uu____5260 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5265 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5265
                   then
                     let uu____5272 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5273 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5272 uu____5273
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f) in
                   (let uu____5277 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5277
                    then
                      let uu____5284 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5285 = FStar_Syntax_Print.term_to_string res in
                      let uu____5286 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5284 uu____5285 uu____5286
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu____5340 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____5340
                then
                  let uu____5347 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____5348 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____5347
                    uu____5348
                else ());
               (let a_tm =
                  let uu____5351 = embed ea a1 in
                  uu____5351 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu____5361 =
                    let uu____5366 =
                      let uu____5367 =
                        let uu____5368 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu____5368] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____5367
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____5366 in
                  norm uu____5361 in
                let uu____5393 =
                  let uu____5396 = unembed eb b_tm in uu____5396 w norm in
                match uu____5393 with
                | FStar_Pervasives_Native.None ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b1 -> b1) in
             FStar_Pervasives_Native.Some f_wrapped) in
      mk_emb_full em un t_arrow printer1 emb_t_arr_a_b
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun n_tvars ->
          fun fv_lid ->
            fun norm ->
              let rng = FStar_Ident.range_of_lid fv_lid in
              let f_wrapped args =
                let uu____5487 = FStar_List.splitAt n_tvars args in
                match uu____5487 with
                | (_tvar_args, rest_args) ->
                    let uu____5564 = FStar_List.hd rest_args in
                    (match uu____5564 with
                     | (x, uu____5584) ->
                         let shadow_app =
                           let uu____5598 =
                             FStar_Thunk.mk
                               (fun uu____5603 ->
                                  let uu____5604 =
                                    norm (FStar_Util.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____5604
                                    args rng) in
                           FStar_Pervasives_Native.Some uu____5598 in
                         let uu____5607 =
                           let uu____5610 =
                             let uu____5613 = unembed ea x in
                             uu____5613 true norm in
                           FStar_Util.map_opt uu____5610
                             (fun x1 ->
                                let uu____5623 =
                                  let uu____5630 = f x1 in
                                  embed eb uu____5630 in
                                uu____5623 rng shadow_app norm) in
                         (match uu____5607 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None ->
                              force_shadow shadow_app)) in
              f_wrapped
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun n_tvars ->
            fun fv_lid ->
              fun norm ->
                let rng = FStar_Ident.range_of_lid fv_lid in
                let f_wrapped args =
                  let uu____5730 = FStar_List.splitAt n_tvars args in
                  match uu____5730 with
                  | (_tvar_args, rest_args) ->
                      let uu____5793 = FStar_List.hd rest_args in
                      (match uu____5793 with
                       | (x, uu____5809) ->
                           let uu____5814 =
                             let uu____5821 = FStar_List.tl rest_args in
                             FStar_List.hd uu____5821 in
                           (match uu____5814 with
                            | (y, uu____5845) ->
                                let shadow_app =
                                  let uu____5855 =
                                    FStar_Thunk.mk
                                      (fun uu____5860 ->
                                         let uu____5861 =
                                           norm (FStar_Util.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____5861 args rng) in
                                  FStar_Pervasives_Native.Some uu____5855 in
                                let uu____5864 =
                                  let uu____5867 =
                                    let uu____5870 = unembed ea x in
                                    uu____5870 true norm in
                                  FStar_Util.bind_opt uu____5867
                                    (fun x1 ->
                                       let uu____5880 =
                                         let uu____5883 = unembed eb y in
                                         uu____5883 true norm in
                                       FStar_Util.bind_opt uu____5880
                                         (fun y1 ->
                                            let uu____5893 =
                                              let uu____5894 =
                                                let uu____5901 = f x1 y1 in
                                                embed ec uu____5901 in
                                              uu____5894 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu____5893)) in
                                (match uu____5864 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None ->
                                     force_shadow shadow_app))) in
                f_wrapped
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun n_tvars ->
              fun fv_lid ->
                fun norm ->
                  let rng = FStar_Ident.range_of_lid fv_lid in
                  let f_wrapped args =
                    let uu____6020 = FStar_List.splitAt n_tvars args in
                    match uu____6020 with
                    | (_tvar_args, rest_args) ->
                        let uu____6083 = FStar_List.hd rest_args in
                        (match uu____6083 with
                         | (x, uu____6099) ->
                             let uu____6104 =
                               let uu____6111 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6111 in
                             (match uu____6104 with
                              | (y, uu____6135) ->
                                  let uu____6140 =
                                    let uu____6147 =
                                      let uu____6156 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6156 in
                                    FStar_List.hd uu____6147 in
                                  (match uu____6140 with
                                   | (z, uu____6186) ->
                                       let shadow_app =
                                         let uu____6196 =
                                           FStar_Thunk.mk
                                             (fun uu____6201 ->
                                                let uu____6202 =
                                                  norm
                                                    (FStar_Util.Inl fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6202 args rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6196 in
                                       let uu____6205 =
                                         let uu____6208 =
                                           let uu____6211 = unembed ea x in
                                           uu____6211 true norm in
                                         FStar_Util.bind_opt uu____6208
                                           (fun x1 ->
                                              let uu____6221 =
                                                let uu____6224 = unembed eb y in
                                                uu____6224 true norm in
                                              FStar_Util.bind_opt uu____6221
                                                (fun y1 ->
                                                   let uu____6234 =
                                                     let uu____6237 =
                                                       unembed ec z in
                                                     uu____6237 true norm in
                                                   FStar_Util.bind_opt
                                                     uu____6234
                                                     (fun z1 ->
                                                        let uu____6247 =
                                                          let uu____6248 =
                                                            let uu____6255 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____6255 in
                                                          uu____6248 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6247))) in
                                       (match uu____6205 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____6282 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____6282 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____6292 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____6292 then FStar_Util.print1 "------ending %s\n" s else ());
       res)