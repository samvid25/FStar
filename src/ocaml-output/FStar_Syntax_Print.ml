open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___0_4 ->
    match uu___0_4 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____6 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_constant_at_level " uu____6
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____8 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_equational_at_level " uu____8
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____10 =
          let uu____11 = delta_depth_to_string d in Prims.op_Hat uu____11 ")" in
        Prims.op_Hat "Delta_abstract (" uu____10
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu____17 = FStar_Options.print_real_names () in
    if uu____17
    then FStar_Ident.string_of_lid l
    else
      (let uu____19 = FStar_Ident.ident_of_lid l in
       FStar_Ident.string_of_id uu____19)
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____35 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____36 =
      let uu____37 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "#" uu____37 in
    Prims.op_Hat uu____35 uu____36
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____43 = FStar_Options.print_real_names () in
    if uu____43
    then bv_to_string bv
    else FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____50 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____51 =
      let uu____52 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "@" uu____52 in
    Prims.op_Hat uu____50 uu____51
let (infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.op_Addition, "+");
  (FStar_Parser_Const.op_Subtraction, "-");
  (FStar_Parser_Const.op_Multiply, "*");
  (FStar_Parser_Const.op_Division, "/");
  (FStar_Parser_Const.op_Eq, "=");
  (FStar_Parser_Const.op_ColonEq, ":=");
  (FStar_Parser_Const.op_notEq, "<>");
  (FStar_Parser_Const.op_And, "&&");
  (FStar_Parser_Const.op_Or, "||");
  (FStar_Parser_Const.op_LTE, "<=");
  (FStar_Parser_Const.op_GTE, ">=");
  (FStar_Parser_Const.op_LT, "<");
  (FStar_Parser_Const.op_GT, ">");
  (FStar_Parser_Const.op_Modulus, "mod");
  (FStar_Parser_Const.and_lid, "/\\");
  (FStar_Parser_Const.or_lid, "\\/");
  (FStar_Parser_Const.imp_lid, "==>");
  (FStar_Parser_Const.iff_lid, "<==>");
  (FStar_Parser_Const.precedes_lid, "<<");
  (FStar_Parser_Const.eq2_lid, "==");
  (FStar_Parser_Const.eq3_lid, "===")]
let (unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")]
let (is_prim_op :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun ps ->
    fun f ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____190 -> false
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____201 -> failwith "get_lid"
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let (quants : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let (is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t -> is_prim_op [FStar_Parser_Const.b2t_lid] t
let (is_quant : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
let (is_ite : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t -> is_prim_op [FStar_Parser_Const.ite_lid] t
let (is_lex_cons : exp -> Prims.bool) =
  fun f -> is_prim_op [FStar_Parser_Const.lexcons_lid] f
let (is_lex_top : exp -> Prims.bool) =
  fun f -> is_prim_op [FStar_Parser_Const.lextop_lid] f
let is_inr :
  'uuuuuu273 'uuuuuu274 .
    ('uuuuuu273, 'uuuuuu274) FStar_Util.either -> Prims.bool
  =
  fun uu___1_283 ->
    match uu___1_283 with
    | FStar_Util.Inl uu____288 -> false
    | FStar_Util.Inr uu____289 -> true
let filter_imp :
  'uuuuuu294 .
    ('uuuuuu294 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu294 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_349 ->
            match uu___2_349 with
            | (uu____356, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____362, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____363)) -> false
            | (uu____366, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____367)) -> false
            | uu____370 -> true))
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e ->
    let uu____386 =
      let uu____387 = FStar_Syntax_Subst.compress e in
      uu____387.FStar_Syntax_Syntax.n in
    match uu____386 with
    | FStar_Syntax_Syntax.Tm_app (f, args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____448 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2))) in
        if uu____448
        then
          let uu____453 =
            let uu____458 = FStar_List.nth exps Prims.int_one in
            reconstruct_lex uu____458 in
          (match uu____453 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____468 =
                 let uu____471 = FStar_List.nth exps Prims.int_zero in
                 uu____471 :: xs in
               FStar_Pervasives_Native.Some uu____468
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____481 ->
        let uu____482 = is_lex_top e in
        if uu____482
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "blah"
      | hd::tl -> let uu____523 = f hd in if uu____523 then hd else find f tl
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x ->
    fun xs ->
      let uu____547 =
        find
          (fun p -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____547
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____571 = get_lid e in find_lid uu____571 infix_prim_ops
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____581 = get_lid e in find_lid uu____581 unary_prim_ops
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t -> let uu____591 = get_lid t in find_lid uu____591 quants
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x -> FStar_Parser_Const.const_to_string x
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_601 ->
    match uu___3_601 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu____609 = FStar_Options.hide_uvar_nums () in
    if uu____609
    then "?"
    else
      (let uu____611 =
         let uu____612 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____612 FStar_Util.string_of_int in
       Prims.op_Hat "?" uu____611)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu____618 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu____619 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____618 uu____619
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    -> Prims.string)
  =
  fun u ->
    let uu____645 = FStar_Options.hide_uvar_nums () in
    if uu____645
    then "?"
    else
      (let uu____647 =
         let uu____648 =
           let uu____649 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____649 FStar_Util.string_of_int in
         let uu____650 =
           let uu____651 =
             FStar_All.pipe_right u
               (fun uu____666 ->
                  match uu____666 with
                  | (uu____677, u1, uu____679) -> version_to_string u1) in
           Prims.op_Hat ":" uu____651 in
         Prims.op_Hat uu____648 uu____650 in
       Prims.op_Hat "?" uu____647)
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n ->
    fun u ->
      let uu____704 = FStar_Syntax_Subst.compress_univ u in
      match uu____704 with
      | FStar_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu____714 -> (n, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    FStar_Errors.with_ctx "While printing universe"
      (fun uu____726 ->
         let uu____727 = FStar_Syntax_Subst.compress_univ u in
         match uu____727 with
         | FStar_Syntax_Syntax.U_unif u1 ->
             let uu____739 = univ_uvar_to_string u1 in
             Prims.op_Hat "U_unif " uu____739
         | FStar_Syntax_Syntax.U_name x ->
             let uu____741 = FStar_Ident.string_of_id x in
             Prims.op_Hat "U_name " uu____741
         | FStar_Syntax_Syntax.U_bvar x ->
             let uu____743 = FStar_Util.string_of_int x in
             Prims.op_Hat "@" uu____743
         | FStar_Syntax_Syntax.U_zero -> "0"
         | FStar_Syntax_Syntax.U_succ u1 ->
             let uu____745 = int_of_univ Prims.int_one u1 in
             (match uu____745 with
              | (n, FStar_Pervasives_Native.None) ->
                  FStar_Util.string_of_int n
              | (n, FStar_Pervasives_Native.Some u2) ->
                  let uu____759 = univ_to_string u2 in
                  let uu____760 = FStar_Util.string_of_int n in
                  FStar_Util.format2 "(%s + %s)" uu____759 uu____760)
         | FStar_Syntax_Syntax.U_max us ->
             let uu____764 =
               let uu____765 = FStar_List.map univ_to_string us in
               FStar_All.pipe_right uu____765 (FStar_String.concat ", ") in
             FStar_Util.format1 "(max %s)" uu____764
         | FStar_Syntax_Syntax.U_unknown -> "unknown")
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us ->
    let uu____775 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____775 (FStar_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu____785 = FStar_List.map (fun x -> FStar_Ident.string_of_id x) us in
    FStar_All.pipe_right uu____785 (FStar_String.concat ", ")
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_796 ->
    match uu___4_796 with
    | FStar_Syntax_Syntax.Assumption -> "assume"
    | FStar_Syntax_Syntax.New -> "new"
    | FStar_Syntax_Syntax.Private -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction -> "inline"
    | FStar_Syntax_Syntax.NoExtract -> "noextract"
    | FStar_Syntax_Syntax.Visible_default -> "visible"
    | FStar_Syntax_Syntax.Irreducible -> "irreducible"
    | FStar_Syntax_Syntax.Noeq -> "noeq"
    | FStar_Syntax_Syntax.Unopteq -> "unopteq"
    | FStar_Syntax_Syntax.Logic -> "logic"
    | FStar_Syntax_Syntax.TotalEffect -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____798 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____798
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu____801 = lid_to_string l in
        let uu____802 = FStar_Ident.string_of_id x in
        FStar_Util.format2 "(Projector %s %s)" uu____801 uu____802
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu____813 =
          let uu____814 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____814 in
        let uu____815 =
          let uu____816 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____816 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____813 uu____815
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu____835 =
          let uu____836 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____836 in
        let uu____837 =
          let uu____838 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____838 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____835 uu____837
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____848 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____848
    | FStar_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect -> "Effect"
    | FStar_Syntax_Syntax.Reifiable -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu____850 = FStar_Ident.string_of_lid l in
        FStar_Util.format1 "(reflect %s)" uu____850
    | FStar_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____860 ->
        let uu____863 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____863 (FStar_String.concat " ")
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____881 ->
        let uu____884 = quals_to_string quals in Prims.op_Hat uu____884 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.op_Hat "(" (Prims.op_Hat s ")")
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1034 = db_to_string x in
        Prims.op_Hat "Tm_bvar: " uu____1034
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1036 = nm_to_string x in
        Prims.op_Hat "Tm_name: " uu____1036
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1038 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.op_Hat "Tm_fvar: " uu____1038
    | FStar_Syntax_Syntax.Tm_uinst uu____1039 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1046 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1047 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1048,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
           FStar_Syntax_Syntax.antiquotes = uu____1049;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1062,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
           FStar_Syntax_Syntax.antiquotes = uu____1063;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1076 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1095 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1110 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1117 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1134 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1157 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1184 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1197 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1210 -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta (uu____1225, m) ->
        let uu____1231 = metadata_to_string m in
        Prims.op_Hat "Tm_meta:" uu____1231
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1232 -> "Tm_lazy"
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu____1234 =
      let uu____1235 = FStar_Options.ugly () in Prims.op_Negation uu____1235 in
    if uu____1234
    then
      let e =
        FStar_Errors.with_ctx "While resugaring a term"
          (fun uu____1238 -> FStar_Syntax_Resugar.resugar_term x) in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      FStar_Errors.with_ctx "While ugly-printing a term"
        (fun uu____1245 ->
           let x1 = FStar_Syntax_Subst.compress x in
           let x2 =
             let uu____1250 = FStar_Options.print_implicits () in
             if uu____1250 then x1 else FStar_Syntax_Util.unmeta x1 in
           match x2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____1254 ->
               failwith "impossible"
           | FStar_Syntax_Syntax.Tm_app (uu____1269, []) ->
               failwith "Empty args!"
           | FStar_Syntax_Syntax.Tm_lazy
               { FStar_Syntax_Syntax.blob = b;
                 FStar_Syntax_Syntax.lkind =
                   FStar_Syntax_Syntax.Lazy_embedding (uu____1293, thunk);
                 FStar_Syntax_Syntax.ltyp = uu____1295;
                 FStar_Syntax_Syntax.rng = uu____1296;_}
               ->
               let uu____1307 =
                 let uu____1308 =
                   let uu____1309 = FStar_Thunk.force thunk in
                   term_to_string uu____1309 in
                 Prims.op_Hat uu____1308 "]" in
               Prims.op_Hat "[LAZYEMB:" uu____1307
           | FStar_Syntax_Syntax.Tm_lazy i ->
               let uu____1313 =
                 let uu____1314 =
                   let uu____1315 =
                     let uu____1316 =
                       let uu____1325 =
                         FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                       FStar_Util.must uu____1325 in
                     uu____1316 i.FStar_Syntax_Syntax.lkind i in
                   term_to_string uu____1315 in
                 Prims.op_Hat uu____1314 "]" in
               Prims.op_Hat "[lazy:" uu____1313
           | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
               (match qi.FStar_Syntax_Syntax.qkind with
                | FStar_Syntax_Syntax.Quote_static ->
                    let print_aq uu____1377 =
                      match uu____1377 with
                      | (bv, t) ->
                          let uu____1384 = bv_to_string bv in
                          let uu____1385 = term_to_string t in
                          FStar_Util.format2 "%s -> %s" uu____1384 uu____1385 in
                    let uu____1386 = term_to_string tm in
                    let uu____1387 =
                      FStar_Common.string_of_list print_aq
                        qi.FStar_Syntax_Syntax.antiquotes in
                    FStar_Util.format2 "`(%s)%s" uu____1386 uu____1387
                | FStar_Syntax_Syntax.Quote_dynamic ->
                    let uu____1394 = term_to_string tm in
                    FStar_Util.format1 "quote (%s)" uu____1394)
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_pattern (uu____1396, ps)) ->
               let pats =
                 let uu____1435 =
                   FStar_All.pipe_right ps
                     (FStar_List.map
                        (fun args ->
                           let uu____1469 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____1491 ->
                                     match uu____1491 with
                                     | (t1, uu____1499) -> term_to_string t1)) in
                           FStar_All.pipe_right uu____1469
                             (FStar_String.concat "; "))) in
                 FStar_All.pipe_right uu____1435 (FStar_String.concat "\\/") in
               let uu____1508 = term_to_string t in
               FStar_Util.format2 "{:pattern %s} %s" pats uu____1508
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
               let uu____1520 = tag_of_term t in
               let uu____1521 = sli m in
               let uu____1522 = term_to_string t' in
               let uu____1523 = term_to_string t in
               FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1520
                 uu____1521 uu____1522 uu____1523
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) ->
               let uu____1536 = tag_of_term t in
               let uu____1537 = term_to_string t' in
               let uu____1538 = sli m0 in
               let uu____1539 = sli m1 in
               let uu____1540 = term_to_string t in
               FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
                 uu____1536 uu____1537 uu____1538 uu____1539 uu____1540
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) ->
               let uu____1549 = FStar_Range.string_of_range r in
               let uu____1550 = term_to_string t in
               FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1549
                 uu____1550
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_named l) ->
               let uu____1557 = lid_to_string l in
               let uu____1558 =
                 FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
               let uu____1559 = term_to_string t in
               FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1557
                 uu____1558 uu____1559
           | FStar_Syntax_Syntax.Tm_meta
               (t, FStar_Syntax_Syntax.Meta_desugared uu____1561) ->
               let uu____1566 = term_to_string t in
               FStar_Util.format1 "Meta_desugared{%s}" uu____1566
           | FStar_Syntax_Syntax.Tm_bvar x3 ->
               let uu____1568 = db_to_string x3 in
               let uu____1569 =
                 let uu____1570 =
                   let uu____1571 = tag_of_term x3.FStar_Syntax_Syntax.sort in
                   Prims.op_Hat uu____1571 ")" in
                 Prims.op_Hat ":(" uu____1570 in
               Prims.op_Hat uu____1568 uu____1569
           | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
           | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
           | FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____1575)) ->
               let uu____1590 =
                 (FStar_Options.print_bound_var_types ()) &&
                   (FStar_Options.print_effect_args ()) in
               if uu____1590
               then ctx_uvar_to_string_aux true u
               else
                 (let uu____1592 =
                    let uu____1593 =
                      FStar_Syntax_Unionfind.uvar_id
                        u.FStar_Syntax_Syntax.ctx_uvar_head in
                    FStar_All.pipe_left FStar_Util.string_of_int uu____1593 in
                  Prims.op_Hat "?" uu____1592)
           | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
               let uu____1612 =
                 (FStar_Options.print_bound_var_types ()) &&
                   (FStar_Options.print_effect_args ()) in
               if uu____1612
               then
                 let uu____1613 = ctx_uvar_to_string_aux true u in
                 let uu____1614 =
                   let uu____1615 =
                     FStar_List.map subst_to_string
                       (FStar_Pervasives_Native.fst s) in
                   FStar_All.pipe_right uu____1615 (FStar_String.concat "; ") in
                 FStar_Util.format2 "(%s @ %s)" uu____1613 uu____1614
               else
                 (let uu____1627 =
                    let uu____1628 =
                      FStar_Syntax_Unionfind.uvar_id
                        u.FStar_Syntax_Syntax.ctx_uvar_head in
                    FStar_All.pipe_left FStar_Util.string_of_int uu____1628 in
                  Prims.op_Hat "?" uu____1627)
           | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1631 = FStar_Options.print_universes () in
               if uu____1631
               then
                 let uu____1632 = univ_to_string u in
                 FStar_Util.format1 "Type u#(%s)" uu____1632
               else "Type"
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               let uu____1656 = binders_to_string " -> " bs in
               let uu____1657 = comp_to_string c in
               FStar_Util.format2 "(%s -> %s)" uu____1656 uu____1657
           | FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) ->
               (match lc with
                | FStar_Pervasives_Native.Some rc when
                    FStar_Options.print_implicits () ->
                    let uu____1686 = binders_to_string " " bs in
                    let uu____1687 = term_to_string t2 in
                    let uu____1688 =
                      FStar_Ident.string_of_lid
                        rc.FStar_Syntax_Syntax.residual_effect in
                    let uu____1689 =
                      if
                        FStar_Option.isNone
                          rc.FStar_Syntax_Syntax.residual_typ
                      then "None"
                      else
                        (let uu____1693 =
                           FStar_Option.get
                             rc.FStar_Syntax_Syntax.residual_typ in
                         term_to_string uu____1693) in
                    FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                      uu____1686 uu____1687 uu____1688 uu____1689
                | uu____1696 ->
                    let uu____1699 = binders_to_string " " bs in
                    let uu____1700 = term_to_string t2 in
                    FStar_Util.format2 "(fun %s -> %s)" uu____1699 uu____1700)
           | FStar_Syntax_Syntax.Tm_refine (xt, f) ->
               let uu____1707 = bv_to_string xt in
               let uu____1708 =
                 FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort
                   term_to_string in
               let uu____1709 = FStar_All.pipe_right f formula_to_string in
               FStar_Util.format3 "(%s:%s{%s})" uu____1707 uu____1708
                 uu____1709
           | FStar_Syntax_Syntax.Tm_app (t, args) ->
               let uu____1738 = term_to_string t in
               let uu____1739 = args_to_string args in
               FStar_Util.format2 "(%s %s)" uu____1738 uu____1739
           | FStar_Syntax_Syntax.Tm_let (lbs, e) ->
               let uu____1758 = lbs_to_string [] lbs in
               let uu____1759 = term_to_string e in
               FStar_Util.format2 "%s\nin\n%s" uu____1758 uu____1759
           | FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) ->
               let annot1 =
                 match annot with
                 | FStar_Util.Inl t ->
                     let uu____1820 =
                       let uu____1821 =
                         FStar_Util.map_opt eff_name
                           FStar_Ident.string_of_lid in
                       FStar_All.pipe_right uu____1821
                         (FStar_Util.dflt "default") in
                     let uu____1826 = term_to_string t in
                     FStar_Util.format2 "[%s] %s" uu____1820 uu____1826
                 | FStar_Util.Inr c -> comp_to_string c in
               let topt1 =
                 match topt with
                 | FStar_Pervasives_Native.None -> ""
                 | FStar_Pervasives_Native.Some t ->
                     let uu____1842 = term_to_string t in
                     FStar_Util.format1 "by %s" uu____1842 in
               let uu____1843 = term_to_string e in
               FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1843 annot1
                 topt1
           | FStar_Syntax_Syntax.Tm_match (head, branches) ->
               let uu____1882 = term_to_string head in
               let uu____1883 =
                 let uu____1884 =
                   FStar_All.pipe_right branches
                     (FStar_List.map branch_to_string) in
                 FStar_Util.concat_l "\n\t|" uu____1884 in
               FStar_Util.format2 "(match %s with\n\t| %s)" uu____1882
                 uu____1883
           | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
               let uu____1897 = FStar_Options.print_universes () in
               if uu____1897
               then
                 let uu____1898 = term_to_string t in
                 let uu____1899 = univs_to_string us in
                 FStar_Util.format2 "%s<%s>" uu____1898 uu____1899
               else term_to_string t
           | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____1901 ->
    match uu____1901 with
    | (p, wopt, e) ->
        let uu____1921 = FStar_All.pipe_right p pat_to_string in
        let uu____1922 =
          match wopt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____1930 = FStar_All.pipe_right w term_to_string in
              FStar_Util.format1 "when %s" uu____1930 in
        let uu____1931 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format3 "%s %s -> %s" uu____1921 uu____1922 uu____1931
and (ctx_uvar_to_string_aux :
  Prims.bool -> FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun print_reason ->
    fun ctx_uvar ->
      let reason_string =
        if print_reason
        then
          FStar_Util.format1 "(* %s *)\n"
            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason
        else
          (let uu____1936 =
             let uu____1937 =
               FStar_Range.start_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Range.string_of_pos uu____1937 in
           let uu____1938 =
             let uu____1939 =
               FStar_Range.end_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Range.string_of_pos uu____1939 in
           FStar_Util.format2 "(%s-%s) " uu____1936 uu____1938) in
      let uu____1940 =
        binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
      let uu____1941 =
        uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
      let uu____1942 =
        term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
      FStar_Util.format4 "%s(%s |- %s : %s)" reason_string uu____1940
        uu____1941 uu____1942
and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_1943 ->
    match uu___5_1943 with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu____1946 = FStar_Util.string_of_int i in
        let uu____1947 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1946 uu____1947
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu____1950 = bv_to_string x in
        let uu____1951 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1950 uu____1951
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu____1958 = bv_to_string x in
        let uu____1959 = term_to_string t in
        FStar_Util.format2 "NT (%s, %s)" uu____1958 uu____1959
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu____1962 = FStar_Util.string_of_int i in
        let uu____1963 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1962 uu____1963
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu____1966 = FStar_Ident.string_of_id u in
        let uu____1967 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" uu____1966 uu____1967
and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu____1969 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1969 (FStar_String.concat "; ")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu____1979 =
      let uu____1980 = FStar_Options.ugly () in Prims.op_Negation uu____1980 in
    if uu____1979
    then
      let e =
        let uu____1982 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Syntax_Resugar.resugar_pat x uu____1982 in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, pats) ->
           let uu____2005 = fv_to_string l in
           let uu____2006 =
             let uu____2007 =
               FStar_List.map
                 (fun uu____2018 ->
                    match uu____2018 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.op_Hat "#" p else p) pats in
             FStar_All.pipe_right uu____2007 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____2005 uu____2006
       | FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2030) ->
           let uu____2035 = FStar_Options.print_bound_var_types () in
           if uu____2035
           then
             let uu____2036 = bv_to_string x1 in
             let uu____2037 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2036 uu____2037
           else
             (let uu____2039 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2039)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2041 = FStar_Options.print_bound_var_types () in
           if uu____2041
           then
             let uu____2042 = bv_to_string x1 in
             let uu____2043 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2042 uu____2043
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2047 = FStar_Options.print_bound_var_types () in
           if uu____2047
           then
             let uu____2048 = bv_to_string x1 in
             let uu____2049 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "_wild_%s:%s" uu____2048 uu____2049
           else bv_to_string x1)
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu____2055 = quals_to_string' quals in
      let uu____2056 =
        let uu____2057 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb ->
                  let uu____2073 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu____2074 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2075 =
                    let uu____2076 = FStar_Options.print_universes () in
                    if uu____2076
                    then
                      let uu____2077 =
                        let uu____2078 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.op_Hat uu____2078 ">" in
                      Prims.op_Hat "<" uu____2077
                    else "" in
                  let uu____2080 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2081 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2073
                    uu____2074 uu____2075 uu____2080 uu____2081)) in
        FStar_Util.concat_l "\n and " uu____2057 in
      FStar_Util.format3 "%slet %s %s" uu____2055
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2056
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2085 ->
    match uu___6_2085 with
    | [] -> ""
    | tms ->
        let uu____2091 =
          let uu____2092 =
            FStar_List.map
              (fun t -> let uu____2098 = term_to_string t in paren uu____2098)
              tms in
          FStar_All.pipe_right uu____2092 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____2091
and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___7_2102 ->
      match uu___7_2102 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
          Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____2111 =
            let uu____2112 = term_to_string t in
            Prims.op_Hat uu____2112 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[" uu____2111
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____2116 =
            let uu____2117 = term_to_string t in
            Prims.op_Hat uu____2117 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[@@" uu____2116
      | FStar_Pervasives_Native.None -> s
and (imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  = fun s -> fun aq -> aqual_to_string' s aq
and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun is_arrow ->
    fun b ->
      let uu____2130 =
        let uu____2131 = FStar_Options.ugly () in
        Prims.op_Negation uu____2131 in
      if uu____2130
      then
        let uu____2132 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2132 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2138 = b in
         match uu____2138 with
         | (a, imp) ->
             let uu____2151 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2151
             then
               let uu____2152 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.op_Hat "_:" uu____2152
             else
               (let uu____2154 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2156 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2156) in
                if uu____2154
                then
                  let uu____2157 = nm_to_string a in
                  imp_to_string uu____2157 imp
                else
                  (let uu____2159 =
                     let uu____2160 = nm_to_string a in
                     let uu____2161 =
                       let uu____2162 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.op_Hat ":" uu____2162 in
                     Prims.op_Hat uu____2160 uu____2161 in
                   imp_to_string uu____2159 imp)))
and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' false b
and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  = fun b -> binder_to_string' true b
and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep ->
    fun bs ->
      let bs1 =
        let uu____2176 = FStar_Options.print_implicits () in
        if uu____2176 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2180 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2180 (FStar_String.concat sep)
      else
        (let uu____2202 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2202 (FStar_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_2211 ->
    match uu___8_2211 with
    | (a, imp) ->
        let uu____2224 = term_to_string a in imp_to_string uu____2224 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu____2235 = FStar_Options.print_implicits () in
      if uu____2235 then args else filter_imp args in
    let uu____2247 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2247 (FStar_String.concat " ")
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu____2269 =
      let uu____2270 = FStar_Options.ugly () in Prims.op_Negation uu____2270 in
    if uu____2269
    then
      let e =
        FStar_Errors.with_ctx "While resugaring a computation"
          (fun uu____2273 -> FStar_Syntax_Resugar.resugar_comp c) in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      FStar_Errors.with_ctx "While ugly-printing a computation"
        (fun uu____2281 ->
           match c.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t, uopt) ->
               let uu____2292 =
                 let uu____2293 = FStar_Syntax_Subst.compress t in
                 uu____2293.FStar_Syntax_Syntax.n in
               (match uu____2292 with
                | FStar_Syntax_Syntax.Tm_type uu____2296 when
                    let uu____2297 =
                      (FStar_Options.print_implicits ()) ||
                        (FStar_Options.print_universes ()) in
                    Prims.op_Negation uu____2297 -> term_to_string t
                | uu____2298 ->
                    (match uopt with
                     | FStar_Pervasives_Native.Some u when
                         FStar_Options.print_universes () ->
                         let uu____2300 = univ_to_string u in
                         let uu____2301 = term_to_string t in
                         FStar_Util.format2 "Tot<%s> %s" uu____2300
                           uu____2301
                     | uu____2302 ->
                         let uu____2305 = term_to_string t in
                         FStar_Util.format1 "Tot %s" uu____2305))
           | FStar_Syntax_Syntax.GTotal (t, uopt) ->
               let uu____2316 =
                 let uu____2317 = FStar_Syntax_Subst.compress t in
                 uu____2317.FStar_Syntax_Syntax.n in
               (match uu____2316 with
                | FStar_Syntax_Syntax.Tm_type uu____2320 when
                    let uu____2321 =
                      (FStar_Options.print_implicits ()) ||
                        (FStar_Options.print_universes ()) in
                    Prims.op_Negation uu____2321 -> term_to_string t
                | uu____2322 ->
                    (match uopt with
                     | FStar_Pervasives_Native.Some u when
                         FStar_Options.print_universes () ->
                         let uu____2324 = univ_to_string u in
                         let uu____2325 = term_to_string t in
                         FStar_Util.format2 "GTot<%s> %s" uu____2324
                           uu____2325
                     | uu____2326 ->
                         let uu____2329 = term_to_string t in
                         FStar_Util.format1 "GTot %s" uu____2329))
           | FStar_Syntax_Syntax.Comp c1 ->
               let basic =
                 let uu____2332 = FStar_Options.print_effect_args () in
                 if uu____2332
                 then
                   let uu____2333 = sli c1.FStar_Syntax_Syntax.effect_name in
                   let uu____2334 =
                     let uu____2335 =
                       FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                         (FStar_List.map univ_to_string) in
                     FStar_All.pipe_right uu____2335
                       (FStar_String.concat ", ") in
                   let uu____2344 =
                     term_to_string c1.FStar_Syntax_Syntax.result_typ in
                   let uu____2345 =
                     let uu____2346 =
                       FStar_All.pipe_right
                         c1.FStar_Syntax_Syntax.effect_args
                         (FStar_List.map arg_to_string) in
                     FStar_All.pipe_right uu____2346
                       (FStar_String.concat ", ") in
                   let uu____2367 =
                     cflags_to_string c1.FStar_Syntax_Syntax.flags in
                   FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                     uu____2333 uu____2334 uu____2344 uu____2345 uu____2367
                 else
                   (let uu____2369 =
                      (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                         (FStar_Util.for_some
                            (fun uu___9_2373 ->
                               match uu___9_2373 with
                               | FStar_Syntax_Syntax.TOTAL -> true
                               | uu____2374 -> false)))
                        &&
                        (let uu____2376 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2376) in
                    if uu____2369
                    then
                      let uu____2377 =
                        term_to_string c1.FStar_Syntax_Syntax.result_typ in
                      FStar_Util.format1 "Tot %s" uu____2377
                    else
                      (let uu____2379 =
                         ((let uu____2382 =
                             FStar_Options.print_effect_args () in
                           Prims.op_Negation uu____2382) &&
                            (let uu____2384 =
                               FStar_Options.print_implicits () in
                             Prims.op_Negation uu____2384))
                           &&
                           (FStar_Ident.lid_equals
                              c1.FStar_Syntax_Syntax.effect_name
                              FStar_Parser_Const.effect_ML_lid) in
                       if uu____2379
                       then term_to_string c1.FStar_Syntax_Syntax.result_typ
                       else
                         (let uu____2386 =
                            (let uu____2389 =
                               FStar_Options.print_effect_args () in
                             Prims.op_Negation uu____2389) &&
                              (FStar_All.pipe_right
                                 c1.FStar_Syntax_Syntax.flags
                                 (FStar_Util.for_some
                                    (fun uu___10_2393 ->
                                       match uu___10_2393 with
                                       | FStar_Syntax_Syntax.MLEFFECT -> true
                                       | uu____2394 -> false))) in
                          if uu____2386
                          then
                            let uu____2395 =
                              term_to_string
                                c1.FStar_Syntax_Syntax.result_typ in
                            FStar_Util.format1 "ALL %s" uu____2395
                          else
                            (let uu____2397 =
                               sli c1.FStar_Syntax_Syntax.effect_name in
                             let uu____2398 =
                               term_to_string
                                 c1.FStar_Syntax_Syntax.result_typ in
                             FStar_Util.format2 "%s (%s)" uu____2397
                               uu____2398)))) in
               let dec =
                 let uu____2400 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.collect
                        (fun uu___11_2410 ->
                           match uu___11_2410 with
                           | FStar_Syntax_Syntax.DECREASES e ->
                               let uu____2416 =
                                 let uu____2417 = term_to_string e in
                                 FStar_Util.format1 " (decreases %s)"
                                   uu____2417 in
                               [uu____2416]
                           | uu____2418 -> [])) in
                 FStar_All.pipe_right uu____2400 (FStar_String.concat " ") in
               FStar_Util.format2 "%s%s" basic dec)
and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
  fun c ->
    match c with
    | FStar_Syntax_Syntax.TOTAL -> "total"
    | FStar_Syntax_Syntax.MLEFFECT -> "ml"
    | FStar_Syntax_Syntax.RETURN -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA -> "lemma"
    | FStar_Syntax_Syntax.CPS -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2422 -> ""
and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs -> FStar_Common.string_of_list cflag_to_string fs
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_2431 ->
    match uu___12_2431 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____2432, ps) ->
        let pats =
          let uu____2467 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args ->
                    let uu____2501 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2523 ->
                              match uu____2523 with
                              | (t, uu____2531) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2501
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____2467 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2541 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2541
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2544) ->
        let uu____2545 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2545
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____2553 = sli m in
        let uu____2554 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2553 uu____2554
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu____2562 = sli m in
        let uu____2563 = sli m' in
        let uu____2564 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2562
          uu____2563 uu____2564
let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq -> aqual_to_string' "" aq
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu____2580 = FStar_Options.ugly () in
      if uu____2580
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu____2594 = FStar_Options.ugly () in
      if uu____2594
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env ->
    fun b ->
      let uu____2608 = b in
      match uu____2608 with
      | (a, imp) ->
          let n =
            let uu____2616 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____2616
            then FStar_Util.JsonNull
            else
              (let uu____2618 =
                 let uu____2619 = nm_to_string a in
                 imp_to_string uu____2619 imp in
               FStar_Util.JsonStr uu____2618) in
          let t =
            let uu____2621 = term_to_string' env a.FStar_Syntax_Syntax.sort in
            FStar_Util.JsonStr uu____2621 in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env ->
    fun bs ->
      let uu____2644 = FStar_List.map (binder_to_json env) bs in
      FStar_Util.JsonList uu____2644
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu____2658 = FStar_Options.print_universes () in
    if uu____2658 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu____2665 =
      let uu____2666 = FStar_Options.ugly () in Prims.op_Negation uu____2666 in
    if uu____2665
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____2670 = s in
       match uu____2670 with
       | (us, t) ->
           let uu____2681 =
             let uu____2682 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2682 in
           let uu____2683 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2681 uu____2683)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu____2689 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2690 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2691 =
      let uu____2692 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2692 in
    let uu____2693 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2694 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2689 uu____2690 uu____2691
      uu____2693 uu____2694
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs ->
    let tscheme_opt_to_string uu___13_2707 =
      match uu___13_2707 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None -> "None" in
    let uu____2711 =
      let uu____2714 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp in
      let uu____2715 =
        let uu____2718 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp in
        let uu____2719 =
          let uu____2722 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger in
          let uu____2723 =
            let uu____2726 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else in
            let uu____2727 =
              let uu____2730 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp in
              let uu____2731 =
                let uu____2734 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp in
                let uu____2735 =
                  let uu____2738 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial in
                  let uu____2739 =
                    let uu____2742 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr in
                    let uu____2743 =
                      let uu____2746 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr in
                      let uu____2747 =
                        let uu____2750 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr in
                        [uu____2750] in
                      uu____2746 :: uu____2747 in
                    uu____2742 :: uu____2743 in
                  uu____2738 :: uu____2739 in
                uu____2734 :: uu____2735 in
              uu____2730 :: uu____2731 in
            uu____2726 :: uu____2727 in
          uu____2722 :: uu____2723 in
        uu____2718 :: uu____2719 in
      uu____2714 :: uu____2715 in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____2711
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs ->
    let to_str uu____2765 =
      match uu____2765 with
      | (ts_t, ts_ty) ->
          let uu____2772 = tscheme_to_string ts_t in
          let uu____2773 = tscheme_to_string ts_ty in
          FStar_Util.format2 "(%s) : (%s)" uu____2772 uu____2773 in
    let uu____2774 =
      let uu____2777 = to_str combs.FStar_Syntax_Syntax.l_repr in
      let uu____2778 =
        let uu____2781 = to_str combs.FStar_Syntax_Syntax.l_return in
        let uu____2782 =
          let uu____2785 = to_str combs.FStar_Syntax_Syntax.l_bind in
          let uu____2786 =
            let uu____2789 = to_str combs.FStar_Syntax_Syntax.l_subcomp in
            let uu____2790 =
              let uu____2793 =
                to_str combs.FStar_Syntax_Syntax.l_if_then_else in
              [uu____2793] in
            uu____2789 :: uu____2790 in
          uu____2785 :: uu____2786 in
        uu____2781 :: uu____2782 in
      uu____2777 :: uu____2778 in
    FStar_Util.format
      "{\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____2774
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_2798 ->
    match uu___14_2798 with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.Layered_eff combs ->
        layered_eff_combinators_to_string combs
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free ->
    fun r ->
      fun q ->
        fun ed ->
          let uu____2826 =
            let uu____2827 = FStar_Options.ugly () in
            Prims.op_Negation uu____2827 in
          if uu____2826
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____2841 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2841 (FStar_String.concat ",\n\t") in
             let eff_name =
               let uu____2851 = FStar_Syntax_Util.is_layered ed in
               if uu____2851 then "layered_effect" else "new_effect" in
             let uu____2853 =
               let uu____2856 =
                 let uu____2859 =
                   let uu____2862 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname in
                   let uu____2863 =
                     let uu____2866 =
                       let uu____2867 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                       FStar_All.pipe_left enclose_universes uu____2867 in
                     let uu____2868 =
                       let uu____2871 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                       let uu____2872 =
                         let uu____2875 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature in
                         let uu____2876 =
                           let uu____2879 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____2880 =
                             let uu____2883 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions in
                             [uu____2883] in
                           uu____2879 :: uu____2880 in
                         uu____2875 :: uu____2876 in
                       uu____2871 :: uu____2872 in
                     uu____2866 :: uu____2868 in
                   uu____2862 :: uu____2863 in
                 (if for_free then "_for_free " else "") :: uu____2859 in
               eff_name :: uu____2856 in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____2853)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____2910 = FStar_All.pipe_right ts_opt FStar_Util.must in
        FStar_All.pipe_right uu____2910 tscheme_to_string
      else "<None>" in
    let uu____2914 = lid_to_string se.FStar_Syntax_Syntax.source in
    let uu____2915 = lid_to_string se.FStar_Syntax_Syntax.target in
    let uu____2916 = tsopt_to_string se.FStar_Syntax_Syntax.lift in
    let uu____2917 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____2914 uu____2915 uu____2916 uu____2917
let (pragma_to_string : FStar_Syntax_Syntax.pragma -> Prims.string) =
  fun p ->
    match p with
    | FStar_Syntax_Syntax.LightOff -> "#light \"off\""
    | FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.None) ->
        "#reset-options"
    | FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.Some s) ->
        FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.SetOptions s ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.None) ->
        "#push-options"
    | FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some s) ->
        FStar_Util.format1 "#push-options \"%s\"" s
    | FStar_Syntax_Syntax.RestartSolver -> "#restart-solver"
    | FStar_Syntax_Syntax.PopOptions -> "#pop-options"
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma p -> pragma_to_string p
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univs, tps, k, uu____2937, uu____2938) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let binders_str = binders_to_string " " tps in
          let term_str = term_to_string k in
          let uu____2950 = FStar_Options.print_universes () in
          if uu____2950
          then
            let uu____2951 = FStar_Ident.string_of_lid lid in
            let uu____2952 = univ_names_to_string univs in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____2951
              uu____2952 binders_str term_str
          else
            (let uu____2954 = FStar_Ident.string_of_lid lid in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____2954
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univs, t, uu____2958, uu____2959, uu____2960) ->
          let uu____2965 = FStar_Options.print_universes () in
          if uu____2965
          then
            let uu____2966 = univ_names_to_string univs in
            let uu____2967 = FStar_Ident.string_of_lid lid in
            let uu____2968 = term_to_string t in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2966 uu____2967
              uu____2968
          else
            (let uu____2970 = FStar_Ident.string_of_lid lid in
             let uu____2971 = term_to_string t in
             FStar_Util.format2 "datacon %s : %s" uu____2970 uu____2971)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) ->
          let uu____2975 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let uu____2976 = FStar_Ident.string_of_lid lid in
          let uu____2977 =
            let uu____2978 = FStar_Options.print_universes () in
            if uu____2978
            then
              let uu____2979 = univ_names_to_string univs in
              FStar_Util.format1 "<%s>" uu____2979
            else "" in
          let uu____2981 = term_to_string t in
          FStar_Util.format4 "%sval %s %s : %s" uu____2975 uu____2976
            uu____2977 uu____2981
      | FStar_Syntax_Syntax.Sig_assume (lid, us, f) ->
          let uu____2985 = FStar_Options.print_universes () in
          if uu____2985
          then
            let uu____2986 = FStar_Ident.string_of_lid lid in
            let uu____2987 = univ_names_to_string us in
            let uu____2988 = term_to_string f in
            FStar_Util.format3 "assume %s<%s> : %s" uu____2986 uu____2987
              uu____2988
          else
            (let uu____2990 = FStar_Ident.string_of_lid lid in
             let uu____2991 = term_to_string f in
             FStar_Util.format2 "assume %s : %s" uu____2990 uu____2991)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____2993) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____2999) ->
          let uu____3008 =
            let uu____3009 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____3009 (FStar_String.concat "\n") in
          Prims.op_Hat "(* Sig_bundle *)" uu____3008
      | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
          let uu____3025 = FStar_Util.string_of_bool lax in
          let uu____3026 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs in
          let uu____3027 =
            let uu____3028 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____3028 (FStar_String.concat "\n") in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____3025 uu____3026 uu____3027
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3034 = FStar_Syntax_Util.is_dm4f ed in
          eff_decl_to_string' uu____3034 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, flags) ->
          let uu____3045 = FStar_Options.print_universes () in
          if uu____3045
          then
            let uu____3046 =
              let uu____3051 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Range.dummyRange in
              FStar_Syntax_Subst.open_univ_vars univs uu____3051 in
            (match uu____3046 with
             | (univs1, t) ->
                 let uu____3064 =
                   let uu____3069 =
                     let uu____3070 = FStar_Syntax_Subst.compress t in
                     uu____3070.FStar_Syntax_Syntax.n in
                   match uu____3069 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> (bs, c1)
                   | uu____3099 -> failwith "impossible" in
                 (match uu____3064 with
                  | (tps1, c1) ->
                      let uu____3106 = sli l in
                      let uu____3107 = univ_names_to_string univs1 in
                      let uu____3108 = binders_to_string " " tps1 in
                      let uu____3109 = comp_to_string c1 in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____3106
                        uu____3107 uu____3108 uu____3109))
          else
            (let uu____3111 = sli l in
             let uu____3112 = binders_to_string " " tps in
             let uu____3113 = comp_to_string c in
             FStar_Util.format3 "effect %s %s = %s" uu____3111 uu____3112
               uu____3113)
      | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
          let uu____3120 =
            let uu____3121 = FStar_List.map FStar_Ident.string_of_lid lids in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____3121 in
          let uu____3126 = term_to_string t in
          FStar_Util.format2 "splice[%s] (%s)" uu____3120 uu____3126
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m, n, p, t, ty) ->
          let uu____3132 = FStar_Ident.string_of_lid m in
          let uu____3133 = FStar_Ident.string_of_lid n in
          let uu____3134 = FStar_Ident.string_of_lid p in
          let uu____3135 = tscheme_to_string t in
          let uu____3136 = tscheme_to_string ty in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____3132 uu____3133 uu____3134 uu____3135 uu____3136
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m, n, t, ty) ->
          let uu____3141 = FStar_Ident.string_of_lid m in
          let uu____3142 = FStar_Ident.string_of_lid n in
          let uu____3143 = tscheme_to_string t in
          let uu____3144 = tscheme_to_string ty in
          FStar_Util.format4 "polymonadic_subcomp %s <: %s = (%s, %s)"
            uu____3141 uu____3142 uu____3143 uu____3144 in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____3145 ->
        let uu____3148 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
        Prims.op_Hat uu____3148 (Prims.op_Hat "\n" basic)
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma p -> pragma_to_string p
    | FStar_Syntax_Syntax.Sig_let
        ((false,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____3156;
            FStar_Syntax_Syntax.lbtyp = uu____3157;
            FStar_Syntax_Syntax.lbeff = uu____3158;
            FStar_Syntax_Syntax.lbdef = uu____3159;
            FStar_Syntax_Syntax.lbattrs = uu____3160;
            FStar_Syntax_Syntax.lbpos = uu____3161;_}::[]),
         uu____3162)
        ->
        let uu____3183 = lbname_to_string lb in
        FStar_Util.format1 "let %s" uu____3183
    | FStar_Syntax_Syntax.Sig_let
        ((true,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____3185;
            FStar_Syntax_Syntax.lbtyp = uu____3186;
            FStar_Syntax_Syntax.lbeff = uu____3187;
            FStar_Syntax_Syntax.lbdef = uu____3188;
            FStar_Syntax_Syntax.lbattrs = uu____3189;
            FStar_Syntax_Syntax.lbpos = uu____3190;_}::[]),
         uu____3191)
        ->
        let uu____3212 = lbname_to_string lb in
        FStar_Util.format1 "let rec %s" uu____3212
    | FStar_Syntax_Syntax.Sig_let
        ((true,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____3214;
            FStar_Syntax_Syntax.lbtyp = uu____3215;
            FStar_Syntax_Syntax.lbeff = uu____3216;
            FStar_Syntax_Syntax.lbdef = uu____3217;
            FStar_Syntax_Syntax.lbattrs = uu____3218;
            FStar_Syntax_Syntax.lbpos = uu____3219;_}::uu____3220),
         uu____3221)
        ->
        let uu____3244 = lbname_to_string lb in
        FStar_Util.format1 "let rec %s and ..." uu____3244
    | FStar_Syntax_Syntax.Sig_let uu____3245 ->
        failwith "Impossible: sigelt_to_string_short, ill-formed let"
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3253, t) ->
        let uu____3255 = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "val %s" uu____3255
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, uu____3257, uu____3258, uu____3259, uu____3260, uu____3261) ->
        let uu____3270 = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "type %s" uu____3270
    | FStar_Syntax_Syntax.Sig_datacon
        (lid, uu____3272, t, uu____3274, uu____3275, uu____3276) ->
        let uu____3281 = FStar_Ident.string_of_lid lid in
        let uu____3282 = term_to_string t in
        FStar_Util.format2 "datacon %s : %s" uu____3281 uu____3282
    | FStar_Syntax_Syntax.Sig_assume (lid, us, f) ->
        let uu____3286 = FStar_Ident.string_of_lid lid in
        let uu____3287 = term_to_string f in
        FStar_Util.format2 "assume %s : %s" uu____3286 uu____3287
    | FStar_Syntax_Syntax.Sig_bundle (ses, uu____3289) ->
        let uu____3298 = FStar_List.hd ses in
        FStar_All.pipe_right uu____3298 sigelt_to_string_short
    | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
        let uu____3310 =
          let uu____3311 = FStar_All.pipe_right ses FStar_List.hd in
          FStar_All.pipe_right uu____3311 sigelt_to_string_short in
        FStar_Util.format1 "[@@expect_failure] %s" uu____3310
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let kw =
          let uu____3316 = FStar_Syntax_Util.is_layered ed in
          if uu____3316
          then "layered_effect"
          else
            (let uu____3318 = FStar_Syntax_Util.is_dm4f ed in
             if uu____3318 then "new_effect_for_free" else "new_effect") in
        let uu____3320 = lid_to_string ed.FStar_Syntax_Syntax.mname in
        FStar_Util.format2 "%s { %s ... }" kw uu____3320
    | FStar_Syntax_Syntax.Sig_sub_effect se ->
        let uu____3322 = lid_to_string se.FStar_Syntax_Syntax.source in
        let uu____3323 = lid_to_string se.FStar_Syntax_Syntax.target in
        FStar_Util.format2 "sub_effect %s ~> %s" uu____3322 uu____3323
    | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, flags) ->
        let uu____3333 = sli l in
        let uu____3334 = binders_to_string " " tps in
        let uu____3335 = comp_to_string c in
        FStar_Util.format3 "effect %s %s = %s" uu____3333 uu____3334
          uu____3335
    | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
        let uu____3342 =
          let uu____3343 = FStar_List.map FStar_Ident.string_of_lid lids in
          FStar_All.pipe_left (FStar_String.concat "; ") uu____3343 in
        let uu____3348 = term_to_string t in
        FStar_Util.format3 "%splice[%s] (%s)" "%s" uu____3342 uu____3348
    | FStar_Syntax_Syntax.Sig_polymonadic_bind (m, n, p, t, ty) ->
        let uu____3354 = FStar_Ident.string_of_lid m in
        let uu____3355 = FStar_Ident.string_of_lid n in
        let uu____3356 = FStar_Ident.string_of_lid p in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu____3354
          uu____3355 uu____3356
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m, n, t, ty) ->
        let uu____3361 = FStar_Ident.string_of_lid m in
        let uu____3362 = FStar_Ident.string_of_lid n in
        FStar_Util.format2 "polymonadic_subcomp %s <: %s" uu____3361
          uu____3362
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____3368 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____3385 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____3394 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____3409 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____3416 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu____3423 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____3430 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3431 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3432 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____3445 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____3446 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3453 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3464 ->
        "Sig_polymonadic_subcomp"
    | FStar_Syntax_Syntax.Sig_fail uu____3473 -> "Sig_fail"
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu____3489 = sli m.FStar_Syntax_Syntax.name in
    let uu____3490 =
      let uu____3491 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3491 (FStar_String.concat "\n") in
    let uu____3496 =
      let uu____3497 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3497 (FStar_String.concat "\n") in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____3489
      uu____3490 uu____3496
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun elts ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____3535 = f x in
            FStar_Util.string_builder_append strb uu____3535);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3542 = f x1 in
                 FStar_Util.string_builder_append strb uu____3542)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f ->
    fun s ->
      let elts = FStar_Util.set_elements s in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "{";
           (let uu____3580 = f x in
            FStar_Util.string_builder_append strb uu____3580);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3587 = f x1 in
                 FStar_Util.string_builder_append strb uu____3587)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu____3603 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu____3603
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux true ctx_uvar
let (ctx_uvar_to_string_no_reason :
  FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux false ctx_uvar
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_3624 ->
    match uu___15_3624 with
    | FStar_Syntax_Syntax.ET_abstract -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h, []) -> h
    | FStar_Syntax_Syntax.ET_app (h, args) ->
        let uu____3634 =
          let uu____3635 =
            let uu____3636 =
              let uu____3637 =
                let uu____3638 = FStar_List.map emb_typ_to_string args in
                FStar_All.pipe_right uu____3638 (FStar_String.concat " ") in
              Prims.op_Hat uu____3637 ")" in
            Prims.op_Hat " " uu____3636 in
          Prims.op_Hat h uu____3635 in
        Prims.op_Hat "(" uu____3634
    | FStar_Syntax_Syntax.ET_fun (a, b) ->
        let uu____3645 =
          let uu____3646 = emb_typ_to_string a in
          let uu____3647 =
            let uu____3648 = emb_typ_to_string b in
            Prims.op_Hat ") -> " uu____3648 in
          Prims.op_Hat uu____3646 uu____3647 in
        Prims.op_Hat "(" uu____3645