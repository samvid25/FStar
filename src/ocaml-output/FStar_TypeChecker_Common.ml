open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee -> match projectee with | EQ -> true | uu____35 -> false
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUB -> true | uu____41 -> false
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUBINV -> true | uu____47 -> false
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_rigid -> true | uu____53 -> false
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid_eq -> true | uu____59 -> false
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex_pattern_eq -> true | uu____65 -> false
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid -> true | uu____71 -> false
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_flex -> true | uu____77 -> false
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex -> true | uu____83 -> false
type 'a problem =
  {
  pid: Prims.int ;
  lhs: 'a ;
  relation: rel ;
  rhs: 'a ;
  element: FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ;
  logical_guard: FStar_Syntax_Syntax.term ;
  logical_guard_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  reason: Prims.string Prims.list ;
  loc: FStar_Range.range ;
  rank: rank_t FStar_Pervasives_Native.option }
let __proj__Mkproblem__item__pid : 'a . 'a problem -> Prims.int =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> pid
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> lhs
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> relation
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rhs
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> element
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard
let __proj__Mkproblem__item__logical_guard_uvar :
  'a . 'a problem -> FStar_Syntax_Syntax.ctx_uvar =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard_uvar
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> reason
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> loc
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> rank_t FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rank
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee ->
    match projectee with | TProb _0 -> true | uu____473 -> false
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee -> match projectee with | TProb _0 -> _0
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee ->
    match projectee with | CProb _0 -> true | uu____494 -> false
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee -> match projectee with | CProb _0 -> _0
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_513 ->
    match uu___0_513 with
    | TProb p -> p
    | uu____519 -> failwith "Expected a TProb"
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Trivial -> true | uu____534 -> false
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | NonTrivial _0 -> true | uu____541 -> false
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string * prob) Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac ->
    fun f ->
      let t_by_tactic =
        let uu____569 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____569
          [FStar_Syntax_Syntax.U_zero] in
      let uu____570 =
        let uu____571 = FStar_Syntax_Syntax.as_arg tac in
        let uu____580 =
          let uu____591 = FStar_Syntax_Syntax.as_arg f in [uu____591] in
        uu____571 :: uu____580 in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____570
        FStar_Range.dummyRange
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l ->
    fun m ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_equational_at_level i,
         FStar_Syntax_Syntax.Delta_equational_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_constant_at_level i,
         FStar_Syntax_Syntax.Delta_constant_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_abstract d, uu____639) ->
          delta_depth_greater_than d m
      | (uu____640, FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____642, uu____643)
          -> true
      | (uu____644, FStar_Syntax_Syntax.Delta_equational_at_level uu____645)
          -> false
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_652 ->
    match uu___1_652 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____655 when
        uu____655 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____656 when
        uu____656 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_constant_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_equational_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_ty
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_range
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int * identifier_info) Prims.list ->
        (Prims.int * identifier_info) Prims.list)
  =
  fun col ->
    fun info ->
      fun col_infos ->
        let rec __insert aux rest =
          match rest with
          | [] -> (aux, [(col, info)])
          | (c, i)::rest' ->
              if col < c
              then (aux, ((col, info) :: rest))
              else __insert ((c, i) :: aux) rest' in
        let uu____897 = __insert [] col_infos in
        match uu____897 with
        | (l, r) -> FStar_List.append (FStar_List.rev l) r
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col ->
    fun col_infos ->
      let rec aux out uu___2_1002 =
        match uu___2_1002 with
        | [] -> out
        | (c, i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest in
      aux FStar_Pervasives_Native.None col_infos
type id_info_by_col = (Prims.int * identifier_info) Prims.list
type col_info_by_row = id_info_by_col FStar_Util.pimap
type row_info_by_file = col_info_by_row FStar_Util.psmap
type id_info_table =
  {
  id_info_enabled: Prims.bool ;
  id_info_db: row_info_by_file ;
  id_info_buffer: identifier_info Prims.list }
let (__proj__Mkid_info_table__item__id_info_enabled :
  id_info_table -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_enabled
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_db
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_buffer
let (id_info_table_empty : id_info_table) =
  let uu____1094 = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu____1094; id_info_buffer = [] }
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int * identifier_info) Prims.list FStar_Util.pimap
      FStar_Util.psmap ->
      identifier_info ->
        (Prims.int * identifier_info) Prims.list FStar_Util.pimap
          FStar_Util.psmap)
  =
  fun ty_map ->
    fun db ->
      fun info ->
        let range = info.identifier_range in
        let use_range =
          let uu____1147 = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu____1147 in
        let info1 =
          let uu___143_1149 = info in
          let uu____1150 = ty_map info.identifier_ty in
          {
            identifier = (uu___143_1149.identifier);
            identifier_ty = uu____1150;
            identifier_range = use_range
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____1153 =
          let uu____1158 = FStar_Range.line_of_pos start in
          let uu____1159 = FStar_Range.col_of_pos start in
          (uu____1158, uu____1159) in
        match uu____1153 with
        | (row, col) ->
            let rows =
              let uu____1181 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu____1181 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu____1221 =
              let uu____1230 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu____1230 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu____1221 (FStar_Util.psmap_add db fn)
let (id_info_insert :
  id_info_table ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table)
  =
  fun table ->
    fun id ->
      fun ty ->
        fun range ->
          let info =
            { identifier = id; identifier_ty = ty; identifier_range = range } in
          let uu___158_1312 = table in
          {
            id_info_enabled = (uu___158_1312.id_info_enabled);
            id_info_db = (uu___158_1312.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
let (id_info_insert_bv :
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun bv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu____1328 = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1328
        else table
let (id_info_insert_fv :
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun fv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu____1345 = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1345
        else table
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table ->
    fun enabled ->
      let uu___170_1357 = table in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1357.id_info_db);
        id_info_buffer = (uu___170_1357.id_info_buffer)
      }
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table ->
    fun ty_map ->
      let uu___174_1373 = table in
      let uu____1374 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___174_1373.id_info_enabled);
        id_info_db = uu____1374;
        id_info_buffer = []
      }
let (id_info_at_pos :
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option)
  =
  fun table ->
    fun fn ->
      fun row ->
        fun col ->
          let rows =
            let uu____1410 = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1410 in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu____1416 = find_nearest_preceding_col_info col cols in
          match uu____1416 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1423 =
                  FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu____1423 in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
let (check_uvar_ctx_invariant :
  Prims.string ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.binders -> unit)
  =
  fun reason ->
    fun r ->
      fun should_check ->
        fun g ->
          fun bs ->
            let print_gamma gamma =
              let uu____1462 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1472 ->
                        match uu___3_1472 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1474 =
                              FStar_Syntax_Print.bv_to_string x in
                            Prims.op_Hat "Binding_var " uu____1474
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu____1476 = FStar_Ident.string_of_id u in
                            Prims.op_Hat "Binding_univ " uu____1476
                        | FStar_Syntax_Syntax.Binding_lid (l, uu____1478) ->
                            let uu____1491 = FStar_Ident.string_of_lid l in
                            Prims.op_Hat "Binding_lid " uu____1491)) in
              FStar_All.pipe_right uu____1462 (FStar_String.concat "::\n") in
            let fail uu____1499 =
              let uu____1500 =
                let uu____1501 = FStar_Range.string_of_range r in
                let uu____1502 = print_gamma g in
                let uu____1503 = FStar_Syntax_Print.binders_to_string ", " bs in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1501
                  (if should_check then "true" else "false") uu____1502
                  uu____1503 in
              failwith uu____1500 in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1506 =
                 let uu____1531 =
                   FStar_Util.prefix_until
                     (fun uu___4_1546 ->
                        match uu___4_1546 with
                        | FStar_Syntax_Syntax.Binding_var uu____1547 -> true
                        | uu____1548 -> false) g in
                 (uu____1531, bs) in
               match uu____1506 with
               | (FStar_Pervasives_Native.None, []) -> ()
               | (FStar_Pervasives_Native.Some (uu____1605, hd, gamma_tail),
                  uu____1608::uu____1609) ->
                   let uu____1668 = FStar_Util.prefix bs in
                   (match uu____1668 with
                    | (uu____1693, (x, uu____1695)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____1723 -> fail ()))
               | uu____1724 -> fail ())
type implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
type implicits = implicit Prims.list
let (implicits_to_string : implicits -> Prims.string) =
  fun imps ->
    let imp_to_string i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
    FStar_Common.string_of_list imp_to_string imps
type guard_t =
  {
  guard_f: guard_formula ;
  deferred_to_tac: deferred ;
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> guard_f
let (__proj__Mkguard_t__item__deferred_to_tac : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred_to_tac
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred1
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> univ_ineqs
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> implicits1
let (trivial_guard : guard_t) =
  {
    guard_f = Trivial;
    deferred_to_tac = [];
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  }
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> g
      | (NonTrivial f1, NonTrivial f2) ->
          let uu____1983 = FStar_Syntax_Util.mk_conj f1 f2 in
          NonTrivial uu____1983
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t ->
    let uu____1989 =
      let uu____1990 = FStar_Syntax_Util.unmeta t in
      uu____1990.FStar_Syntax_Syntax.n in
    match uu____1989 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____1994 -> NonTrivial t
let (imp_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> Trivial
      | (NonTrivial f1, NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard :
  (guard_formula -> guard_formula -> guard_formula) ->
    guard_t -> guard_t -> guard_t)
  =
  fun f ->
    fun g1 ->
      fun g2 ->
        let uu____2035 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____2035;
          deferred_to_tac =
            (FStar_List.append g1.deferred_to_tac g2.deferred_to_tac);
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard conj_guard_f g1 g2
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard imp_guard_f g1 g2
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs -> FStar_List.fold_left conj_guard trivial_guard gs
let (weaken_guard_formula : guard_t -> FStar_Syntax_Syntax.typ -> guard_t) =
  fun g ->
    fun fml ->
      match g.guard_f with
      | Trivial -> g
      | NonTrivial f ->
          let uu___305_2104 = g in
          let uu____2105 =
            let uu____2106 = FStar_Syntax_Util.mk_imp fml f in
            check_trivial uu____2106 in
          {
            guard_f = uu____2105;
            deferred_to_tac = (uu___305_2104.deferred_to_tac);
            deferred = (uu___305_2104.deferred);
            univ_ineqs = (uu___305_2104.univ_ineqs);
            implicits = (uu___305_2104.implicits)
          }
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: FStar_Syntax_Syntax.typ ;
  cflags: FStar_Syntax_Syntax.cflag Prims.list ;
  comp_thunk:
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref
    }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
let (__proj__Mklcomp__item__res_typ : lcomp -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
let (__proj__Mklcomp__item__cflags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
let (__proj__Mklcomp__item__comp_thunk :
  lcomp ->
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref)
  =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
let (mk_lcomp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        (unit -> (FStar_Syntax_Syntax.comp * guard_t)) -> lcomp)
  =
  fun eff_name ->
    fun res_typ ->
      fun cflags ->
        fun comp_thunk ->
          let uu____2310 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu____2310 }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu____2351 = FStar_ST.op_Bang lc.comp_thunk in
    match uu____2351 with
    | FStar_Util.Inl thunk ->
        let uu____2410 = thunk () in
        (match uu____2410 with
         | (c, g) ->
             (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c);
              (c, g)))
    | FStar_Util.Inr c -> (c, trivial_guard)
let (apply_lcomp :
  (FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) ->
    (guard_t -> guard_t) -> lcomp -> lcomp)
  =
  fun fc ->
    fun fg ->
      fun lc ->
        mk_lcomp lc.eff_name lc.res_typ lc.cflags
          (fun uu____2496 ->
             let uu____2497 = lcomp_comp lc in
             match uu____2497 with
             | (c, g) ->
                 let uu____2508 = fc c in
                 let uu____2509 = fg g in (uu____2508, uu____2509))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu____2515 = FStar_Options.print_effect_args () in
    if uu____2515
    then
      let uu____2516 =
        let uu____2517 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu____2517 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu____2516
    else
      (let uu____2531 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu____2532 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu____2531 uu____2532)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2557 -> c
        | FStar_Syntax_Syntax.GTotal uu____2566 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2577 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2577.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2577.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2577.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2577.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___358_2578 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2578.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2578.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2581 ->
           let uu____2582 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2582
             (fun uu____2604 ->
                match uu____2604 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2627 ->
               match uu___5_2627 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2628 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2637 ->
               match uu___6_2637 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2638 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_2647 ->
            match uu___7_2647 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____2648 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_2657 ->
               match uu___8_2657 with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu____2658 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____2676 ->
           let uu____2677 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2677
             (fun uu____2704 ->
                match uu____2704 with
                | (c, g) ->
                    let uu____2721 = FStar_Syntax_Util.set_result_typ c t in
                    (uu____2721, g)))
let (residual_comp_of_lcomp : lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.cflags)
    }
let (lcomp_of_comp_guard : FStar_Syntax_Syntax.comp -> guard_t -> lcomp) =
  fun c0 ->
    fun g ->
      let uu____2739 =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2752 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu____2763 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu____2739 with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu____2784 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___409_2812 = t in
        {
          FStar_Syntax_Syntax.n = (uu___409_2812.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___409_2812.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu____2823 =
          let uu____2824 = FStar_Syntax_Util.unmeta t in
          uu____2824.FStar_Syntax_Syntax.n in
        match uu____2823 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____2831 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu____2892)::args1, (bv, uu____2895)::bs1) ->
            let uu____2949 =
              let uu____2950 = FStar_Syntax_Subst.compress t in
              uu____2950.FStar_Syntax_Syntax.n in
            (match uu____2949 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____2954 -> false)
        | ([], []) -> true
        | (uu____2983, uu____2984) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu____3033 = FStar_Syntax_Print.term_to_string t in
           let uu____3034 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3033
             uu____3034)
        else ();
        (let uu____3036 = FStar_Syntax_Util.head_and_args' t in
         match uu____3036 with
         | (hd, args) ->
             let uu____3075 =
               let uu____3076 = FStar_Syntax_Subst.compress hd in
               uu____3076.FStar_Syntax_Syntax.n in
             (match uu____3075 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3083 = FStar_Syntax_Print.term_to_string t in
                      let uu____3084 = FStar_Syntax_Print.bv_to_string bv in
                      let uu____3085 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3083 uu____3084 uu____3085)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3087 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3104 = FStar_Syntax_Print.term_to_string t in
           let uu____3105 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3104 uu____3105)
        else ();
        (let uu____3107 = FStar_Syntax_Util.is_squash t in
         match uu____3107 with
         | FStar_Pervasives_Native.Some (uu____3118, t') -> is_applied bs t'
         | uu____3130 ->
             let uu____3139 = FStar_Syntax_Util.is_auto_squash t in
             (match uu____3139 with
              | FStar_Pervasives_Native.Some (uu____3150, t') ->
                  is_applied bs t'
              | uu____3162 -> is_applied bs t)) in
      let is_const_match phi =
        let uu____3181 =
          let uu____3182 = FStar_Syntax_Subst.compress phi in
          uu____3182.FStar_Syntax_Syntax.n in
        match uu____3181 with
        | FStar_Syntax_Syntax.Tm_match (uu____3187, br::brs) ->
            let uu____3254 = br in
            (match uu____3254 with
             | (uu____3271, uu____3272, e) ->
                 let r =
                   let uu____3293 = simp_t e in
                   match uu____3293 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3299 =
                         FStar_List.for_all
                           (fun uu____3317 ->
                              match uu____3317 with
                              | (uu____3330, uu____3331, e') ->
                                  let uu____3345 = simp_t e' in
                                  uu____3345 =
                                    (FStar_Pervasives_Native.Some b)) brs in
                       if uu____3299
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu____3353 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu____3362 = FStar_Syntax_Util.is_sub_singleton t in
        if uu____3362
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3395 =
          match uu____3395 with
          | (t1, q) ->
              let uu____3416 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu____3416 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu____3448 -> (t1, q)) in
        let uu____3461 = FStar_Syntax_Util.head_and_args t in
        match uu____3461 with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu____3537 =
          let uu____3538 = FStar_Syntax_Util.unmeta ty in
          uu____3538.FStar_Syntax_Syntax.n in
        match uu____3537 with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu____3542) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3547, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3571 -> false in
      let simplify arg =
        let uu____3602 = simp_t (FStar_Pervasives_Native.fst arg) in
        (uu____3602, arg) in
      let uu____3615 =
        let uu____3616 = FStar_Syntax_Subst.compress tm in
        uu____3616.FStar_Syntax_Syntax.n in
      match uu____3615 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____3620;
                  FStar_Syntax_Syntax.vars = uu____3621;_},
                uu____3622);
             FStar_Syntax_Syntax.pos = uu____3623;
             FStar_Syntax_Syntax.vars = uu____3624;_},
           args)
          ->
          let uu____3654 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____3654
          then
            let uu____3655 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____3655 with
             | (FStar_Pervasives_Native.Some (true), uu____3710)::(uu____3711,
                                                                   (arg,
                                                                    uu____3713))::[]
                 -> maybe_auto_squash arg
             | (uu____3778, (arg, uu____3780))::(FStar_Pervasives_Native.Some
                                                 (true), uu____3781)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____3846)::uu____3847::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3910::(FStar_Pervasives_Native.Some (false), uu____3911)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3974 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____3990 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____3990
             then
               let uu____3991 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____3991 with
               | (FStar_Pervasives_Native.Some (true), uu____4046)::uu____4047::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4110::(FStar_Pervasives_Native.Some (true),
                              uu____4111)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____4174)::
                   (uu____4175, (arg, uu____4177))::[] ->
                   maybe_auto_squash arg
               | (uu____4242, (arg, uu____4244))::(FStar_Pervasives_Native.Some
                                                   (false), uu____4245)::[]
                   -> maybe_auto_squash arg
               | uu____4310 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4326 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____4326
                then
                  let uu____4327 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4327 with
                  | uu____4382::(FStar_Pervasives_Native.Some (true),
                                 uu____4383)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____4446)::uu____4447::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____4510)::
                      (uu____4511, (arg, uu____4513))::[] ->
                      maybe_auto_squash arg
                  | (uu____4578, (p, uu____4580))::(uu____4581,
                                                    (q, uu____4583))::[]
                      ->
                      let uu____4648 = FStar_Syntax_Util.term_eq p q in
                      (if uu____4648
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____4650 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____4666 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____4666
                   then
                     let uu____4667 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4667 with
                     | (FStar_Pervasives_Native.Some (true), uu____4722)::
                         (FStar_Pervasives_Native.Some (true), uu____4723)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____4788)::
                         (FStar_Pervasives_Native.Some (false), uu____4789)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____4854)::
                         (FStar_Pervasives_Native.Some (false), uu____4855)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____4920)::
                         (FStar_Pervasives_Native.Some (true), uu____4921)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____4986, (arg, uu____4988))::(FStar_Pervasives_Native.Some
                                                         (true), uu____4989)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____5054)::
                         (uu____5055, (arg, uu____5057))::[] ->
                         maybe_auto_squash arg
                     | (uu____5122, (arg, uu____5124))::(FStar_Pervasives_Native.Some
                                                         (false), uu____5125)::[]
                         ->
                         let uu____5190 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5190
                     | (FStar_Pervasives_Native.Some (false), uu____5191)::
                         (uu____5192, (arg, uu____5194))::[] ->
                         let uu____5259 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5259
                     | (uu____5260, (p, uu____5262))::(uu____5263,
                                                       (q, uu____5265))::[]
                         ->
                         let uu____5330 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5330
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5332 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5348 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5348
                      then
                        let uu____5349 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5349 with
                        | (FStar_Pervasives_Native.Some (true), uu____5404)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____5443)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5482 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____5498 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5498
                         then
                           match args with
                           | (t, uu____5500)::[] ->
                               let uu____5525 =
                                 let uu____5526 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5526.FStar_Syntax_Syntax.n in
                               (match uu____5525 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5529::[], body, uu____5531) ->
                                    let uu____5566 = simp_t body in
                                    (match uu____5566 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5569 -> tm)
                                | uu____5572 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5574))::
                               (t, uu____5576)::[] ->
                               let uu____5615 =
                                 let uu____5616 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5616.FStar_Syntax_Syntax.n in
                               (match uu____5615 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5619::[], body, uu____5621) ->
                                    let uu____5656 = simp_t body in
                                    (match uu____5656 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____5659 -> tm)
                                | uu____5662 -> tm)
                           | uu____5663 -> tm
                         else
                           (let uu____5675 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5675
                            then
                              match args with
                              | (t, uu____5677)::[] ->
                                  let uu____5702 =
                                    let uu____5703 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5703.FStar_Syntax_Syntax.n in
                                  (match uu____5702 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5706::[], body, uu____5708) ->
                                       let uu____5743 = simp_t body in
                                       (match uu____5743 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5746 -> tm)
                                   | uu____5749 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5751))::
                                  (t, uu____5753)::[] ->
                                  let uu____5792 =
                                    let uu____5793 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5793.FStar_Syntax_Syntax.n in
                                  (match uu____5792 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5796::[], body, uu____5798) ->
                                       let uu____5833 = simp_t body in
                                       (match uu____5833 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____5836 -> tm)
                                   | uu____5839 -> tm)
                              | uu____5840 -> tm
                            else
                              (let uu____5852 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____5852
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____5853;
                                      FStar_Syntax_Syntax.vars = uu____5854;_},
                                    uu____5855)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____5880;
                                      FStar_Syntax_Syntax.vars = uu____5881;_},
                                    uu____5882)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____5907 -> tm
                               else
                                 (let uu____5919 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____5919
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____5929 =
                                        let uu____5930 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____5930.FStar_Syntax_Syntax.n in
                                      match uu____5929 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____5938 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____5948 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____5948
                                           FStar_Pervasives_Native.fst in
                                       let uu____5987 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____5987
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____5989 =
                                             let uu____5990 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____5990.FStar_Syntax_Syntax.n in
                                           match uu____5989 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____5993 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____6001 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____6001
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6006 =
                                                      let uu____6007 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____6007.FStar_Syntax_Syntax.n in
                                                    match uu____6006 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____6013) ->
                                                        hd
                                                    | uu____6038 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____6041 =
                                                    let uu____6052 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____6052] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6041)
                                           | uu____6085 -> tm))
                                     else tm)
                                  else
                                    (let uu____6088 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____6088
                                     then
                                       match args with
                                       | (_typ, uu____6090)::(a1, uu____6092)::
                                           (a2, uu____6094)::[] ->
                                           let uu____6151 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____6151 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6152 -> tm)
                                       | uu____6153 -> tm
                                     else
                                       (let uu____6165 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____6165
                                        then
                                          match args with
                                          | (t1, uu____6167)::(t2,
                                                               uu____6169)::
                                              (a1, uu____6171)::(a2,
                                                                 uu____6173)::[]
                                              ->
                                              let uu____6246 =
                                                let uu____6247 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____6248 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6247 uu____6248 in
                                              (match uu____6246 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6249 -> tm)
                                          | uu____6250 -> tm
                                        else
                                          (let uu____6262 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____6262 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6282 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6292;
             FStar_Syntax_Syntax.vars = uu____6293;_},
           args)
          ->
          let uu____6319 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____6319
          then
            let uu____6320 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____6320 with
             | (FStar_Pervasives_Native.Some (true), uu____6375)::(uu____6376,
                                                                   (arg,
                                                                    uu____6378))::[]
                 -> maybe_auto_squash arg
             | (uu____6443, (arg, uu____6445))::(FStar_Pervasives_Native.Some
                                                 (true), uu____6446)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____6511)::uu____6512::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6575::(FStar_Pervasives_Native.Some (false), uu____6576)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6639 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____6655 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____6655
             then
               let uu____6656 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____6656 with
               | (FStar_Pervasives_Native.Some (true), uu____6711)::uu____6712::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____6775::(FStar_Pervasives_Native.Some (true),
                              uu____6776)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____6839)::
                   (uu____6840, (arg, uu____6842))::[] ->
                   maybe_auto_squash arg
               | (uu____6907, (arg, uu____6909))::(FStar_Pervasives_Native.Some
                                                   (false), uu____6910)::[]
                   -> maybe_auto_squash arg
               | uu____6975 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____6991 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____6991
                then
                  let uu____6992 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____6992 with
                  | uu____7047::(FStar_Pervasives_Native.Some (true),
                                 uu____7048)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____7111)::uu____7112::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____7175)::
                      (uu____7176, (arg, uu____7178))::[] ->
                      maybe_auto_squash arg
                  | (uu____7243, (p, uu____7245))::(uu____7246,
                                                    (q, uu____7248))::[]
                      ->
                      let uu____7313 = FStar_Syntax_Util.term_eq p q in
                      (if uu____7313
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____7315 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____7331 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____7331
                   then
                     let uu____7332 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7332 with
                     | (FStar_Pervasives_Native.Some (true), uu____7387)::
                         (FStar_Pervasives_Native.Some (true), uu____7388)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____7453)::
                         (FStar_Pervasives_Native.Some (false), uu____7454)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____7519)::
                         (FStar_Pervasives_Native.Some (false), uu____7520)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____7585)::
                         (FStar_Pervasives_Native.Some (true), uu____7586)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____7651, (arg, uu____7653))::(FStar_Pervasives_Native.Some
                                                         (true), uu____7654)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____7719)::
                         (uu____7720, (arg, uu____7722))::[] ->
                         maybe_auto_squash arg
                     | (uu____7787, (arg, uu____7789))::(FStar_Pervasives_Native.Some
                                                         (false), uu____7790)::[]
                         ->
                         let uu____7855 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7855
                     | (FStar_Pervasives_Native.Some (false), uu____7856)::
                         (uu____7857, (arg, uu____7859))::[] ->
                         let uu____7924 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7924
                     | (uu____7925, (p, uu____7927))::(uu____7928,
                                                       (q, uu____7930))::[]
                         ->
                         let uu____7995 = FStar_Syntax_Util.term_eq p q in
                         (if uu____7995
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____7997 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8013 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8013
                      then
                        let uu____8014 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8014 with
                        | (FStar_Pervasives_Native.Some (true), uu____8069)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____8108)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8147 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____8163 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8163
                         then
                           match args with
                           | (t, uu____8165)::[] ->
                               let uu____8190 =
                                 let uu____8191 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8191.FStar_Syntax_Syntax.n in
                               (match uu____8190 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8194::[], body, uu____8196) ->
                                    let uu____8231 = simp_t body in
                                    (match uu____8231 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____8234 -> tm)
                                | uu____8237 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8239))::
                               (t, uu____8241)::[] ->
                               let uu____8280 =
                                 let uu____8281 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8281.FStar_Syntax_Syntax.n in
                               (match uu____8280 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8284::[], body, uu____8286) ->
                                    let uu____8321 = simp_t body in
                                    (match uu____8321 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____8324 -> tm)
                                | uu____8327 -> tm)
                           | uu____8328 -> tm
                         else
                           (let uu____8340 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8340
                            then
                              match args with
                              | (t, uu____8342)::[] ->
                                  let uu____8367 =
                                    let uu____8368 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8368.FStar_Syntax_Syntax.n in
                                  (match uu____8367 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8371::[], body, uu____8373) ->
                                       let uu____8408 = simp_t body in
                                       (match uu____8408 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____8411 -> tm)
                                   | uu____8414 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8416))::
                                  (t, uu____8418)::[] ->
                                  let uu____8457 =
                                    let uu____8458 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8458.FStar_Syntax_Syntax.n in
                                  (match uu____8457 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8461::[], body, uu____8463) ->
                                       let uu____8498 = simp_t body in
                                       (match uu____8498 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____8501 -> tm)
                                   | uu____8504 -> tm)
                              | uu____8505 -> tm
                            else
                              (let uu____8517 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____8517
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____8518;
                                      FStar_Syntax_Syntax.vars = uu____8519;_},
                                    uu____8520)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____8545;
                                      FStar_Syntax_Syntax.vars = uu____8546;_},
                                    uu____8547)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____8572 -> tm
                               else
                                 (let uu____8584 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____8584
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____8594 =
                                        let uu____8595 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8595.FStar_Syntax_Syntax.n in
                                      match uu____8594 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____8603 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____8613 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____8613
                                           FStar_Pervasives_Native.fst in
                                       let uu____8648 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____8648
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____8650 =
                                             let uu____8651 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____8651.FStar_Syntax_Syntax.n in
                                           match uu____8650 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____8654 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____8662 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____8662
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____8667 =
                                                      let uu____8668 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____8668.FStar_Syntax_Syntax.n in
                                                    match uu____8667 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____8674) ->
                                                        hd
                                                    | uu____8699 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____8702 =
                                                    let uu____8713 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____8713] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____8702)
                                           | uu____8746 -> tm))
                                     else tm)
                                  else
                                    (let uu____8749 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____8749
                                     then
                                       match args with
                                       | (_typ, uu____8751)::(a1, uu____8753)::
                                           (a2, uu____8755)::[] ->
                                           let uu____8812 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____8812 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8813 -> tm)
                                       | uu____8814 -> tm
                                     else
                                       (let uu____8826 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____8826
                                        then
                                          match args with
                                          | (t1, uu____8828)::(t2,
                                                               uu____8830)::
                                              (a1, uu____8832)::(a2,
                                                                 uu____8834)::[]
                                              ->
                                              let uu____8907 =
                                                let uu____8908 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____8909 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____8908 uu____8909 in
                                              (match uu____8907 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____8910 -> tm)
                                          | uu____8911 -> tm
                                        else
                                          (let uu____8923 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____8923 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____8943 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu____8958 = simp_t t in
          (match uu____8958 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____8961 ->
          let uu____8984 = is_const_match tm in
          (match uu____8984 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu____8987 -> tm