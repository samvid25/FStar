open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string * FStar_Range.range) 
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
  | SConst of FStar_Const.sconst 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu____56 -> false
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu____63 -> false
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu____76 -> false
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_String : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____93 -> false
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | Char _0 -> true | uu____118 -> false
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee -> match projectee with | Char _0 -> _0
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | Range _0 -> true | uu____131 -> false
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee -> match projectee with | Range _0 -> _0
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | SConst _0 -> true | uu____144 -> false
let (__proj__SConst__item___0 : constant -> FStar_Const.sconst) =
  fun projectee -> match projectee with | SConst _0 -> _0
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStar_Syntax_Syntax.term FStar_Thunk.t 
and t' =
  | Lam of ((t Prims.list -> t) *
  ((t Prims.list * FStar_Syntax_Syntax.binders *
     FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
  (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either * Prims.int)
  
  | Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list *
  (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of (FStar_Syntax_Syntax.term FStar_Thunk.t,
  ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp)) FStar_Util.either 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of ((FStar_Syntax_Syntax.lazyinfo,
  (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t
  FStar_Thunk.t) 
  | Meta of (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t) 
  | TopLevelLet of (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
  FStar_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStar_Syntax_Syntax.letbinding *
  FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
and t = {
  nbe_t: t' ;
  nbe_r: FStar_Range.range }
and comp =
  | Tot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | GTot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args: (t * FStar_Syntax_Syntax.aqual) Prims.list ;
  flags: cflag Prims.list }
and cflag =
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | PARTIAL_RETURN 
  | SOMETRIVIAL 
  | TRIVIAL_POSTCONDITION 
  | SHOULD_NOT_INLINE 
  | LEMMA 
  | CPS 
  | DECREASES of t 
and residual_comp =
  {
  residual_effect: FStar_Ident.lident ;
  residual_typ: t FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu____615 -> false
let (__proj__Var__item___0 : atom -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____637 -> false
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLet _0 -> true | uu____693 -> false
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee -> match projectee with | UnreducedLet _0 -> _0
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLetRec _0 -> true | uu____770 -> false
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee -> match projectee with | UnreducedLetRec _0 -> _0
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UVar _0 -> true | uu____833 -> false
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee -> match projectee with | UVar _0 -> _0
let (uu___is_Lam : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lam _0 -> true | uu____883 -> false
let (__proj__Lam__item___0 :
  t' ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either *
      Prims.int))
  = fun projectee -> match projectee with | Lam _0 -> _0
let (uu___is_Accu : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Accu _0 -> true | uu____999 -> false
let (__proj__Accu__item___0 :
  t' -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee -> match projectee with | Accu _0 -> _0
let (uu___is_Construct : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu____1056 -> false
let (__proj__Construct__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_FV : t' -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu____1125 -> false
let (__proj__FV__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_Constant : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Constant _0 -> true | uu____1180 -> false
let (__proj__Constant__item___0 : t' -> constant) =
  fun projectee -> match projectee with | Constant _0 -> _0
let (uu___is_Type_t : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Type_t _0 -> true | uu____1193 -> false
let (__proj__Type_t__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Type_t _0 -> _0
let (uu___is_Univ : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____1206 -> false
let (__proj__Univ__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Unknown : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Unknown -> true | uu____1218 -> false
let (uu___is_Arrow : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrow _0 -> true | uu____1241 -> false
let (__proj__Arrow__item___0 :
  t' ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,
      ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp)) FStar_Util.either)
  = fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Refinement : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refinement _0 -> true | uu____1316 -> false
let (__proj__Refinement__item___0 :
  t' -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee -> match projectee with | Refinement _0 -> _0
let (uu___is_Reflect : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflect _0 -> true | uu____1371 -> false
let (__proj__Reflect__item___0 : t' -> t) =
  fun projectee -> match projectee with | Reflect _0 -> _0
let (uu___is_Quote : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote _0 -> true | uu____1388 -> false
let (__proj__Quote__item___0 :
  t' -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_Lazy : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy _0 -> true | uu____1427 -> false
let (__proj__Lazy__item___0 :
  t' ->
    ((FStar_Syntax_Syntax.lazyinfo,
      (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t
      FStar_Thunk.t))
  = fun projectee -> match projectee with | Lazy _0 -> _0
let (uu___is_Meta : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____1488 -> false
let (__proj__Meta__item___0 :
  t' -> (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_TopLevelLet : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu____1531 -> false
let (__proj__TopLevelLet__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_TopLevelRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelRec _0 -> true | uu____1596 -> false
let (__proj__TopLevelRec__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelRec _0 -> _0
let (uu___is_LocalLetRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalLetRec _0 -> true | uu____1683 -> false
let (__proj__LocalLetRec__item___0 :
  t' ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee -> match projectee with | LocalLetRec _0 -> _0
let (__proj__Mkt__item__nbe_t : t -> t') =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_t
let (__proj__Mkt__item__nbe_r : t -> FStar_Range.range) =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_r
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | Tot _0 -> true | uu____1794 -> false
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tot _0 -> _0
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | GTot _0 -> true | uu____1831 -> false
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | GTot _0 -> _0
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp _0 -> true | uu____1862 -> false
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStar_Syntax_Syntax.aqual) Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee -> match projectee with | TOTAL -> true | uu____1980 -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | MLEFFECT -> true | uu____1986 -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | RETURN -> true | uu____1992 -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu____1998 -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu____2004 -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TRIVIAL_POSTCONDITION -> true
    | uu____2010 -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu____2016 -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu____2022 -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu____2028 -> false
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES _0 -> true | uu____2035 -> false
let (__proj__DECREASES__item___0 : cflag -> t) =
  fun projectee -> match projectee with | DECREASES _0 -> _0
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
type arg = (t * FStar_Syntax_Syntax.aqual)
type args = (t * FStar_Syntax_Syntax.aqual) Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm ->
    match trm.nbe_t with | Accu uu____2103 -> true | uu____2114 -> false
let (isNotAccu : t -> Prims.bool) =
  fun x ->
    match x.nbe_t with
    | Accu (uu____2120, uu____2121) -> false
    | uu____2134 -> true
let (mk_rt : FStar_Range.range -> t' -> t) =
  fun r -> fun t1 -> { nbe_t = t1; nbe_r = r }
let (mk_t : t' -> t) = fun t1 -> mk_rt FStar_Range.dummyRange t1
let (nbe_t_of_t : t -> t') = fun t1 -> t1.nbe_t
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i ->
    fun us -> fun ts -> FStar_All.pipe_left mk_t (Construct (i, us, ts))
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i ->
    fun us ->
      fun ts ->
        let uu____2201 = FStar_Syntax_Syntax.range_of_fv i in
        mk_rt uu____2201 (FV (i, us, ts))
let (mkAccuVar : var -> t) =
  fun v ->
    let uu____2215 = FStar_Syntax_Syntax.range_of_bv v in
    mk_rt uu____2215 (Accu ((Var v), []))
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s -> fun bs -> FStar_All.pipe_left mk_t (Accu ((Match (s, bs)), []))
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2264 ->
    if uu___0_2264
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2270 ->
    if uu___1_2270
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.NotEqual
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1 ->
    fun r2 ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual, uu____2282) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2283, FStar_Syntax_Util.NotEqual) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown, uu____2284) -> FStar_Syntax_Util.Unknown
      | (uu____2285, FStar_Syntax_Util.Unknown) -> FStar_Syntax_Util.Unknown
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Syntax_Util.Equal -> g ()
      | uu____2301 -> FStar_Syntax_Util.Unknown
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Unit, Unit) -> FStar_Syntax_Util.Equal
      | (Bool b1, Bool b2) -> equal_iff (b1 = b2)
      | (Int i1, Int i2) -> equal_iff (i1 = i2)
      | (String (s1, uu____2317), String (s2, uu____2319)) ->
          equal_iff (s1 = s2)
      | (Char c11, Char c21) -> equal_iff (c11 = c21)
      | (Range r1, Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2324, uu____2325) -> FStar_Syntax_Util.NotEqual
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1 ->
    fun t2 ->
      match ((t1.nbe_t), (t2.nbe_t)) with
      | (Lam uu____2360, Lam uu____2361) -> FStar_Syntax_Util.Unknown
      | (Accu (a1, as1), Accu (a2, as2)) ->
          let uu____2452 = eq_atom a1 a2 in
          eq_and uu____2452 (fun uu____2454 -> eq_args as1 as2)
      | (Construct (v1, us1, args1), Construct (v2, us2, args2)) ->
          let uu____2493 = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu____2493
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2504 = FStar_List.zip args1 args2 in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc ->
                      fun uu____2561 ->
                        match uu____2561 with
                        | ((a1, uu____2575), (a2, uu____2577)) ->
                            let uu____2586 = eq_t a1 a2 in
                            eq_inj acc uu____2586) FStar_Syntax_Util.Equal)
                uu____2504))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1, us1, args1), FV (v2, us2, args2)) ->
          let uu____2626 = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu____2626
          then
            let uu____2627 =
              let uu____2628 = FStar_Syntax_Util.eq_univs_list us1 us2 in
              equal_iff uu____2628 in
            eq_and uu____2627 (fun uu____2630 -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1, Constant c2) -> eq_constant c1 c2
      | (Type_t u1, Type_t u2) ->
          let uu____2636 = FStar_Syntax_Util.eq_univs u1 u2 in
          equal_iff uu____2636
      | (Univ u1, Univ u2) ->
          let uu____2639 = FStar_Syntax_Util.eq_univs u1 u2 in
          equal_iff uu____2639
      | (Refinement (r1, t11), Refinement (r2, t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit in
          let uu____2685 =
            let uu____2686 =
              let uu____2687 = t11 () in
              FStar_Pervasives_Native.fst uu____2687 in
            let uu____2692 =
              let uu____2693 = t21 () in
              FStar_Pervasives_Native.fst uu____2693 in
            eq_t uu____2686 uu____2692 in
          eq_and uu____2685
            (fun uu____2701 ->
               let uu____2702 = let uu____2703 = mkAccuVar x in r1 uu____2703 in
               let uu____2704 = let uu____2705 = mkAccuVar x in r2 uu____2705 in
               eq_t uu____2702 uu____2704)
      | (Unknown, Unknown) -> FStar_Syntax_Util.Equal
      | (uu____2706, uu____2707) -> FStar_Syntax_Util.Unknown
and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (Var bv1, Var bv2) ->
          let uu____2712 = FStar_Syntax_Syntax.bv_eq bv1 bv2 in
          equal_if uu____2712
      | (uu____2713, uu____2714) -> FStar_Syntax_Util.Unknown
and (eq_arg : arg -> arg -> FStar_Syntax_Util.eq_result) =
  fun a1 ->
    fun a2 ->
      eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)
and (eq_args : args -> args -> FStar_Syntax_Util.eq_result) =
  fun as1 ->
    fun as2 ->
      match (as1, as2) with
      | ([], []) -> FStar_Syntax_Util.Equal
      | (x::xs, y::ys) ->
          let uu____2795 = eq_arg x y in
          eq_and uu____2795 (fun uu____2797 -> eq_args xs ys)
      | (uu____2798, uu____2799) -> FStar_Syntax_Util.Unknown
let (constant_to_string : constant -> Prims.string) =
  fun c ->
    match c with
    | Unit -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s, uu____2834) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2836 = FStar_Range.string_of_range r in
        FStar_Util.format1 "Range %s" uu____2836
    | SConst s -> FStar_Syntax_Print.const_to_string s
let rec (t_to_string : t -> Prims.string) =
  fun x ->
    match x.nbe_t with
    | Lam (b, uu____2848, arity) ->
        let uu____2900 = FStar_Util.string_of_int arity in
        FStar_Util.format1 "Lam (_, %s args)" uu____2900
    | Accu (a, l) ->
        let uu____2915 =
          let uu____2916 = atom_to_string a in
          let uu____2917 =
            let uu____2918 =
              let uu____2919 =
                let uu____2920 =
                  FStar_List.map
                    (fun x1 -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStar_String.concat "; " uu____2920 in
              FStar_String.op_Hat uu____2919 ")" in
            FStar_String.op_Hat ") (" uu____2918 in
          FStar_String.op_Hat uu____2916 uu____2917 in
        FStar_String.op_Hat "Accu (" uu____2915
    | Construct (fv, us, l) ->
        let uu____2952 =
          let uu____2953 = FStar_Syntax_Print.fv_to_string fv in
          let uu____2954 =
            let uu____2955 =
              let uu____2956 =
                let uu____2957 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____2957 in
              let uu____2960 =
                let uu____2961 =
                  let uu____2962 =
                    let uu____2963 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____2963 in
                  FStar_String.op_Hat uu____2962 "]" in
                FStar_String.op_Hat "] [" uu____2961 in
              FStar_String.op_Hat uu____2956 uu____2960 in
            FStar_String.op_Hat ") [" uu____2955 in
          FStar_String.op_Hat uu____2953 uu____2954 in
        FStar_String.op_Hat "Construct (" uu____2952
    | FV (fv, us, l) ->
        let uu____2995 =
          let uu____2996 = FStar_Syntax_Print.fv_to_string fv in
          let uu____2997 =
            let uu____2998 =
              let uu____2999 =
                let uu____3000 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____3000 in
              let uu____3003 =
                let uu____3004 =
                  let uu____3005 =
                    let uu____3006 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____3006 in
                  FStar_String.op_Hat uu____3005 "]" in
                FStar_String.op_Hat "] [" uu____3004 in
              FStar_String.op_Hat uu____2999 uu____3003 in
            FStar_String.op_Hat ") [" uu____2998 in
          FStar_String.op_Hat uu____2996 uu____2997 in
        FStar_String.op_Hat "FV (" uu____2995
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3021 = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Universe " uu____3021
    | Type_t u ->
        let uu____3023 = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Type_t " uu____3023
    | Arrow uu____3024 -> "Arrow"
    | Refinement (f, t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit in
        let t2 =
          let uu____3065 = t1 () in FStar_Pervasives_Native.fst uu____3065 in
        let uu____3070 =
          let uu____3071 = FStar_Syntax_Print.bv_to_string x1 in
          let uu____3072 =
            let uu____3073 =
              let uu____3074 = t_to_string t2 in
              let uu____3075 =
                let uu____3076 =
                  let uu____3077 =
                    let uu____3078 =
                      let uu____3079 = mkAccuVar x1 in f uu____3079 in
                    t_to_string uu____3078 in
                  FStar_String.op_Hat uu____3077 "}" in
                FStar_String.op_Hat "{" uu____3076 in
              FStar_String.op_Hat uu____3074 uu____3075 in
            FStar_String.op_Hat ":" uu____3073 in
          FStar_String.op_Hat uu____3071 uu____3072 in
        FStar_String.op_Hat "Refinement " uu____3070
    | Unknown -> "Unknown"
    | Reflect t1 ->
        let uu____3081 = t_to_string t1 in
        FStar_String.op_Hat "Reflect " uu____3081
    | Quote uu____3082 -> "Quote _"
    | Lazy (FStar_Util.Inl li, uu____3088) ->
        let uu____3105 =
          let uu____3106 = FStar_Syntax_Util.unfold_lazy li in
          FStar_Syntax_Print.term_to_string uu____3106 in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3105
    | Lazy (FStar_Util.Inr (uu____3107, et), uu____3109) ->
        let uu____3126 = FStar_Syntax_Print.emb_typ_to_string et in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3126
    | LocalLetRec
        (uu____3127, l, uu____3129, uu____3130, uu____3131, uu____3132,
         uu____3133)
        ->
        let uu____3158 =
          let uu____3159 = FStar_Syntax_Print.lbs_to_string [] (true, [l]) in
          FStar_String.op_Hat uu____3159 ")" in
        FStar_String.op_Hat "LocalLetRec (" uu____3158
    | TopLevelLet (lb, uu____3163, uu____3164) ->
        let uu____3177 =
          let uu____3178 =
            let uu____3179 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu____3179 in
          FStar_String.op_Hat uu____3178 ")" in
        FStar_String.op_Hat "TopLevelLet (" uu____3177
    | TopLevelRec (lb, uu____3181, uu____3182, uu____3183) ->
        let uu____3200 =
          let uu____3201 =
            let uu____3202 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu____3202 in
          FStar_String.op_Hat uu____3201 ")" in
        FStar_String.op_Hat "TopLevelRec (" uu____3200
and (atom_to_string : atom -> Prims.string) =
  fun a ->
    match a with
    | Var v ->
        let uu____3205 = FStar_Syntax_Print.bv_to_string v in
        FStar_String.op_Hat "Var " uu____3205
    | Match (t1, uu____3207) ->
        let uu____3218 = t_to_string t1 in
        FStar_String.op_Hat "Match " uu____3218
    | UnreducedLet (var1, typ, def, body, lb) ->
        let uu____3236 =
          let uu____3237 = FStar_Syntax_Print.lbs_to_string [] (false, [lb]) in
          FStar_String.op_Hat uu____3237 " in ...)" in
        FStar_String.op_Hat "UnreducedLet(" uu____3236
    | UnreducedLetRec (uu____3240, body, lbs) ->
        let uu____3263 =
          let uu____3264 = FStar_Syntax_Print.lbs_to_string [] (true, lbs) in
          let uu____3267 =
            let uu____3268 =
              let uu____3269 = t_to_string body in
              FStar_String.op_Hat uu____3269 ")" in
            FStar_String.op_Hat " in " uu____3268 in
          FStar_String.op_Hat uu____3264 uu____3267 in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3263
    | UVar uu____3270 -> "UVar"
let (arg_to_string : arg -> Prims.string) =
  fun a ->
    let uu____3278 = FStar_All.pipe_right a FStar_Pervasives_Native.fst in
    FStar_All.pipe_right uu____3278 t_to_string
let (args_to_string : args -> Prims.string) =
  fun args1 ->
    let uu____3288 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____3288 (FStar_String.concat " ")
type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStar_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> iapp
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> translate
let (iapp_cb : nbe_cbs -> t -> args -> t) =
  fun cbs -> fun h -> fun a -> cbs.iapp h a
let (translate_cb : nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun cbs -> fun t1 -> cbs.translate t1
type 'a embedding =
  {
  em: nbe_cbs -> 'a -> t ;
  un: nbe_cbs -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> un
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> typ
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; typ; emb_typ;_} -> emb_typ
let embed : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun e -> fun cb -> fun x -> e.em cb x
let unembed :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun e -> fun cb -> fun trm -> e.un cb trm
let type_of : 'a . 'a embedding -> t = fun e -> e.typ
let mk_emb :
  'a .
    (nbe_cbs -> 'a -> t) ->
      (nbe_cbs -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  = fun em -> fun un -> fun typ -> fun et -> { em; un; typ; emb_typ = et }
let mk_emb' :
  'uuuuuu3730 .
    (nbe_cbs -> 'uuuuuu3730 -> t') ->
      (nbe_cbs -> t' -> 'uuuuuu3730 FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'uuuuuu3730 embedding
  =
  fun em ->
    fun un ->
      mk_emb
        (fun cbs ->
           fun t1 ->
             let uu____3780 = em cbs t1 in
             FStar_All.pipe_left mk_t uu____3780)
        (fun cbs -> fun t1 -> un cbs t1.nbe_t)
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) -> t FStar_Pervasives_Native.option -> 'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun ot ->
          mk_emb
            (fun cbs ->
               fun x -> let uu____3844 = ba x in embed ea cbs uu____3844)
            (fun cbs ->
               fun t1 ->
                 let uu____3850 = unembed ea cbs t1 in
                 FStar_Util.map_opt uu____3850 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None -> ea.typ) ea.emb_typ
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu____3874 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        mkConstruct uu____3874 us args1
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu____3894 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        mkFV uu____3894 us args1
let (as_iarg : t -> arg) =
  fun a -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
let (as_arg : t -> arg) = fun a -> (a, FStar_Pervasives_Native.None)
let (make_arrow1 : t -> arg -> t) =
  fun t1 ->
    fun a ->
      FStar_All.pipe_left mk_t
        (Arrow
           (FStar_Util.Inr ([a], (Tot (t1, FStar_Pervasives_Native.None)))))
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et ->
    fun x ->
      fun f ->
        (let uu____3973 = FStar_ST.op_Bang FStar_Options.debug_embedding in
         if uu____3973
         then
           let uu____3980 = FStar_Syntax_Print.emb_typ_to_string et in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3980
         else ());
        (let uu____3982 = FStar_ST.op_Bang FStar_Options.eager_embedding in
         if uu____3982
         then f ()
         else
           (let thunk = FStar_Thunk.mk f in
            let li = let uu____3998 = FStar_Dyn.mkdyn x in (uu____3998, et) in
            FStar_All.pipe_left mk_t (Lazy ((FStar_Util.Inr li), thunk))))
let lazy_unembed :
  'uuuuuu4025 'a .
    'uuuuuu4025 ->
      FStar_Syntax_Syntax.emb_typ ->
        t ->
          (t -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun cb ->
    fun et ->
      fun x ->
        fun f ->
          match x.nbe_t with
          | Lazy (FStar_Util.Inl li, thunk) ->
              let uu____4076 = FStar_Thunk.force thunk in f uu____4076
          | Lazy (FStar_Util.Inr (b, et'), thunk) ->
              let uu____4096 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding) in
              if uu____4096
              then
                let res =
                  let uu____4108 = FStar_Thunk.force thunk in f uu____4108 in
                ((let uu____4110 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____4110
                  then
                    let uu____4117 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____4118 = FStar_Syntax_Print.emb_typ_to_string et' in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4117
                      uu____4118
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b in
                 (let uu____4123 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____4123
                  then
                    let uu____4130 = FStar_Syntax_Print.emb_typ_to_string et in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4130
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____4132 ->
              let aopt = f x in
              ((let uu____4137 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____4137
                then
                  let uu____4144 = FStar_Syntax_Print.emb_typ_to_string et in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4144
                else ());
               aopt)
let (mk_any_emb : t -> t embedding) =
  fun ty ->
    let em _cb a = a in
    let un _cb t1 = FStar_Pervasives_Native.Some t1 in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
let (e_any : t embedding) =
  let em _cb a = a in
  let un _cb t1 = FStar_Pervasives_Native.Some t1 in
  let uu____4207 = lid_as_typ FStar_Parser_Const.term_lid [] [] in
  mk_emb em un uu____4207 FStar_Syntax_Syntax.ET_abstract
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit in
  let un _cb t1 = FStar_Pervasives_Native.Some () in
  let uu____4240 = lid_as_typ FStar_Parser_Const.unit_lid [] [] in
  let uu____4245 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu____4240 uu____4245
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a) in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4277 -> FStar_Pervasives_Native.None in
  let uu____4278 = lid_as_typ FStar_Parser_Const.bool_lid [] [] in
  let uu____4283 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu____4278 uu____4283
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c) in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4315 -> FStar_Pervasives_Native.None in
  let uu____4316 = lid_as_typ FStar_Parser_Const.char_lid [] [] in
  let uu____4321 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char in
  mk_emb' em un uu____4316 uu____4321
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange)) in
  let un _cb s =
    match s with
    | Constant (String (s1, uu____4353)) -> FStar_Pervasives_Native.Some s1
    | uu____4354 -> FStar_Pervasives_Native.None in
  let uu____4355 = lid_as_typ FStar_Parser_Const.string_lid [] [] in
  let uu____4360 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string in
  mk_emb' em un uu____4355 uu____4360
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c) in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4392 -> FStar_Pervasives_Native.None in
  let uu____4393 = lid_as_typ FStar_Parser_Const.int_lid [] [] in
  let uu____4398 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int in
  mk_emb' em un uu____4393 uu____4398
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let etyp =
      let uu____4418 =
        let uu____4425 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____4425, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____4418 in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4447 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____4448 =
                 let uu____4449 =
                   let uu____4454 = type_of ea in as_iarg uu____4454 in
                 [uu____4449] in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4448
           | FStar_Pervasives_Native.Some x ->
               let uu____4464 =
                 let uu____4465 =
                   let uu____4470 = embed ea cb x in as_arg uu____4470 in
                 let uu____4471 =
                   let uu____4478 =
                     let uu____4483 = type_of ea in as_iarg uu____4483 in
                   [uu____4478] in
                 uu____4465 :: uu____4471 in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4464) in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fvar, us, args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar, us, (a1, uu____4550)::uu____4551::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____4578 = unembed ea cb a1 in
               FStar_Util.bind_opt uu____4578
                 (fun a2 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____4587 -> FStar_Pervasives_Native.None) in
    let uu____4590 =
      let uu____4591 =
        let uu____4592 = let uu____4597 = type_of ea in as_arg uu____4597 in
        [uu____4592] in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4591 in
    mk_emb em un uu____4590 etyp
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp =
        let uu____4643 =
          let uu____4650 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____4650, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____4643 in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4678 ->
             let uu____4679 =
               let uu____4680 =
                 let uu____4685 = embed eb cb (FStar_Pervasives_Native.snd x) in
                 as_arg uu____4685 in
               let uu____4686 =
                 let uu____4693 =
                   let uu____4698 =
                     embed ea cb (FStar_Pervasives_Native.fst x) in
                   as_arg uu____4698 in
                 let uu____4699 =
                   let uu____4706 =
                     let uu____4711 = type_of eb in as_iarg uu____4711 in
                   let uu____4712 =
                     let uu____4719 =
                       let uu____4724 = type_of ea in as_iarg uu____4724 in
                     [uu____4719] in
                   uu____4706 :: uu____4712 in
                 uu____4693 :: uu____4699 in
               uu____4680 :: uu____4686 in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4679) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct
                 (fvar, us,
                  (b1, uu____4792)::(a1, uu____4794)::uu____4795::uu____4796::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4835 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu____4835
                   (fun a2 ->
                      let uu____4845 = unembed eb cb b1 in
                      FStar_Util.bind_opt uu____4845
                        (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____4858 -> FStar_Pervasives_Native.None) in
      let uu____4863 =
        let uu____4864 =
          let uu____4865 = let uu____4870 = type_of eb in as_arg uu____4870 in
          let uu____4871 =
            let uu____4878 = let uu____4883 = type_of ea in as_arg uu____4883 in
            [uu____4878] in
          uu____4865 :: uu____4871 in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4864 in
      mk_emb em un uu____4863 etyp
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let etyp =
        let uu____4935 =
          let uu____4942 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____4942, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____4935 in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4971 ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____4973 =
                   let uu____4974 =
                     let uu____4979 = embed ea cb a1 in as_arg uu____4979 in
                   let uu____4980 =
                     let uu____4987 =
                       let uu____4992 = type_of eb in as_iarg uu____4992 in
                     let uu____4993 =
                       let uu____5000 =
                         let uu____5005 = type_of ea in as_iarg uu____5005 in
                       [uu____5000] in
                     uu____4987 :: uu____4993 in
                   uu____4974 :: uu____4980 in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4973
             | FStar_Util.Inr b1 ->
                 let uu____5023 =
                   let uu____5024 =
                     let uu____5029 = embed eb cb b1 in as_arg uu____5029 in
                   let uu____5030 =
                     let uu____5037 =
                       let uu____5042 = type_of eb in as_iarg uu____5042 in
                     let uu____5043 =
                       let uu____5050 =
                         let uu____5055 = type_of ea in as_iarg uu____5055 in
                       [uu____5050] in
                     uu____5037 :: uu____5043 in
                   uu____5024 :: uu____5030 in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5023) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct
                 (fvar, us, (a1, uu____5117)::uu____5118::uu____5119::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5154 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu____5154
                   (fun a2 ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar, us, (b1, uu____5170)::uu____5171::uu____5172::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5207 = unembed eb cb b1 in
                 FStar_Util.bind_opt uu____5207
                   (fun b2 ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____5220 -> FStar_Pervasives_Native.None) in
      let uu____5225 =
        let uu____5226 =
          let uu____5227 = let uu____5232 = type_of eb in as_arg uu____5232 in
          let uu____5233 =
            let uu____5240 = let uu____5245 = type_of ea in as_arg uu____5245 in
            [uu____5240] in
          uu____5227 :: uu____5233 in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5226 in
      mk_emb em un uu____5225 etyp
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r) in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5293 -> FStar_Pervasives_Native.None in
  let uu____5294 = lid_as_typ FStar_Parser_Const.range_lid [] [] in
  let uu____5299 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range in
  mk_emb' em un uu____5294 uu____5299
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let etyp =
      let uu____5319 =
        let uu____5326 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____5326, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____5319 in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5350 ->
           let typ = let uu____5352 = type_of ea in as_iarg uu____5352 in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ] in
           let cons hd tl =
             let uu____5373 =
               let uu____5374 = as_arg tl in
               let uu____5379 =
                 let uu____5386 =
                   let uu____5391 = embed ea cb hd in as_arg uu____5391 in
                 [uu____5386; typ] in
               uu____5374 :: uu____5379 in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5373 in
           FStar_List.fold_right cons l nil) in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fv, uu____5439, uu____5440) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv, uu____5460,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::
                (uu____5463, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5464))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5491 = unembed ea cb hd in
               FStar_Util.bind_opt uu____5491
                 (fun hd1 ->
                    let uu____5499 = un cb tl in
                    FStar_Util.bind_opt uu____5499
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv, uu____5515,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5540 = unembed ea cb hd in
               FStar_Util.bind_opt uu____5540
                 (fun hd1 ->
                    let uu____5548 = un cb tl in
                    FStar_Util.bind_opt uu____5548
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____5563 -> FStar_Pervasives_Native.None) in
    let uu____5566 =
      let uu____5567 =
        let uu____5568 = let uu____5573 = type_of ea in as_arg uu____5573 in
        [uu____5568] in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5567 in
    mk_emb em un uu____5566 etyp
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5643 ->
             let uu____5644 =
               let uu____5645 =
                 let uu____5677 =
                   let uu____5698 =
                     let uu____5705 =
                       let uu____5710 = type_of eb in as_arg uu____5710 in
                     [uu____5705] in
                   FStar_Util.Inr uu____5698 in
                 ((fun tas ->
                     let uu____5767 =
                       let uu____5770 = FStar_List.hd tas in
                       unembed ea cb uu____5770 in
                     match uu____5767 with
                     | FStar_Pervasives_Native.Some a1 ->
                         let uu____5772 = f a1 in embed eb cb uu____5772
                     | FStar_Pervasives_Native.None ->
                         failwith "cannot unembed function argument"),
                   uu____5677, Prims.int_one) in
               Lam uu____5645 in
             FStar_All.pipe_left mk_t uu____5644) in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x ->
               let uu____5817 =
                 let uu____5820 =
                   let uu____5821 =
                     let uu____5822 =
                       let uu____5827 = embed ea cb x in as_arg uu____5827 in
                     [uu____5822] in
                   cb.iapp lam1 uu____5821 in
                 unembed eb cb uu____5820 in
               match uu____5817 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None ->
                   failwith "cannot unembed function result") in
        lazy_unembed cb etyp lam k in
      let uu____5840 =
        let uu____5841 = type_of ea in
        let uu____5842 = let uu____5843 = type_of eb in as_iarg uu____5843 in
        make_arrow1 uu____5841 uu____5842 in
      mk_emb em un uu____5840 etyp
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl ->
        let uu____5860 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5860 [] []
    | FStar_Syntax_Embeddings.Weak ->
        let uu____5865 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5865 [] []
    | FStar_Syntax_Embeddings.HNF ->
        let uu____5870 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5870 [] []
    | FStar_Syntax_Embeddings.Primops ->
        let uu____5875 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5875 [] []
    | FStar_Syntax_Embeddings.Delta ->
        let uu____5880 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5880 [] []
    | FStar_Syntax_Embeddings.Zeta ->
        let uu____5885 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5885 [] []
    | FStar_Syntax_Embeddings.Iota ->
        let uu____5890 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5890 [] []
    | FStar_Syntax_Embeddings.Reify ->
        let uu____5895 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5895 [] []
    | FStar_Syntax_Embeddings.NBE ->
        let uu____5900 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____5900 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5908 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____5909 =
          let uu____5910 =
            let uu____5915 =
              let uu____5916 = e_list e_string in embed uu____5916 cb l in
            as_arg uu____5915 in
          [uu____5910] in
        mkFV uu____5908 [] uu____5909
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5934 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____5935 =
          let uu____5936 =
            let uu____5941 =
              let uu____5942 = e_list e_string in embed uu____5942 cb l in
            as_arg uu____5941 in
          [uu____5936] in
        mkFV uu____5934 [] uu____5935
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5960 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____5961 =
          let uu____5962 =
            let uu____5967 =
              let uu____5968 = e_list e_string in embed uu____5968 cb l in
            as_arg uu____5967 in
          [uu____5962] in
        mkFV uu____5960 [] uu____5961 in
  let un cb t0 =
    match t0.nbe_t with
    | FV (fv, uu____5999, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv, uu____6015, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv, uu____6031, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv, uu____6047, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv, uu____6063, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv, uu____6079, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv, uu____6095, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv, uu____6111, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv, uu____6127, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv, uu____6143, (l, uu____6145)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6164 =
          let uu____6169 = e_list e_string in unembed uu____6169 cb l in
        FStar_Util.bind_opt uu____6164
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____6184 -> FStar_Pervasives_Native.Some uu____6184)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv, uu____6186, (l, uu____6188)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6207 =
          let uu____6212 = e_list e_string in unembed uu____6212 cb l in
        FStar_Util.bind_opt uu____6207
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____6227 -> FStar_Pervasives_Native.Some uu____6227)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv, uu____6229, (l, uu____6231)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6250 =
          let uu____6255 = e_list e_string in unembed uu____6255 cb l in
        FStar_Util.bind_opt uu____6250
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____6270 -> FStar_Pervasives_Native.Some uu____6270)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6271 ->
        ((let uu____6273 =
            let uu____6278 =
              let uu____6279 = t_to_string t0 in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6279 in
            (FStar_Errors.Warning_NotEmbedded, uu____6278) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6273);
         FStar_Pervasives_Native.None) in
  let uu____6280 =
    let uu____6281 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    mkFV uu____6281 [] [] in
  let uu____6286 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step in
  mk_emb em un uu____6280 uu____6286
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h -> fun _args -> h);
    translate = (fun uu____6294 -> failwith "bogus_cbs translate")
  }
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cbs)
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cbs)
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cbs)
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cbs)
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e ->
    fun a1 ->
      let uu____6356 =
        let uu____6365 = e_list e in unembed uu____6365 bogus_cbs in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____6356
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6386 ->
    match uu____6386 with
    | (a, uu____6394) ->
        (match a.nbe_t with
         | FV
             (fv1, [],
              ({ nbe_t = Constant (Int i); nbe_r = uu____6409;_}, uu____6410)::[])
             when
             let uu____6427 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             FStar_Util.ends_with uu____6427 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6432 -> FStar_Pervasives_Native.None)
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t ->
    fun n ->
      let c = embed e_int bogus_cbs n in
      let int_to_t1 args1 =
        FStar_All.pipe_left mk_t (FV (int_to_t, [], args1)) in
      let uu____6474 = let uu____6481 = as_arg c in [uu____6481] in
      int_to_t1 uu____6474
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu____6534 = f a1 in FStar_Pervasives_Native.Some uu____6534
      | uu____6535 -> FStar_Pervasives_Native.None
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____6588 = f a0 a1 in FStar_Pervasives_Native.Some uu____6588
      | uu____6589 -> FStar_Pervasives_Native.None
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu____6632 = FStar_List.map as_a args1 in lift_unary f uu____6632
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu____6686 = FStar_List.map as_a args1 in
        lift_binary f uu____6686
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    unary_op arg_as_int
      (fun x -> let uu____6715 = f x in embed e_int bogus_cbs uu____6715)
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_int
      (fun x ->
         fun y -> let uu____6741 = f x y in embed e_int bogus_cbs uu____6741)
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f ->
    unary_op arg_as_bool
      (fun x -> let uu____6760 = f x in embed e_bool bogus_cbs uu____6760)
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_bool
      (fun x ->
         fun y -> let uu____6786 = f x y in embed e_bool bogus_cbs uu____6786)
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_string
      (fun x ->
         fun y ->
           let uu____6812 = f x y in embed e_string bogus_cbs uu____6812)
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          ('a -> 'b -> 'c) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun embed_c ->
        fun f ->
          fun args1 ->
            match args1 with
            | a1::b1::[] ->
                let uu____6914 =
                  let uu____6923 = as_a a1 in
                  let uu____6926 = as_b b1 in (uu____6923, uu____6926) in
                (match uu____6914 with
                 | (FStar_Pervasives_Native.Some a2,
                    FStar_Pervasives_Native.Some b2) ->
                     let uu____6941 =
                       let uu____6942 = f a2 b2 in embed_c uu____6942 in
                     FStar_Pervasives_Native.Some uu____6941
                 | uu____6943 -> FStar_Pervasives_Native.None)
            | uu____6952 -> FStar_Pervasives_Native.None
let (list_of_string' : Prims.string -> t) =
  fun s ->
    let uu____6958 = e_list e_char in
    let uu____6963 = FStar_String.list_of_string s in
    embed uu____6958 bogus_cbs uu____6963
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l ->
    let s = FStar_String.string_of_list l in
    FStar_All.pipe_left mk_t (Constant (String (s, FStar_Range.dummyRange)))
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1 ->
    fun s2 ->
      let r = FStar_String.compare s1 s2 in
      let uu____6989 =
        let uu____6990 = FStar_Util.string_of_int r in
        FStar_BigInt.big_int_of_string uu____6990 in
      embed e_int bogus_cbs uu____6989
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7022 = arg_as_string a1 in
        (match uu____7022 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7028 = arg_as_list e_string a2 in
             (match uu____7028 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____7041 = embed e_string bogus_cbs r in
                  FStar_Pervasives_Native.Some uu____7041
              | uu____7042 -> FStar_Pervasives_Native.None)
         | uu____7047 -> FStar_Pervasives_Native.None)
    | uu____7050 -> FStar_Pervasives_Native.None
let (string_of_int : FStar_BigInt.t -> t) =
  fun i ->
    let uu____7056 = FStar_BigInt.string_of_big_int i in
    embed e_string bogus_cbs uu____7056
let (string_of_bool : Prims.bool -> t) =
  fun b -> embed e_string bogus_cbs (if b then "true" else "false")
let (string_lowercase : Prims.string -> t) =
  fun s -> embed e_string bogus_cbs (FStar_String.lowercase s)
let (string_uppercase : Prims.string -> t) =
  fun s -> embed e_string bogus_cbs (FStar_String.lowercase s)
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg ->
    fun args1 ->
      let tru = embed e_bool bogus_cbs true in
      let fal = embed e_bool bogus_cbs false in
      match args1 with
      | (_typ, uu____7092)::(a1, uu____7094)::(a2, uu____7096)::[] ->
          let uu____7113 = eq_t a1 a2 in
          (match uu____7113 with
           | FStar_Syntax_Util.Equal ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7118 -> FStar_Pervasives_Native.None)
      | uu____7119 -> failwith "Unexpected number of arguments"
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu____7132)::(_typ, uu____7134)::(a1, uu____7136)::(a2,
                                                               uu____7138)::[]
        ->
        let uu____7159 = eq_t a1 a2 in
        (match uu____7159 with
         | FStar_Syntax_Util.Equal ->
             let uu____7162 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu____7162
         | FStar_Syntax_Util.NotEqual ->
             let uu____7163 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu____7163
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu____7164 -> failwith "Unexpected number of arguments"
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu____7177)::(_v, uu____7179)::(t1, uu____7181)::(t2, uu____7183)::
        (a1, uu____7185)::(a2, uu____7187)::[] ->
        let uu____7216 =
          let uu____7217 = eq_t t1 t2 in
          let uu____7218 = eq_t a1 a2 in
          FStar_Syntax_Util.eq_inj uu____7217 uu____7218 in
        (match uu____7216 with
         | FStar_Syntax_Util.Equal ->
             let uu____7221 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu____7221
         | FStar_Syntax_Util.NotEqual ->
             let uu____7222 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu____7222
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu____7223 -> failwith "Unexpected number of arguments"
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid ->
    fun args1 ->
      let uu____7240 =
        let uu____7241 = FStar_Ident.string_of_lid lid in
        FStar_String.op_Hat "No interpretation for " uu____7241 in
      failwith uu____7240
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (a1, uu____7254)::[] ->
        let uu____7263 = unembed e_range bogus_cbs a1 in
        (match uu____7263 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7269 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu____7269
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____7270 -> failwith "Unexpected number of arguments"
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7304 = arg_as_list e_char a1 in
        (match uu____7304 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7316 = arg_as_string a2 in
             (match uu____7316 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu____7325 =
                    let uu____7326 = e_list e_string in
                    embed uu____7326 bogus_cbs r in
                  FStar_Pervasives_Native.Some uu____7325
              | uu____7333 -> FStar_Pervasives_Native.None)
         | uu____7336 -> FStar_Pervasives_Native.None)
    | uu____7341 -> FStar_Pervasives_Native.None
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7373 =
          let uu____7382 = arg_as_string a1 in
          let uu____7385 = arg_as_int a2 in (uu____7382, uu____7385) in
        (match uu____7373 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___1042_7405 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu____7409 = embed e_char bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____7409) ()
              with | uu___1041_7411 -> FStar_Pervasives_Native.None)
         | uu____7414 -> FStar_Pervasives_Native.None)
    | uu____7423 -> FStar_Pervasives_Native.None
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7455 =
          let uu____7464 = arg_as_string a1 in
          let uu____7467 = arg_as_char a2 in (uu____7464, uu____7467) in
        (match uu____7455 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___1060_7487 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu____7491 = embed e_int bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____7491) ()
              with | uu___1059_7493 -> FStar_Pervasives_Native.None)
         | uu____7496 -> FStar_Pervasives_Native.None)
    | uu____7505 -> FStar_Pervasives_Native.None
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____7546 =
          let uu____7559 = arg_as_string a1 in
          let uu____7562 = arg_as_int a2 in
          let uu____7565 = arg_as_int a3 in
          (uu____7559, uu____7562, uu____7565) in
        (match uu____7546 with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___1083_7592 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu____7596 = embed e_string bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____7596) ()
              with | uu___1082_7598 -> FStar_Pervasives_Native.None)
         | uu____7601 -> FStar_Pervasives_Native.None)
    | uu____7614 -> FStar_Pervasives_Native.None
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7673 =
          let uu____7694 = arg_as_string fn in
          let uu____7697 = arg_as_int from_line in
          let uu____7700 = arg_as_int from_col in
          let uu____7703 = arg_as_int to_line in
          let uu____7706 = arg_as_int to_col in
          (uu____7694, uu____7697, uu____7700, uu____7703, uu____7706) in
        (match uu____7673 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____7737 =
                 let uu____7738 = FStar_BigInt.to_int_fs from_l in
                 let uu____7739 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____7738 uu____7739 in
               let uu____7740 =
                 let uu____7741 = FStar_BigInt.to_int_fs to_l in
                 let uu____7742 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____7741 uu____7742 in
               FStar_Range.mk_range fn1 uu____7737 uu____7740 in
             let uu____7743 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu____7743
         | uu____7744 -> FStar_Pervasives_Native.None)
    | uu____7765 -> FStar_Pervasives_Native.None
let (division_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7797 =
          let uu____7806 = arg_as_int a1 in
          let uu____7809 = arg_as_int a2 in (uu____7806, uu____7809) in
        (match uu____7797 with
         | (FStar_Pervasives_Native.Some m, FStar_Pervasives_Native.Some n)
             ->
             let uu____7824 =
               let uu____7825 = FStar_BigInt.to_int_fs n in
               uu____7825 <> Prims.int_zero in
             if uu____7824
             then
               let uu____7828 =
                 let uu____7829 = FStar_BigInt.div_big_int m n in
                 embed e_int bogus_cbs uu____7829 in
               FStar_Pervasives_Native.Some uu____7828
             else FStar_Pervasives_Native.None
         | uu____7831 -> FStar_Pervasives_Native.None)
    | uu____7840 -> failwith "Unexpected number of arguments"
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun n_tvars ->
          fun _fv_lid ->
            fun cb ->
              let f_wrapped args1 =
                let uu____7929 = FStar_List.splitAt n_tvars args1 in
                match uu____7929 with
                | (_tvar_args, rest_args) ->
                    let uu____7978 = FStar_List.hd rest_args in
                    (match uu____7978 with
                     | (x, uu____7990) ->
                         let uu____7991 = unembed ea cb x in
                         FStar_Util.map_opt uu____7991
                           (fun x1 ->
                              let uu____7997 = f x1 in embed eb cb uu____7997)) in
              f_wrapped
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun n_tvars ->
            fun _fv_lid ->
              fun cb ->
                let f_wrapped args1 =
                  let uu____8103 = FStar_List.splitAt n_tvars args1 in
                  match uu____8103 with
                  | (_tvar_args, rest_args) ->
                      let uu____8152 = FStar_List.hd rest_args in
                      (match uu____8152 with
                       | (x, uu____8164) ->
                           let uu____8165 =
                             let uu____8170 = FStar_List.tl rest_args in
                             FStar_List.hd uu____8170 in
                           (match uu____8165 with
                            | (y, uu____8188) ->
                                let uu____8189 = unembed ea cb x in
                                FStar_Util.bind_opt uu____8189
                                  (fun x1 ->
                                     let uu____8195 = unembed eb cb y in
                                     FStar_Util.bind_opt uu____8195
                                       (fun y1 ->
                                          let uu____8201 =
                                            let uu____8202 = f x1 y1 in
                                            embed ec cb uu____8202 in
                                          FStar_Pervasives_Native.Some
                                            uu____8201)))) in
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
                  nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun n_tvars ->
              fun _fv_lid ->
                fun cb ->
                  let f_wrapped args1 =
                    let uu____8327 = FStar_List.splitAt n_tvars args1 in
                    match uu____8327 with
                    | (_tvar_args, rest_args) ->
                        let uu____8376 = FStar_List.hd rest_args in
                        (match uu____8376 with
                         | (x, uu____8388) ->
                             let uu____8389 =
                               let uu____8394 = FStar_List.tl rest_args in
                               FStar_List.hd uu____8394 in
                             (match uu____8389 with
                              | (y, uu____8412) ->
                                  let uu____8413 =
                                    let uu____8418 =
                                      let uu____8425 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____8425 in
                                    FStar_List.hd uu____8418 in
                                  (match uu____8413 with
                                   | (z, uu____8447) ->
                                       let uu____8448 = unembed ea cb x in
                                       FStar_Util.bind_opt uu____8448
                                         (fun x1 ->
                                            let uu____8454 = unembed eb cb y in
                                            FStar_Util.bind_opt uu____8454
                                              (fun y1 ->
                                                 let uu____8460 =
                                                   unembed ec cb z in
                                                 FStar_Util.bind_opt
                                                   uu____8460
                                                   (fun z1 ->
                                                      let uu____8466 =
                                                        let uu____8467 =
                                                          f x1 y1 z1 in
                                                        embed ed cb
                                                          uu____8467 in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8466)))))) in
                  f_wrapped