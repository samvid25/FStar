open Prims
let (desugar_disjunctive_pattern :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list)
  =
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
let (trans_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___82_58  ->
    match uu___82_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___83_76  ->
        match uu___83_76 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___84_83  ->
    match uu___84_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___85_92  ->
    match uu___85_92 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____95 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____99 .
    FStar_Parser_AST.imp ->
      'Auu____99 ->
        ('Auu____99,FStar_Syntax_Syntax.arg_qualifier
                      FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____119 .
    FStar_Parser_AST.imp ->
      'Auu____119 ->
        ('Auu____119,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____136 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____151 -> true
            | uu____156 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____161 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____166  in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____170 =
      let uu____171 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____171  in
    FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____178 =
        let uu____179 = unparen t  in uu____179.FStar_Parser_AST.tm  in
      match uu____178 with
      | FStar_Parser_AST.Name l ->
          let uu____181 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____181 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____187) ->
          let uu____200 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____206,uu____207) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____210,uu____211) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____216,t1) -> is_comp_type env t1
      | uu____218 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____228 =
          let uu____231 =
            let uu____232 =
              let uu____237 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____237, r)  in
            FStar_Ident.mk_ident uu____232  in
          [uu____231]  in
        FStar_All.pipe_right uu____228 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____245 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____245 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____273 =
              let uu____274 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____273  in
          let fallback uu____280 =
            match FStar_Ident.text_of_id op with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____283 = FStar_Options.ml_ish ()  in
                if uu____283
                then
                  r FStar_Parser_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____287 -> FStar_Pervasives_Native.None  in
          let uu____288 =
            let uu____295 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____295  in
          match uu____288 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____307 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____323 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____323
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____362 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____366 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____366 with | (env1,uu____378) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____381,term) ->
          let uu____383 = free_type_vars env term  in (env, uu____383)
      | FStar_Parser_AST.TAnnotated (id1,uu____389) ->
          let uu____390 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____390 with | (env1,uu____402) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____406 = free_type_vars env t  in (env, uu____406)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____413 =
        let uu____414 = unparen t  in uu____414.FStar_Parser_AST.tm  in
      match uu____413 with
      | FStar_Parser_AST.Labeled uu____417 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____427 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____427 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____440 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____447 -> []
      | FStar_Parser_AST.Uvar uu____448 -> []
      | FStar_Parser_AST.Var uu____449 -> []
      | FStar_Parser_AST.Projector uu____450 -> []
      | FStar_Parser_AST.Discrim uu____455 -> []
      | FStar_Parser_AST.Name uu____456 -> []
      | FStar_Parser_AST.Requires (t1,uu____458) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____464) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____469,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____487,ts) ->
          FStar_List.collect
            (fun uu____508  ->
               match uu____508 with | (t1,uu____516) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____517,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____525) ->
          let uu____526 = free_type_vars env t1  in
          let uu____529 = free_type_vars env t2  in
          FStar_List.append uu____526 uu____529
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____534 = free_type_vars_b env b  in
          (match uu____534 with
           | (env1,f) ->
               let uu____549 = free_type_vars env1 t1  in
               FStar_List.append f uu____549)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____558 =
            FStar_List.fold_left
              (fun uu____578  ->
                 fun binder  ->
                   match uu____578 with
                   | (env1,free) ->
                       let uu____598 = free_type_vars_b env1 binder  in
                       (match uu____598 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____558 with
           | (env1,free) ->
               let uu____629 = free_type_vars env1 body  in
               FStar_List.append free uu____629)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____638 =
            FStar_List.fold_left
              (fun uu____658  ->
                 fun binder  ->
                   match uu____658 with
                   | (env1,free) ->
                       let uu____678 = free_type_vars_b env1 binder  in
                       (match uu____678 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____638 with
           | (env1,free) ->
               let uu____709 = free_type_vars env1 body  in
               FStar_List.append free uu____709)
      | FStar_Parser_AST.Project (t1,uu____713) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____717 -> []
      | FStar_Parser_AST.Let uu____724 -> []
      | FStar_Parser_AST.LetOpen uu____745 -> []
      | FStar_Parser_AST.If uu____750 -> []
      | FStar_Parser_AST.QForall uu____757 -> []
      | FStar_Parser_AST.QExists uu____770 -> []
      | FStar_Parser_AST.Record uu____783 -> []
      | FStar_Parser_AST.Match uu____796 -> []
      | FStar_Parser_AST.TryWith uu____811 -> []
      | FStar_Parser_AST.Bind uu____826 -> []
      | FStar_Parser_AST.Quote uu____833 -> []
      | FStar_Parser_AST.Seq uu____834 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____881 =
        let uu____882 = unparen t1  in uu____882.FStar_Parser_AST.tm  in
      match uu____881 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____924 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____944 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____944  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____962 =
                     let uu____963 =
                       let uu____968 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____968)  in
                     FStar_Parser_AST.TAnnotated uu____963  in
                   FStar_Parser_AST.mk_binder uu____962 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____981 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____981  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____999 =
                     let uu____1000 =
                       let uu____1005 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1005)  in
                     FStar_Parser_AST.TAnnotated uu____1000  in
                   FStar_Parser_AST.mk_binder uu____999 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1007 =
             let uu____1008 = unparen t  in uu____1008.FStar_Parser_AST.tm
              in
           match uu____1007 with
           | FStar_Parser_AST.Product uu____1009 -> t
           | uu____1016 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1048 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1054,uu____1055) -> true
    | FStar_Parser_AST.PatVar (uu____1060,uu____1061) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1067) -> is_var_pattern p1
    | uu____1068 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1073) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1074;
           FStar_Parser_AST.prange = uu____1075;_},uu____1076)
        -> true
    | uu____1087 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1091 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1131 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1131 with
             | (name,args,uu____1162) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1188);
               FStar_Parser_AST.prange = uu____1189;_},args)
            when is_top_level1 ->
            let uu____1199 =
              let uu____1204 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1204  in
            (uu____1199, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1214);
               FStar_Parser_AST.prange = uu____1215;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1233 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1271 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1272,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1275 -> acc
      | FStar_Parser_AST.PatTvar uu____1276 -> acc
      | FStar_Parser_AST.PatOp uu____1283 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1291) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1300) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1315 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1315
      | FStar_Parser_AST.PatAscribed (pat,uu____1323) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then (Prims.parse_int "0")
           else (Prims.parse_int "1"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1361 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1389 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___86_1415  ->
    match uu___86_1415 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1422 -> failwith "Impossible"
  
let (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___87_1447  ->
        match uu___87_1447 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1463 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1463, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1468 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1468 with
             | (env1,a1) ->
                 (((let uu___111_1488 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1488.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1488.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_Syntax_DsEnv.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple4 -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1513  ->
    match uu____1513 with
    | (attrs,n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1578 =
        let uu____1593 =
          let uu____1594 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1594  in
        let uu____1595 =
          let uu____1604 =
            let uu____1611 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1611)  in
          [uu____1604]  in
        (uu____1593, uu____1595)  in
      FStar_Syntax_Syntax.Tm_app uu____1578  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1644 =
        let uu____1659 =
          let uu____1660 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1660  in
        let uu____1661 =
          let uu____1670 =
            let uu____1677 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1677)  in
          [uu____1670]  in
        (uu____1659, uu____1661)  in
      FStar_Syntax_Syntax.Tm_app uu____1644  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1720 =
            let uu____1735 =
              let uu____1736 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1736  in
            let uu____1737 =
              let uu____1746 =
                let uu____1753 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1753)  in
              let uu____1756 =
                let uu____1765 =
                  let uu____1772 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1772)  in
                [uu____1765]  in
              uu____1746 :: uu____1756  in
            (uu____1735, uu____1737)  in
          FStar_Syntax_Syntax.Tm_app uu____1720  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1803  ->
    match uu___88_1803 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1804 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1812 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1812)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____1827 =
      let uu____1828 = unparen t  in uu____1828.FStar_Parser_AST.tm  in
    match uu____1827 with
    | FStar_Parser_AST.Wild  ->
        let uu____1833 =
          let uu____1834 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1834  in
        FStar_Util.Inr uu____1833
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1845)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.strcat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____1911 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1911
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1922 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1922
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1933 =
               let uu____1938 =
                 let uu____1939 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1939
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1938)
                in
             FStar_Errors.raise_error uu____1933 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1944 ->
        let rec aux t1 univargs =
          let uu____1974 =
            let uu____1975 = unparen t1  in uu____1975.FStar_Parser_AST.tm
             in
          match uu____1974 with
          | FStar_Parser_AST.App (t2,targ,uu____1982) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2006  ->
                     match uu___89_2006 with
                     | FStar_Util.Inr uu____2011 -> true
                     | uu____2012 -> false) univargs
              then
                let uu____2017 =
                  let uu____2018 =
                    FStar_List.map
                      (fun uu___90_2027  ->
                         match uu___90_2027 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2018  in
                FStar_Util.Inr uu____2017
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2044  ->
                        match uu___91_2044 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2050 -> failwith "impossible")
                     univargs
                    in
                 let uu____2051 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2051)
          | uu____2057 ->
              let uu____2058 =
                let uu____2063 =
                  let uu____2064 =
                    let uu____2065 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2065 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2064  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2063)  in
              FStar_Errors.raise_error uu____2058 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2074 ->
        let uu____2075 =
          let uu____2080 =
            let uu____2081 =
              let uu____2082 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2082 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2081  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2080)  in
        FStar_Errors.raise_error uu____2075 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2101 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2101) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2126 = FStar_List.hd fields  in
        match uu____2126 with
        | (f,uu____2136) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2146 =
                match uu____2146 with
                | (f',uu____2152) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2154 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2154
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____2158 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2158);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 r =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2375 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2382 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2383 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2385,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2426  ->
                          match uu____2426 with
                          | (p3,uu____2436) ->
                              let uu____2437 =
                                let uu____2438 =
                                  let uu____2441 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2441 out  in
                                FStar_Util.set_is_empty uu____2438  in
                              if uu____2437
                              then
                                let uu____2446 = pat_vars p3  in
                                FStar_Util.set_union out uu____2446
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2453) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2454) -> ()
         | (true ,uu____2461) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2496 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2496 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2510 ->
               let uu____2513 = push_bv_maybe_mut e x  in
               (match uu____2513 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2600 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2616 =
                 let uu____2617 =
                   let uu____2618 =
                     let uu____2625 =
                       let uu____2626 =
                         let uu____2631 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2631, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2626  in
                     (uu____2625, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2618  in
                 {
                   FStar_Parser_AST.pat = uu____2617;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2616
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2636 = aux loc env1 p2  in
               (match uu____2636 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2690 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2695 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2695.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2695.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2690.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2697 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2702 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2702.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2702.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2697.FStar_Syntax_Syntax.p)
                          }
                      | uu____2703 when top -> p4
                      | uu____2704 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2707 =
                      match binder with
                      | LetBinder uu____2720 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2734 = close_fun env1 t  in
                            desugar_term env1 uu____2734  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2736 -> true)
                           then
                             (let uu____2737 =
                                let uu____2742 =
                                  let uu____2743 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2744 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2745 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2743 uu____2744 uu____2745
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2742)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2737)
                           else ();
                           (let uu____2747 = annot_pat_var p3 t1  in
                            (uu____2747,
                              (LocalBinder
                                 ((let uu___116_2753 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2753.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2753.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2707 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2775 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2775, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2786 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2786, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2807 = resolvex loc env1 x  in
               (match uu____2807 with
                | (loc1,env2,xbv) ->
                    let uu____2829 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2829, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2850 = resolvex loc env1 x  in
               (match uu____2850 with
                | (loc1,env2,xbv) ->
                    let uu____2872 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2872, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_Syntax_DsEnv.fail_or env1
                   (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2884 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2884, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2908;_},args)
               ->
               let uu____2914 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2955  ->
                        match uu____2955 with
                        | (loc1,env2,args1) ->
                            let uu____3003 = aux loc1 env2 arg  in
                            (match uu____3003 with
                             | (loc2,env3,uu____3032,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2914 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____3102 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3102, false))
           | FStar_Parser_AST.PatApp uu____3119 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3141 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3174  ->
                        match uu____3174 with
                        | (loc1,env2,pats1) ->
                            let uu____3206 = aux loc1 env2 pat  in
                            (match uu____3206 with
                             | (loc2,env3,uu____3231,pat1,uu____3233) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3141 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3276 =
                        let uu____3279 =
                          let uu____3284 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3284  in
                        let uu____3285 =
                          let uu____3286 =
                            let uu____3299 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3299, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3286  in
                        FStar_All.pipe_left uu____3279 uu____3285  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3331 =
                               let uu____3332 =
                                 let uu____3345 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3345, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3332  in
                             FStar_All.pipe_left (pos_r r) uu____3331) pats1
                        uu____3276
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3389 =
                 FStar_List.fold_left
                   (fun uu____3429  ->
                      fun p2  ->
                        match uu____3429 with
                        | (loc1,env2,pats) ->
                            let uu____3478 = aux loc1 env2 p2  in
                            (match uu____3478 with
                             | (loc2,env3,uu____3507,pat,uu____3509) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3389 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____3604 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3604 with
                     | (constr,uu____3626) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3629 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3631 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3631, false)))
           | FStar_Parser_AST.PatRecord [] ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____3702  ->
                         match uu____3702 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____3732  ->
                         match uu____3732 with
                         | (f,uu____3738) ->
                             let uu____3739 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3765  ->
                                       match uu____3765 with
                                       | (g,uu____3771) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3739 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3776,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3783 =
                   let uu____3784 =
                     let uu____3791 =
                       let uu____3792 =
                         let uu____3793 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3793  in
                       FStar_Parser_AST.mk_pattern uu____3792
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3791, args)  in
                   FStar_Parser_AST.PatApp uu____3784  in
                 FStar_Parser_AST.mk_pattern uu____3783
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3796 = aux loc env1 app  in
               (match uu____3796 with
                | (env2,e,b,p2,uu____3825) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3853 =
                            let uu____3854 =
                              let uu____3867 =
                                let uu___117_3868 = fv  in
                                let uu____3869 =
                                  let uu____3872 =
                                    let uu____3873 =
                                      let uu____3880 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____3880)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3873
                                     in
                                  FStar_Pervasives_Native.Some uu____3872  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3868.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3868.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3869
                                }  in
                              (uu____3867, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3854  in
                          FStar_All.pipe_left pos uu____3853
                      | uu____3907 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3957 = aux' true loc env1 p2  in
               (match uu____3957 with
                | (loc1,env2,var,p3,uu____3984) ->
                    let uu____3989 =
                      FStar_List.fold_left
                        (fun uu____4021  ->
                           fun p4  ->
                             match uu____4021 with
                             | (loc2,env3,ps1) ->
                                 let uu____4054 = aux' true loc2 env3 p4  in
                                 (match uu____4054 with
                                  | (loc3,env4,uu____4079,p5,uu____4081) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3989 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4132 ->
               let uu____4133 = aux' true loc env1 p1  in
               (match uu____4133 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4173 = aux_maybe_or env p  in
         match uu____4173 with
         | (env1,b,pats) ->
             ((let uu____4204 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4204);
              (env1, b, pats)))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____4241 =
              let uu____4242 =
                let uu____4247 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4247, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4242  in
            (env, uu____4241, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4267 =
                  let uu____4268 =
                    let uu____4273 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4273, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4268  in
                mklet uu____4267
            | FStar_Parser_AST.PatVar (x,uu____4275) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4281);
                   FStar_Parser_AST.prange = uu____4282;_},t)
                ->
                let uu____4288 =
                  let uu____4289 =
                    let uu____4294 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4295 = desugar_term env t  in
                    (uu____4294, uu____4295)  in
                  LetBinder uu____4289  in
                (env, uu____4288, [])
            | uu____4298 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4308 = desugar_data_pat env p is_mut  in
             match uu____4308 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4337;
                       FStar_Syntax_Syntax.p = uu____4338;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4343;
                       FStar_Syntax_Syntax.p = uu____4344;_}::[] -> []
                   | uu____4349 -> p1  in
                 (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun uu____4356  ->
    fun env  ->
      fun pat  ->
        let uu____4359 = desugar_data_pat env pat false  in
        match uu____4359 with | (env1,uu____4375,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4393  ->
        fun range  ->
          match uu____4393 with
          | (signedness,width) ->
              let tnm =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____4403 =
                  let uu____4404 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4404  in
                if uu____4403
                then
                  let uu____4405 =
                    let uu____4410 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4410)  in
                  FStar_Errors.log_issue range uu____4405
                else ());
               (let private_intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat ".__"
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat "."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range
                   in
                let lid1 =
                  let uu____4418 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4418 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4428) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4438 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4438 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4439 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4439.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4439.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4440 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4447 =
                        let uu____4452 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4452)
                         in
                      FStar_Errors.raise_error uu____4447 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4468 =
                  let uu____4471 =
                    let uu____4472 =
                      let uu____4487 =
                        let uu____4496 =
                          let uu____4503 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4503)  in
                        [uu____4496]  in
                      (lid1, uu____4487)  in
                    FStar_Syntax_Syntax.Tm_app uu____4472  in
                  FStar_Syntax_Syntax.mk uu____4471  in
                uu____4468 FStar_Pervasives_Native.None range))

and (desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____4542 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4542 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4588;
                              FStar_Syntax_Syntax.vars = uu____4589;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4612 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4612 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4620 =
                                 let uu____4621 =
                                   let uu____4624 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4624  in
                                 uu____4621.FStar_Syntax_Syntax.n  in
                               match uu____4620 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4640))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4641 -> msg
                             else msg  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4645 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4645 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4646 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4651 =
                      let uu____4652 =
                        let uu____4659 = mk_ref_read tm1  in
                        (uu____4659,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4652  in
                    FStar_All.pipe_left mk1 uu____4651
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4675 =
          let uu____4676 = unparen t  in uu____4676.FStar_Parser_AST.tm  in
        match uu____4675 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4677; FStar_Ident.ident = uu____4678;
              FStar_Ident.nsstr = uu____4679; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4682 ->
            let uu____4683 =
              let uu____4688 =
                let uu____4689 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4689  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4688)  in
            FStar_Errors.raise_error uu____4683 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___119_4709 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4709.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4709.FStar_Syntax_Syntax.vars)
          }  in
        let uu____4712 =
          let uu____4713 = unparen top  in uu____4713.FStar_Parser_AST.tm  in
        match uu____4712 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4714 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4765::uu____4766::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4770 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4770 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4783;_},t1::t2::[])
                  ->
                  let uu____4788 = flatten1 t1  in
                  FStar_List.append uu____4788 [t2]
              | uu____4791 -> [t]  in
            let targs =
              let uu____4795 =
                let uu____4798 = unparen top  in flatten1 uu____4798  in
              FStar_All.pipe_right uu____4795
                (FStar_List.map
                   (fun t  ->
                      let uu____4806 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4806))
               in
            let uu____4807 =
              let uu____4812 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_lid env) uu____4812
               in
            (match uu____4807 with
             | (tup,uu____4818) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4822 =
              let uu____4825 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4825  in
            FStar_All.pipe_left setpos uu____4822
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4845 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4845 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4877 = desugar_term env t  in
                             (uu____4877, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4891)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4906 =
              let uu___120_4907 = top  in
              let uu____4908 =
                let uu____4909 =
                  let uu____4916 =
                    let uu___121_4917 = top  in
                    let uu____4918 =
                      let uu____4919 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4919  in
                    {
                      FStar_Parser_AST.tm = uu____4918;
                      FStar_Parser_AST.range =
                        (uu___121_4917.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4917.FStar_Parser_AST.level)
                    }  in
                  (uu____4916, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4909  in
              {
                FStar_Parser_AST.tm = uu____4908;
                FStar_Parser_AST.range =
                  (uu___120_4907.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4907.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4906
        | FStar_Parser_AST.Construct (n1,(a,uu____4922)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4938 =
                let uu___122_4939 = top  in
                let uu____4940 =
                  let uu____4941 =
                    let uu____4948 =
                      let uu___123_4949 = top  in
                      let uu____4950 =
                        let uu____4951 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4951  in
                      {
                        FStar_Parser_AST.tm = uu____4950;
                        FStar_Parser_AST.range =
                          (uu___123_4949.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4949.FStar_Parser_AST.level)
                      }  in
                    (uu____4948, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4941  in
                {
                  FStar_Parser_AST.tm = uu____4940;
                  FStar_Parser_AST.range =
                    (uu___122_4939.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4939.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4938))
        | FStar_Parser_AST.Construct (n1,(a,uu____4954)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4969 =
              let uu___124_4970 = top  in
              let uu____4971 =
                let uu____4972 =
                  let uu____4979 =
                    let uu___125_4980 = top  in
                    let uu____4981 =
                      let uu____4982 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4982  in
                    {
                      FStar_Parser_AST.tm = uu____4981;
                      FStar_Parser_AST.range =
                        (uu___125_4980.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4980.FStar_Parser_AST.level)
                    }  in
                  (uu____4979, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4972  in
              {
                FStar_Parser_AST.tm = uu____4971;
                FStar_Parser_AST.range =
                  (uu___124_4970.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4970.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4969
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4983; FStar_Ident.ident = uu____4984;
              FStar_Ident.nsstr = uu____4985; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4988; FStar_Ident.ident = uu____4989;
              FStar_Ident.nsstr = uu____4990; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4993; FStar_Ident.ident = uu____4994;
               FStar_Ident.nsstr = uu____4995; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5013 =
              let uu____5014 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____5014  in
            mk1 uu____5013
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5015; FStar_Ident.ident = uu____5016;
              FStar_Ident.nsstr = uu____5017; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5020; FStar_Ident.ident = uu____5021;
              FStar_Ident.nsstr = uu____5022; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5025; FStar_Ident.ident = uu____5026;
              FStar_Ident.nsstr = uu____5027; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5032;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5034 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5034 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5039 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5039))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5054 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____5054 with
                | FStar_Pervasives_Native.Some uu____5063 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5068 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____5068 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5082 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5095 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5095
              | uu____5096 ->
                  let uu____5103 =
                    let uu____5108 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5108)  in
                  FStar_Errors.raise_error uu____5103
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____5111 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____5111 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5114 =
                    let uu____5119 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5119)
                     in
                  FStar_Errors.raise_error uu____5114
                    top.FStar_Parser_AST.range
              | uu____5120 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5139 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____5139 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> head2
                   | uu____5150 ->
                       let uu____5157 =
                         FStar_Util.take
                           (fun uu____5181  ->
                              match uu____5181 with
                              | (uu____5186,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____5157 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let args2 =
                              FStar_List.map
                                (fun uu____5250  ->
                                   match uu____5250 with
                                   | (t,imp) ->
                                       let te = desugar_term env t  in
                                       arg_withimp_e imp te) args1
                               in
                            let head3 =
                              if universes1 = []
                              then head2
                              else
                                mk1
                                  (FStar_Syntax_Syntax.Tm_uinst
                                     (head2, universes1))
                               in
                            mk1 (FStar_Syntax_Syntax.Tm_app (head3, args2))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____5291 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____5291 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5298 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5305 =
              FStar_List.fold_left
                (fun uu____5350  ->
                   fun b  ->
                     match uu____5350 with
                     | (env1,tparams,typs) ->
                         let uu____5407 = desugar_binder env1 b  in
                         (match uu____5407 with
                          | (xopt,t1) ->
                              let uu____5436 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5445 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5445)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____5436 with
                               | (env2,x) ->
                                   let uu____5465 =
                                     let uu____5468 =
                                       let uu____5471 =
                                         let uu____5472 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5472
                                          in
                                       [uu____5471]  in
                                     FStar_List.append typs uu____5468  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5498 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5498.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5498.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5465)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5305 with
             | (env1,uu____5522,targs) ->
                 let uu____5544 =
                   let uu____5549 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____5549
                    in
                 (match uu____5544 with
                  | (tup,uu____5555) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5566 = uncurry binders t  in
            (match uu____5566 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5598 =
                   match uu___92_5598 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5612 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5612
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5634 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5634 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5649 = desugar_binder env b  in
            (match uu____5649 with
             | (FStar_Pervasives_Native.None ,uu____5656) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5666 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5666 with
                  | ((x,uu____5672),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5679 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5679))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5699 =
              FStar_List.fold_left
                (fun uu____5719  ->
                   fun pat  ->
                     match uu____5719 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5745,t) ->
                              let uu____5747 =
                                let uu____5750 = free_type_vars env1 t  in
                                FStar_List.append uu____5750 ftvs  in
                              (env1, uu____5747)
                          | uu____5755 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5699 with
             | (uu____5760,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5772 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____5772 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5813 =
                   match uu___93_5813 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5851 =
                                 let uu____5852 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5852
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5851 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5905 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5905
                   | p::rest ->
                       let uu____5916 = desugar_binding_pat env1 p  in
                       (match uu____5916 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5940 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5945 =
                              match b with
                              | LetBinder uu____5978 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6028) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6064 =
                                          let uu____6069 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6069, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6064
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6105,uu____6106) ->
                                             let tup2 =
                                               let uu____6108 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6108
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6112 =
                                                 let uu____6115 =
                                                   let uu____6116 =
                                                     let uu____6131 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6134 =
                                                       let uu____6137 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6138 =
                                                         let uu____6141 =
                                                           let uu____6142 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6142
                                                            in
                                                         [uu____6141]  in
                                                       uu____6137 ::
                                                         uu____6138
                                                        in
                                                     (uu____6131, uu____6134)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6116
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6115
                                                  in
                                               uu____6112
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6153 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6153
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6184,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6186,pats)) ->
                                             let tupn =
                                               let uu____6225 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6225
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6235 =
                                                 let uu____6236 =
                                                   let uu____6251 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6254 =
                                                     let uu____6263 =
                                                       let uu____6272 =
                                                         let uu____6273 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6273
                                                          in
                                                       [uu____6272]  in
                                                     FStar_List.append args
                                                       uu____6263
                                                      in
                                                   (uu____6251, uu____6254)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6236
                                                  in
                                               mk1 uu____6235  in
                                             let p2 =
                                               let uu____6293 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6293
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6328 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5945 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6395,uu____6396,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6410 =
                let uu____6411 = unparen e  in uu____6411.FStar_Parser_AST.tm
                 in
              match uu____6410 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6417 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6421 ->
            let rec aux args e =
              let uu____6453 =
                let uu____6454 = unparen e  in uu____6454.FStar_Parser_AST.tm
                 in
              match uu____6453 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6467 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6467  in
                  aux (arg :: args) e1
              | uu____6480 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let tac_bind_lid =
              FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Effect"; "bind"]
                x.FStar_Ident.idRange
               in
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr
               in
            let uu____6508 =
              FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6508 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6513 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6513
             | uu____6514 ->
                 let uu____6517 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6517)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6520 =
              let uu____6521 =
                let uu____6528 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [(FStar_Pervasives_Native.None,
                               ((FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   t1.FStar_Parser_AST.range), t1))], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____6528,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6521  in
            mk1 uu____6520
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____6580 =
              let uu____6585 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____6585 then desugar_typ else desugar_term  in
            uu____6580 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6628 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6753  ->
                        match uu____6753 with
                        | (attr_opt,(p,def)) ->
                            let uu____6805 = is_app_pattern p  in
                            if uu____6805
                            then
                              let uu____6830 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6830, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6894 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6894, def1)
                               | uu____6927 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6959);
                                           FStar_Parser_AST.prange =
                                             uu____6960;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6990 =
                                            let uu____7005 =
                                              let uu____7010 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7010  in
                                            (uu____7005, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____6990, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7065) ->
                                        if top_level
                                        then
                                          let uu____7094 =
                                            let uu____7109 =
                                              let uu____7114 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7114  in
                                            (uu____7109, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7094, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7168 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7193 =
                FStar_List.fold_left
                  (fun uu____7260  ->
                     fun uu____7261  ->
                       match (uu____7260, uu____7261) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7357,uu____7358),uu____7359))
                           ->
                           let uu____7452 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7478 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____7478 with
                                  | (env2,xx) ->
                                      let uu____7497 =
                                        let uu____7500 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7500 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7497))
                             | FStar_Util.Inr l ->
                                 let uu____7508 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7508, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7452 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7193 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7640 =
                    match uu____7640 with
                    | (attrs_opt,(uu____7670,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7722 = is_comp_type env1 t  in
                                if uu____7722
                                then
                                  ((let uu____7724 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7734 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7734))
                                       in
                                    match uu____7724 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7737 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7739 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7739))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7737
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7743 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7743 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7747 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7762 =
                                let uu____7763 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7763
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7762
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l
                           in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____7817 =
                    let uu____7818 =
                      let uu____7831 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7831)  in
                    FStar_Syntax_Syntax.Tm_let uu____7818  in
                  FStar_All.pipe_left mk1 uu____7817
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let is_mutable = qual = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____7885 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7885 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7912 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7912
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7932) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7935;
                              FStar_Syntax_Syntax.p = uu____7936;_}::[] ->
                              body1
                          | uu____7941 ->
                              let uu____7944 =
                                let uu____7947 =
                                  let uu____7948 =
                                    let uu____7971 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7972 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7971, uu____7972)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7948  in
                                FStar_Syntax_Syntax.mk uu____7947  in
                              uu____7944 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____7982 =
                          let uu____7983 =
                            let uu____7996 =
                              let uu____7997 =
                                let uu____7998 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____7998]  in
                              FStar_Syntax_Subst.close uu____7997 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7996)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____7983  in
                        FStar_All.pipe_left mk1 uu____7982
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____8026 = FStar_List.hd lbs  in
            (match uu____8026 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8066 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8066
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8075 =
                let uu____8076 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8076  in
              mk1 uu____8075  in
            let uu____8077 =
              let uu____8078 =
                let uu____8101 =
                  let uu____8104 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8104
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8125 =
                  let uu____8140 =
                    let uu____8153 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8156 = desugar_term env t2  in
                    (uu____8153, FStar_Pervasives_Native.None, uu____8156)
                     in
                  let uu____8165 =
                    let uu____8180 =
                      let uu____8193 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8196 = desugar_term env t3  in
                      (uu____8193, FStar_Pervasives_Native.None, uu____8196)
                       in
                    [uu____8180]  in
                  uu____8140 :: uu____8165  in
                (uu____8101, uu____8125)  in
              FStar_Syntax_Syntax.Tm_match uu____8078  in
            mk1 uu____8077
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____8337 =
              match uu____8337 with
              | (pat,wopt,b) ->
                  let uu____8355 = desugar_match_pat env pat  in
                  (match uu____8355 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8376 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8376
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8378 =
              let uu____8379 =
                let uu____8402 = desugar_term env e  in
                let uu____8403 = FStar_List.collect desugar_branch branches
                   in
                (uu____8402, uu____8403)  in
              FStar_Syntax_Syntax.Tm_match uu____8379  in
            FStar_All.pipe_left mk1 uu____8378
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8432 = is_comp_type env t  in
              if uu____8432
              then
                let uu____8439 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8439
              else
                (let uu____8445 = desugar_term env t  in
                 FStar_Util.Inl uu____8445)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8451 =
              let uu____8452 =
                let uu____8479 = desugar_term env e  in
                (uu____8479, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8452  in
            FStar_All.pipe_left mk1 uu____8451
        | FStar_Parser_AST.Record (uu____8504,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8541 = FStar_List.hd fields  in
              match uu____8541 with | (f,uu____8553) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8595  ->
                        match uu____8595 with
                        | (g,uu____8601) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8607,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8621 =
                         let uu____8626 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8626)
                          in
                       FStar_Errors.raise_error uu____8621
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8634 =
                    let uu____8645 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____8676  ->
                              match uu____8676 with
                              | (f,uu____8686) ->
                                  let uu____8687 =
                                    let uu____8688 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8688
                                     in
                                  (uu____8687, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8645)  in
                  FStar_Parser_AST.Construct uu____8634
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8706 =
                      let uu____8707 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8707  in
                    FStar_Parser_AST.mk_term uu____8706 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8709 =
                      let uu____8722 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____8752  ->
                                match uu____8752 with
                                | (f,uu____8762) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8722)  in
                    FStar_Parser_AST.Record uu____8709  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let e = desugar_term env recterm1  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8824;
                    FStar_Syntax_Syntax.vars = uu____8825;_},args)
                 ->
                 let uu____8847 =
                   let uu____8848 =
                     let uu____8863 =
                       let uu____8864 =
                         let uu____8867 =
                           let uu____8868 =
                             let uu____8875 =
                               FStar_All.pipe_right
                                 record.FStar_Syntax_DsEnv.fields
                                 (FStar_List.map FStar_Pervasives_Native.fst)
                                in
                             ((record.FStar_Syntax_DsEnv.typename),
                               uu____8875)
                              in
                           FStar_Syntax_Syntax.Record_ctor uu____8868  in
                         FStar_Pervasives_Native.Some uu____8867  in
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            e.FStar_Syntax_Syntax.pos)
                         FStar_Syntax_Syntax.Delta_constant uu____8864
                        in
                     (uu____8863, args)  in
                   FStar_Syntax_Syntax.Tm_app uu____8848  in
                 FStar_All.pipe_left mk1 uu____8847
             | uu____8902 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____8906 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____8906 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e  in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident
                     in
                  let qual =
                    if is_rec
                    then
                      FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else FStar_Pervasives_Native.None  in
                  let uu____8925 =
                    let uu____8926 =
                      let uu____8941 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8942 =
                        let uu____8945 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8945]  in
                      (uu____8941, uu____8942)  in
                    FStar_Syntax_Syntax.Tm_app uu____8926  in
                  FStar_All.pipe_left mk1 uu____8925))
        | FStar_Parser_AST.NamedTyp (uu____8950,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.Quote e ->
            let uu____8954 =
              let uu____8955 =
                let uu____8962 =
                  let uu____8963 =
                    let uu____8970 = desugar_term env e  in (uu____8970, ())
                     in
                  FStar_Syntax_Syntax.Meta_quoted uu____8963  in
                (FStar_Syntax_Syntax.tun, uu____8962)  in
              FStar_Syntax_Syntax.Tm_meta uu____8955  in
            FStar_All.pipe_left mk1 uu____8954
        | uu____8973 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8974 ->
            let uu____8975 =
              let uu____8980 =
                let uu____8981 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____8981  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____8980)  in
            FStar_Errors.raise_error uu____8975 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8983 -> false
    | uu____8992 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8998 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____8998 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9002 -> false

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____9039  ->
              match uu____9039 with
              | (a,imp) ->
                  let uu____9052 = desugar_term env a  in
                  arg_withimp_e imp uu____9052))

and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail a err = FStar_Errors.raise_error err r  in
        let is_requires uu____9078 =
          match uu____9078 with
          | (t1,uu____9084) ->
              let uu____9085 =
                let uu____9086 = unparen t1  in
                uu____9086.FStar_Parser_AST.tm  in
              (match uu____9085 with
               | FStar_Parser_AST.Requires uu____9087 -> true
               | uu____9094 -> false)
           in
        let is_ensures uu____9102 =
          match uu____9102 with
          | (t1,uu____9108) ->
              let uu____9109 =
                let uu____9110 = unparen t1  in
                uu____9110.FStar_Parser_AST.tm  in
              (match uu____9109 with
               | FStar_Parser_AST.Ensures uu____9111 -> true
               | uu____9118 -> false)
           in
        let is_app head1 uu____9129 =
          match uu____9129 with
          | (t1,uu____9135) ->
              let uu____9136 =
                let uu____9137 = unparen t1  in
                uu____9137.FStar_Parser_AST.tm  in
              (match uu____9136 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9139;
                      FStar_Parser_AST.level = uu____9140;_},uu____9141,uu____9142)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9143 -> false)
           in
        let is_smt_pat uu____9151 =
          match uu____9151 with
          | (t1,uu____9157) ->
              let uu____9158 =
                let uu____9159 = unparen t1  in
                uu____9159.FStar_Parser_AST.tm  in
              (match uu____9158 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9162);
                             FStar_Parser_AST.range = uu____9163;
                             FStar_Parser_AST.level = uu____9164;_},uu____9165)::uu____9166::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____9205;
                             FStar_Parser_AST.level = uu____9206;_},uu____9207)::uu____9208::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9233 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9261 = head_and_args t1  in
          match uu____9261 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None)
                        in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let thunk_ens_ ens =
                     let wildpat =
                       FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                         ens.FStar_Parser_AST.range
                        in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr
                      in
                   let thunk_ens uu____9355 =
                     match uu____9355 with
                     | (e,i) ->
                         let uu____9366 = thunk_ens_ e  in (uu____9366, i)
                      in
                   let fail_lemma uu____9376 =
                     let expected_one_of =
                       ["Lemma post";
                       "Lemma (ensures post)";
                       "Lemma (requires pre) (ensures post)";
                       "Lemma post [SMTPat ...]";
                       "Lemma (ensures post) [SMTPat ...]";
                       "Lemma (ensures post) (decreases d)";
                       "Lemma (ensures post) (decreases d) [SMTPat ...]";
                       "Lemma (requires pre) (ensures post) (decreases d)";
                       "Lemma (requires pre) (ensures post) [SMTPat ...]";
                       "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                        in
                     let msg = FStar_String.concat "\n\t" expected_one_of  in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_InvalidLemmaArgument,
                         (Prims.strcat
                            "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                            msg)) t1.FStar_Parser_AST.range
                      in
                   let args1 =
                     match args with
                     | [] -> fail_lemma ()
                     | req::[] when is_requires req -> fail_lemma ()
                     | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                     | dec::[] when is_decreases dec -> fail_lemma ()
                     | ens::[] ->
                         let uu____9456 =
                           let uu____9463 =
                             let uu____9470 = thunk_ens ens  in
                             [uu____9470; nil_pat]  in
                           req_true :: uu____9463  in
                         unit_tm :: uu____9456
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9517 =
                           let uu____9524 =
                             let uu____9531 = thunk_ens ens  in
                             [uu____9531; nil_pat]  in
                           req :: uu____9524  in
                         unit_tm :: uu____9517
                     | ens::smtpat::[] when
                         (((let uu____9580 = is_requires ens  in
                            Prims.op_Negation uu____9580) &&
                             (let uu____9582 = is_smt_pat ens  in
                              Prims.op_Negation uu____9582))
                            &&
                            (let uu____9584 = is_decreases ens  in
                             Prims.op_Negation uu____9584))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9585 =
                           let uu____9592 =
                             let uu____9599 = thunk_ens ens  in
                             [uu____9599; smtpat]  in
                           req_true :: uu____9592  in
                         unit_tm :: uu____9585
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9646 =
                           let uu____9653 =
                             let uu____9660 = thunk_ens ens  in
                             [uu____9660; nil_pat; dec]  in
                           req_true :: uu____9653  in
                         unit_tm :: uu____9646
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9720 =
                           let uu____9727 =
                             let uu____9734 = thunk_ens ens  in
                             [uu____9734; smtpat; dec]  in
                           req_true :: uu____9727  in
                         unit_tm :: uu____9720
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9794 =
                           let uu____9801 =
                             let uu____9808 = thunk_ens ens  in
                             [uu____9808; nil_pat; dec]  in
                           req :: uu____9801  in
                         unit_tm :: uu____9794
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9868 =
                           let uu____9875 =
                             let uu____9882 = thunk_ens ens  in
                             [uu____9882; smtpat]  in
                           req :: uu____9875  in
                         unit_tm :: uu____9868
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9947 =
                           let uu____9954 =
                             let uu____9961 = thunk_ens ens  in
                             [uu____9961; dec; smtpat]  in
                           req :: uu____9954  in
                         unit_tm :: uu____9947
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____10023 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10023, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10051 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10051
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10069 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10069
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____10107 ->
                   let default_effect =
                     let uu____10109 = FStar_Options.ml_ish ()  in
                     if uu____10109
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10112 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10112
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____10136 = pre_process_comp_typ t  in
        match uu____10136 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10185 =
                       let uu____10190 =
                         let uu____10191 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10191
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10190)
                        in
                     fail () uu____10185)
                else Obj.repr ());
             (let is_universe uu____10200 =
                match uu____10200 with
                | (uu____10205,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10207 = FStar_Util.take is_universe args  in
              match uu____10207 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10266  ->
                         match uu____10266 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10273 =
                    let uu____10288 = FStar_List.hd args1  in
                    let uu____10297 = FStar_List.tl args1  in
                    (uu____10288, uu____10297)  in
                  (match uu____10273 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10352 =
                         let is_decrease uu____10388 =
                           match uu____10388 with
                           | (t1,uu____10398) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10408;
                                       FStar_Syntax_Syntax.vars = uu____10409;_},uu____10410::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10441 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10352 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10555  ->
                                      match uu____10555 with
                                      | (t1,uu____10565) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10574,(arg,uu____10576)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10605 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10618 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags1 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else []
                                    in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes  in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then
                                     match rest2 with
                                     | req::ens::(pat,aq)::[] ->
                                         let pat1 =
                                           match pat.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10758 -> pat  in
                                         let uu____10759 =
                                           let uu____10770 =
                                             let uu____10781 =
                                               let uu____10790 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10790, aq)  in
                                             [uu____10781]  in
                                           ens :: uu____10770  in
                                         req :: uu____10759
                                     | uu____10831 -> rest2
                                   else rest2  in
                                 FStar_Syntax_Syntax.mk_Comp
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_name = eff;
                                     FStar_Syntax_Syntax.result_typ =
                                       result_typ;
                                     FStar_Syntax_Syntax.effect_args = rest3;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags2
                                          decreases_clause)
                                   })))))

and (desugar_formula :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____10853 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10870 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10870.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10870.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10904 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10904.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10904.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10904.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10963 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10963)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10976 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____10976 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_10986 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_10986.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_10986.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11008 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11022 =
                     let uu____11025 =
                       let uu____11026 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11026]  in
                     no_annot_abs uu____11025 body2  in
                   FStar_All.pipe_left setpos uu____11022  in
                 let uu____11031 =
                   let uu____11032 =
                     let uu____11047 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11048 =
                       let uu____11051 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11051]  in
                     (uu____11047, uu____11048)  in
                   FStar_Syntax_Syntax.Tm_app uu____11032  in
                 FStar_All.pipe_left mk1 uu____11031)
        | uu____11056 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11128 = q (rest, pats, body)  in
              let uu____11135 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11128 uu____11135
                FStar_Parser_AST.Formula
               in
            let uu____11136 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11136 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11145 -> failwith "impossible"  in
      let uu____11148 =
        let uu____11149 = unparen f  in uu____11149.FStar_Parser_AST.tm  in
      match uu____11148 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11156,uu____11157) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11168,uu____11169) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11200 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11200
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11236 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11236
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____11279 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____11284 =
        FStar_List.fold_left
          (fun uu____11320  ->
             fun b  ->
               match uu____11320 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11372 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11372.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11372.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11372.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11389 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____11389 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11409 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11409.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11409.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11426 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11284 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11513 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11513)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11518 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11518)
      | FStar_Parser_AST.TVariable x ->
          let uu____11522 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11522)
      | FStar_Parser_AST.NoName t ->
          let uu____11530 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11530)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___94_11563  ->
                  match uu___94_11563 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11564 -> false))
           in
        let quals2 q =
          let uu____11575 =
            (let uu____11578 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____11578) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____11575
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11591 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11591;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____11622 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11652  ->
                        match uu____11652 with
                        | (x,uu____11660) ->
                            let uu____11661 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11661 with
                             | (field_name,uu____11669) ->
                                 let only_decl =
                                   ((let uu____11673 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11673)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11675 =
                                        let uu____11676 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____11676.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11675)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11690 =
                                       FStar_List.filter
                                         (fun uu___95_11694  ->
                                            match uu___95_11694 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11695 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11690
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11708  ->
                                             match uu___96_11708 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11709 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11717 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11717
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11722 =
                                        let uu____11727 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11727  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11722;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = []
                                      }  in
                                    let impl =
                                      let uu____11731 =
                                        let uu____11732 =
                                          let uu____11739 =
                                            let uu____11742 =
                                              let uu____11743 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11743
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11742]  in
                                          ((false, [lb]), uu____11739)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11732
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11731;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11622 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11787,t,uu____11789,n1,uu____11791) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11796 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11796 with
             | (formals,uu____11812) ->
                 (match formals with
                  | [] -> []
                  | uu____11835 ->
                      let filter_records uu___97_11847 =
                        match uu___97_11847 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11850,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11862 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11864 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11864 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11874 = FStar_Util.first_N n1 formals  in
                      (match uu____11874 with
                       | (uu____11897,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11923 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____11973 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____11973
                    then
                      let uu____11976 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____11976
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____11979 =
                      let uu____11984 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____11984  in
                    let uu____11985 =
                      let uu____11988 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____11988  in
                    let uu____11991 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11979;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11985;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11991;
                      FStar_Syntax_Syntax.lbattrs = []
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
  
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___98_12038 =
            match uu___98_12038 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12040,uu____12041) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12051,uu____12052,uu____12053) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12063,uu____12064,uu____12065) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12095,uu____12096,uu____12097) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12139) ->
                let uu____12140 =
                  let uu____12141 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12141  in
                FStar_Parser_AST.mk_term uu____12140 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12143 =
                  let uu____12144 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12144  in
                FStar_Parser_AST.mk_term uu____12143 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12146) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____12169 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12175 =
                     let uu____12176 =
                       let uu____12183 = binder_to_term b  in
                       (out, uu____12183, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12176  in
                   FStar_Parser_AST.mk_term uu____12175
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12193 =
            match uu___99_12193 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12248  ->
                       match uu____12248 with
                       | (x,t,uu____12259) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12265 =
                    let uu____12266 =
                      let uu____12267 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12267  in
                    FStar_Parser_AST.mk_term uu____12266
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12265 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12271 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12298  ->
                          match uu____12298 with
                          | (x,uu____12308,uu____12309) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12271)
            | uu____12362 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12393 =
            match uu___100_12393 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12417 = typars_of_binders _env binders  in
                (match uu____12417 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12463 =
                         let uu____12464 =
                           let uu____12465 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12465  in
                         FStar_Parser_AST.mk_term uu____12464
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12463 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____12478 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12522 =
              FStar_List.fold_left
                (fun uu____12562  ->
                   fun uu____12563  ->
                     match (uu____12562, uu____12563) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12654 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12654 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12522 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12767 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12767
                | uu____12768 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12776 = desugar_abstract_tc quals env [] tc  in
              (match uu____12776 with
               | (uu____12789,uu____12790,se,uu____12792) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12795,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12812 =
                                 let uu____12813 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12813  in
                               if uu____12812
                               then
                                 let uu____12814 =
                                   let uu____12819 =
                                     let uu____12820 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12820
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12819)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12814
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12827 ->
                               let uu____12828 =
                                 let uu____12831 =
                                   let uu____12832 =
                                     let uu____12845 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12845)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12832
                                    in
                                 FStar_Syntax_Syntax.mk uu____12831  in
                               uu____12828 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12849 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12849.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12849.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12849.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12852 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____12855 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____12855
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12870 = typars_of_binders env binders  in
              (match uu____12870 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12906 =
                           FStar_Util.for_some
                             (fun uu___101_12908  ->
                                match uu___101_12908 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12909 -> false) quals
                            in
                         if uu____12906
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12916 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_12920  ->
                               match uu___102_12920 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12921 -> false))
                        in
                     if uu____12916
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____12930 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12930
                     then
                       let uu____12933 =
                         let uu____12940 =
                           let uu____12941 = unparen t  in
                           uu____12941.FStar_Parser_AST.tm  in
                         match uu____12940 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12962 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12992)::args_rev ->
                                   let uu____13004 =
                                     let uu____13005 = unparen last_arg  in
                                     uu____13005.FStar_Parser_AST.tm  in
                                   (match uu____13004 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13033 -> ([], args))
                               | uu____13042 -> ([], args)  in
                             (match uu____12962 with
                              | (cattributes,args1) ->
                                  let uu____13081 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13081))
                         | uu____13092 -> (t, [])  in
                       match uu____12933 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___103_13114  ->
                                     match uu___103_13114 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13115 -> true))
                              in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13126)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13150 = tycon_record_as_variant trec  in
              (match uu____13150 with
               | (t,fs) ->
                   let uu____13167 =
                     let uu____13170 =
                       let uu____13171 =
                         let uu____13180 =
                           let uu____13183 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____13183  in
                         (uu____13180, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13171  in
                     uu____13170 :: quals  in
                   desugar_tycon env d uu____13167 [t])
          | uu____13188::uu____13189 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13350 = et  in
                match uu____13350 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13575 ->
                         let trec = tc  in
                         let uu____13599 = tycon_record_as_variant trec  in
                         (match uu____13599 with
                          | (t,fs) ->
                              let uu____13658 =
                                let uu____13661 =
                                  let uu____13662 =
                                    let uu____13671 =
                                      let uu____13674 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13674  in
                                    (uu____13671, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13662
                                   in
                                uu____13661 :: quals1  in
                              collect_tcs uu____13658 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13761 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13761 with
                          | (env2,uu____13821,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____13970 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13970 with
                          | (env2,uu____14030,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14155 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14202 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14202 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14713  ->
                             match uu___105_14713 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14780,uu____14781);
                                    FStar_Syntax_Syntax.sigrng = uu____14782;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14783;
                                    FStar_Syntax_Syntax.sigmeta = uu____14784;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14785;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14846 =
                                     typars_of_binders env1 binders  in
                                   match uu____14846 with
                                   | (env2,tpars1) ->
                                       let uu____14877 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14877 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____14910 =
                                   let uu____14931 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____14931)
                                    in
                                 [uu____14910]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14999);
                                    FStar_Syntax_Syntax.sigrng = uu____15000;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15002;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15003;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____15099 = push_tparams env1 tpars
                                    in
                                 (match uu____15099 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15176  ->
                                             match uu____15176 with
                                             | (x,uu____15190) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15198 =
                                        let uu____15227 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15341  ->
                                                  match uu____15341 with
                                                  | (id1,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____15397 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15397
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___104_15408
                                                                 ->
                                                                match uu___104_15408
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15420
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15428 =
                                                        let uu____15449 =
                                                          let uu____15450 =
                                                            let uu____15451 =
                                                              let uu____15466
                                                                =
                                                                let uu____15469
                                                                  =
                                                                  let uu____15472
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15472
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15469
                                                                 in
                                                              (name, univs1,
                                                                uu____15466,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15451
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15450;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____15449)
                                                         in
                                                      (name, uu____15428)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15227
                                         in
                                      (match uu____15198 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 []
                                             })
                                           :: constrs1))
                             | uu____15711 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15843  ->
                             match uu____15843 with
                             | (name_doc,uu____15871,uu____15872) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15952  ->
                             match uu____15952 with
                             | (uu____15973,uu____15974,se) -> se))
                      in
                   let uu____16004 =
                     let uu____16011 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16011 rng
                      in
                   (match uu____16004 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16077  ->
                                  match uu____16077 with
                                  | (uu____16100,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16151,tps,k,uu____16154,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____16173 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16190  ->
                                 match uu____16190 with
                                 | (lid,doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      let uu____16225 =
        FStar_List.fold_left
          (fun uu____16248  ->
             fun b  ->
               match uu____16248 with
               | (env1,binders1) ->
                   let uu____16268 = desugar_binder env1 b  in
                   (match uu____16268 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16285 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16285 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16302 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16225 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____16347 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16352  ->
                    match uu___106_16352 with
                    | FStar_Syntax_Syntax.Reflectable uu____16353 -> true
                    | uu____16354 -> false))
             in
          if uu____16347
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                let uu____16453 = desugar_binders monad_env eff_binders  in
                match uu____16453 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16474 =
                        let uu____16475 =
                          let uu____16482 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16482  in
                        FStar_List.length uu____16475  in
                      uu____16474 = (Prims.parse_int "1")  in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"]  in
                      if for_free
                      then rr_members
                      else
                        FStar_List.append rr_members
                          ["return_wp";
                          "bind_wp";
                          "if_then_else";
                          "ite_wp";
                          "stronger";
                          "close_wp";
                          "assert_p";
                          "assume_p";
                          "null_wp";
                          "trivial"]
                       in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____16524,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16526,uu____16527,uu____16528),uu____16529)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16562 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16563 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16575 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16575 mandatory_members)
                        eff_decls
                       in
                    (match uu____16563 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16592 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16621  ->
                                   fun decl  ->
                                     match uu____16621 with
                                     | (env2,out) ->
                                         let uu____16641 =
                                           desugar_decl env2 decl  in
                                         (match uu____16641 with
                                          | (env3,ses) ->
                                              let uu____16654 =
                                                let uu____16657 =
                                                  FStar_List.hd ses  in
                                                uu____16657 :: out  in
                                              (env3, uu____16654)))
                                (env1, []))
                            in
                         (match uu____16592 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16725,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16728,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16729,
                                                                (def,uu____16731)::
                                                                (cps_type,uu____16733)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16734;
                                                             FStar_Parser_AST.level
                                                               = uu____16735;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16787 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16787 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16807 =
                                                   let uu____16808 =
                                                     FStar_Syntax_DsEnv.qualify
                                                       env3 name
                                                      in
                                                   let uu____16809 =
                                                     let uu____16810 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16810
                                                      in
                                                   let uu____16815 =
                                                     let uu____16816 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16816
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16808;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16809;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16815
                                                   }  in
                                                 (uu____16807, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16823,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16826,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16861 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16861 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16881 =
                                                   let uu____16882 =
                                                     FStar_Syntax_DsEnv.qualify
                                                       env3 name
                                                      in
                                                   let uu____16883 =
                                                     let uu____16884 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16884
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16882;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16883;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16881, doc1))
                                        | uu____16891 ->
                                            FStar_Errors.raise_error
                                              (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                              d1.FStar_Parser_AST.drange))
                                 in
                              let actions1 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  actions_docs
                                 in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup1 s =
                                let l =
                                  FStar_Syntax_DsEnv.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____16921 =
                                  let uu____16922 =
                                    FStar_Syntax_DsEnv.fail_or env2
                                      (FStar_Syntax_DsEnv.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16922
                                   in
                                ([], uu____16921)  in
                              let mname =
                                FStar_Syntax_DsEnv.qualify env0 eff_name  in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (FStar_Pervasives_Native.Some mname))
                                  quals
                                 in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____16939 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16939)  in
                                  let uu____16946 =
                                    let uu____16947 =
                                      let uu____16948 =
                                        let uu____16949 = lookup1 "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16949
                                         in
                                      let uu____16958 = lookup1 "return"  in
                                      let uu____16959 = lookup1 "bind"  in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.signature =
                                          eff_t1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.bind_wp =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.if_then_else =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.ite_wp =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.stronger =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.close_wp =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.assert_p =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.assume_p =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.null_wp =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.trivial =
                                          dummy_tscheme;
                                        FStar_Syntax_Syntax.repr =
                                          uu____16948;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16958;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16959;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16947
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16946;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___107_16963  ->
                                          match uu___107_16963 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16964 -> true
                                          | uu____16965 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____16975 =
                                     let uu____16976 =
                                       let uu____16977 = lookup1 "return_wp"
                                          in
                                       let uu____16978 = lookup1 "bind_wp"
                                          in
                                       let uu____16979 =
                                         lookup1 "if_then_else"  in
                                       let uu____16980 = lookup1 "ite_wp"  in
                                       let uu____16981 = lookup1 "stronger"
                                          in
                                       let uu____16982 = lookup1 "close_wp"
                                          in
                                       let uu____16983 = lookup1 "assert_p"
                                          in
                                       let uu____16984 = lookup1 "assume_p"
                                          in
                                       let uu____16985 = lookup1 "null_wp"
                                          in
                                       let uu____16986 = lookup1 "trivial"
                                          in
                                       let uu____16987 =
                                         if rr
                                         then
                                           let uu____16988 = lookup1 "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16988
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____17004 =
                                         if rr
                                         then lookup1 "return"
                                         else un_ts  in
                                       let uu____17006 =
                                         if rr then lookup1 "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16977;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16978;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16979;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16980;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16981;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16982;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16983;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16984;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16985;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16986;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16987;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____17004;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____17006;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16976
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16975;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   })
                                 in
                              let env3 =
                                FStar_Syntax_DsEnv.push_sigelt env0 se  in
                              let env4 =
                                FStar_Syntax_DsEnv.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____17031  ->
                                          match uu____17031 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17045 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_Syntax_DsEnv.push_sigelt
                                                  env5 uu____17045
                                                 in
                                              FStar_Syntax_DsEnv.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                push_reflect_effect env5 qualifiers mname
                                  d.FStar_Parser_AST.drange
                                 in
                              let env7 =
                                FStar_Syntax_DsEnv.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____17069 = desugar_binders env1 eff_binders  in
                match uu____17069 with
                | (env2,binders) ->
                    let uu____17088 =
                      let uu____17107 = head_and_args defn  in
                      match uu____17107 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17152 ->
                                let uu____17153 =
                                  let uu____17158 =
                                    let uu____17159 =
                                      let uu____17160 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17160 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17159  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17158)
                                   in
                                FStar_Errors.raise_error uu____17153
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17162 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17192)::args_rev ->
                                let uu____17204 =
                                  let uu____17205 = unparen last_arg  in
                                  uu____17205.FStar_Parser_AST.tm  in
                                (match uu____17204 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17233 -> ([], args))
                            | uu____17242 -> ([], args)  in
                          (match uu____17162 with
                           | (cattributes,args1) ->
                               let uu____17293 = desugar_args env2 args1  in
                               let uu____17302 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17293, uu____17302))
                       in
                    (match uu____17088 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____17358 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17358 with
                           | (ed_binders,uu____17372,ed_binders_opening) ->
                               let sub1 uu____17383 =
                                 match uu____17383 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17397 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17397 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17401 =
                                       let uu____17402 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17402)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17401
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17407 =
                                   let uu____17408 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17408
                                    in
                                 let uu____17419 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17420 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17421 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17422 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17423 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17424 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17425 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17426 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17427 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17428 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17429 =
                                   let uu____17430 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17430
                                    in
                                 let uu____17441 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17442 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17443 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17451 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17452 =
                                          let uu____17453 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17453
                                           in
                                        let uu____17464 =
                                          let uu____17465 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17465
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17451;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17452;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17464
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____17407;
                                   FStar_Syntax_Syntax.ret_wp = uu____17419;
                                   FStar_Syntax_Syntax.bind_wp = uu____17420;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17421;
                                   FStar_Syntax_Syntax.ite_wp = uu____17422;
                                   FStar_Syntax_Syntax.stronger = uu____17423;
                                   FStar_Syntax_Syntax.close_wp = uu____17424;
                                   FStar_Syntax_Syntax.assert_p = uu____17425;
                                   FStar_Syntax_Syntax.assume_p = uu____17426;
                                   FStar_Syntax_Syntax.null_wp = uu____17427;
                                   FStar_Syntax_Syntax.trivial = uu____17428;
                                   FStar_Syntax_Syntax.repr = uu____17429;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17441;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17442;
                                   FStar_Syntax_Syntax.actions = uu____17443
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17478 =
                                     let uu____17479 =
                                       let uu____17486 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17486
                                        in
                                     FStar_List.length uu____17479  in
                                   uu____17478 = (Prims.parse_int "1")  in
                                 let uu____17515 =
                                   let uu____17518 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17518 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (if for_free
                                      then
                                        FStar_Syntax_Syntax.Sig_new_effect_for_free
                                          ed1
                                      else
                                        FStar_Syntax_Syntax.Sig_new_effect
                                          ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____17515;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____17538 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____17538
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17540 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17540
                                 then
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____17555 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17555 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17606 ->
              let uu____17607 =
                let uu____17608 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17608
                 in
              Prims.strcat "\n  " uu____17607
          | uu____17609 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17622  ->
               match uu____17622 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text))
           in
        let fv =
          let uu____17640 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17640
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17642 =
          let uu____17651 = FStar_Syntax_Syntax.as_arg arg  in [uu____17651]
           in
        FStar_Syntax_Util.mk_app fv uu____17642

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____17658 = desugar_decl_noattrs env d  in
      match uu____17658 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17678 = mk_comment_attr d  in uu____17678 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17689 =
                     let uu____17690 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17690  in
                   Prims.strcat s uu____17689) "" attrs2
             in
          let uu____17691 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17697 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17697.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17697.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17697.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17697.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17691)

and (desugar_decl_noattrs :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17723 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17739 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____17739, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17778  ->
                 match uu____17778 with | (x,uu____17786) -> x) tcs
             in
          let uu____17791 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17791 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17813;
                    FStar_Parser_AST.prange = uu____17814;_},uu____17815)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17824;
                    FStar_Parser_AST.prange = uu____17825;_},uu____17826)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17841;
                         FStar_Parser_AST.prange = uu____17842;_},uu____17843);
                    FStar_Parser_AST.prange = uu____17844;_},uu____17845)::[]
                   -> false
               | (p,uu____17861)::[] ->
                   let uu____17870 = is_app_pattern p  in
                   Prims.op_Negation uu____17870
               | uu____17871 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____17945 =
              let uu____17946 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____17946.FStar_Syntax_Syntax.n  in
            (match uu____17945 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17954) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____17987::uu____17988 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17991 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18005  ->
                               match uu___108_18005 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18008;
                                   FStar_Syntax_Syntax.lbunivs = uu____18009;
                                   FStar_Syntax_Syntax.lbtyp = uu____18010;
                                   FStar_Syntax_Syntax.lbeff = uu____18011;
                                   FStar_Syntax_Syntax.lbdef = uu____18012;
                                   FStar_Syntax_Syntax.lbattrs = uu____18013;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18025;
                                   FStar_Syntax_Syntax.lbtyp = uu____18026;
                                   FStar_Syntax_Syntax.lbeff = uu____18027;
                                   FStar_Syntax_Syntax.lbdef = uu____18028;
                                   FStar_Syntax_Syntax.lbattrs = uu____18029;_}
                                   ->
                                   FStar_Syntax_DsEnv.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18043 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18074  ->
                             match uu____18074 with
                             | (uu____18087,(uu____18088,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18043
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18112 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18112
                   then
                     let uu____18121 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18135 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18137 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18137.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18137.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18135.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18135.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18135.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18135.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18135.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18121)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let attrs =
                   FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = attrs
                   }  in
                 let env1 = FStar_Syntax_DsEnv.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id1  ->
                          FStar_Syntax_DsEnv.push_doc env2 id1
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____18172 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18178 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18197 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18178 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___136_18221 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18221.FStar_Parser_AST.prange)
                       }
                   | uu____18222 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18229 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18229.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18229.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18229.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18261 id1 =
                   match uu____18261 with
                   | (env1,ses) ->
                       let main =
                         let uu____18282 =
                           let uu____18283 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18283  in
                         FStar_Parser_AST.mk_term uu____18282
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____18333 = desugar_decl env1 id_decl  in
                       (match uu____18333 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18351 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18351 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____18382 = close_fun env t  in
            desugar_term env uu____18382  in
          let quals1 =
            let uu____18386 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____18386
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____18392 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18392;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18404 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18404 with
           | (t,uu____18418) ->
               let l = FStar_Syntax_DsEnv.qualify env id1  in
               let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
               let env2 =
                 FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____18452 =
              let uu____18459 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18459]  in
            let uu____18460 =
              let uu____18463 =
                let uu____18464 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18464  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18463
               in
            FStar_Syntax_Util.arrow uu____18452 uu____18460  in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____18526 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____18526 with
            | FStar_Pervasives_Native.None  ->
                let uu____18529 =
                  let uu____18534 =
                    let uu____18535 =
                      let uu____18536 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18536 " not found"  in
                    Prims.strcat "Effect name " uu____18535  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18534)  in
                FStar_Errors.raise_error uu____18529
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____18540 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18582 =
                  let uu____18591 =
                    let uu____18598 = desugar_term env t  in
                    ([], uu____18598)  in
                  FStar_Pervasives_Native.Some uu____18591  in
                (uu____18582, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18631 =
                  let uu____18640 =
                    let uu____18647 = desugar_term env wp  in
                    ([], uu____18647)  in
                  FStar_Pervasives_Native.Some uu____18640  in
                let uu____18656 =
                  let uu____18665 =
                    let uu____18672 = desugar_term env t  in
                    ([], uu____18672)  in
                  FStar_Pervasives_Native.Some uu____18665  in
                (uu____18631, uu____18656)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18698 =
                  let uu____18707 =
                    let uu____18714 = desugar_term env t  in
                    ([], uu____18714)  in
                  FStar_Pervasives_Native.Some uu____18707  in
                (FStar_Pervasives_Native.None, uu____18698)
             in
          (match uu____18540 with
           | (lift_wp,lift) ->
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect
                        {
                          FStar_Syntax_Syntax.source = src;
                          FStar_Syntax_Syntax.target = dst;
                          FStar_Syntax_Syntax.lift_wp = lift_wp;
                          FStar_Syntax_Syntax.lift = lift
                        });
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               (env, [se]))

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun decls  ->
      let uu____18802 =
        FStar_List.fold_left
          (fun uu____18822  ->
             fun d  ->
               match uu____18822 with
               | (env1,sigelts) ->
                   let uu____18842 = desugar_decl env1 d  in
                   (match uu____18842 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18802 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18883 =
            match uu___110_18883 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18897,FStar_Syntax_Syntax.Sig_let uu____18898) ->
                     let uu____18911 =
                       let uu____18914 =
                         let uu___138_18915 = se2  in
                         let uu____18916 =
                           let uu____18919 =
                             FStar_List.filter
                               (fun uu___109_18933  ->
                                  match uu___109_18933 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18937;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18938;_},uu____18939);
                                      FStar_Syntax_Syntax.pos = uu____18940;
                                      FStar_Syntax_Syntax.vars = uu____18941;_}
                                      when
                                      let uu____18964 =
                                        let uu____18965 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____18965
                                         in
                                      uu____18964 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18966 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____18919
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_18915.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_18915.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_18915.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_18915.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18916
                         }  in
                       uu____18914 :: se1 :: acc  in
                     forward uu____18911 sigelts1
                 | uu____18971 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____18979 = forward [] sigelts  in (env1, uu____18979)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____19030) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19034;
               FStar_Syntax_Syntax.exports = uu____19035;
               FStar_Syntax_Syntax.is_interface = uu____19036;_},FStar_Parser_AST.Module
             (current_lid,uu____19038)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19046) ->
              let uu____19049 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____19049
           in
        let uu____19054 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19090 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19090, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19107 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19107, mname, decls, false)
           in
        match uu____19054 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19137 = desugar_decls env2 decls  in
            (match uu____19137 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____19191 =
            (FStar_Options.interactive ()) &&
              (let uu____19193 =
                 let uu____19194 =
                   let uu____19195 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19195  in
                 FStar_Util.get_file_extension uu____19194  in
               FStar_List.mem uu____19193 ["fsti"; "fsi"])
             in
          if uu____19191 then as_interface m else m  in
        let uu____19199 = desugar_modul_common curmod env m1  in
        match uu____19199 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19214 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19230 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19230 with
      | (env1,modul,pop_when_done) ->
          let uu____19244 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____19244 with
           | (env2,modul1) ->
               ((let uu____19256 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____19256
                 then
                   let uu____19257 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____19257
                 else ());
                (let uu____19259 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____19259, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19273 = desugar_modul env modul  in
      match uu____19273 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19300 = desugar_decls env decls  in
      match uu____19300 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19338 = desugar_partial_modul modul env a_modul  in
        match uu____19338 with | (env1,modul1) -> (modul1, env1)
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____19412 ->
                  let t =
                    let uu____19420 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19420  in
                  let uu____19429 =
                    let uu____19430 = FStar_Syntax_Subst.compress t  in
                    uu____19430.FStar_Syntax_Syntax.n  in
                  (match uu____19429 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19440,uu____19441)
                       -> bs1
                   | uu____19462 -> failwith "Impossible")
               in
            let uu____19469 =
              let uu____19476 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19476
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19469 with
            | (binders,uu____19478,binders_opening) ->
                let erase_term t =
                  let uu____19484 =
                    let uu____19485 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19485  in
                  FStar_Syntax_Subst.close binders uu____19484  in
                let erase_tscheme uu____19501 =
                  match uu____19501 with
                  | (us,t) ->
                      let t1 =
                        let uu____19521 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19521 t  in
                      let uu____19524 =
                        let uu____19525 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19525  in
                      ([], uu____19524)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____19554 ->
                        let bs =
                          let uu____19562 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19562  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19592 =
                          let uu____19593 =
                            let uu____19596 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19596  in
                          uu____19593.FStar_Syntax_Syntax.n  in
                        (match uu____19592 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19604,uu____19605) -> bs1
                         | uu____19626 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19637 =
                      let uu____19638 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19638  in
                    FStar_Syntax_Subst.close binders uu____19637  in
                  let uu___139_19639 = action  in
                  let uu____19640 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19641 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19639.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19639.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19640;
                    FStar_Syntax_Syntax.action_typ = uu____19641
                  }  in
                let uu___140_19642 = ed  in
                let uu____19643 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19644 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19645 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19646 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19647 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19648 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19649 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19650 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19651 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19652 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19653 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19654 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19655 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19656 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19657 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19658 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19642.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19642.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19643;
                  FStar_Syntax_Syntax.signature = uu____19644;
                  FStar_Syntax_Syntax.ret_wp = uu____19645;
                  FStar_Syntax_Syntax.bind_wp = uu____19646;
                  FStar_Syntax_Syntax.if_then_else = uu____19647;
                  FStar_Syntax_Syntax.ite_wp = uu____19648;
                  FStar_Syntax_Syntax.stronger = uu____19649;
                  FStar_Syntax_Syntax.close_wp = uu____19650;
                  FStar_Syntax_Syntax.assert_p = uu____19651;
                  FStar_Syntax_Syntax.assume_p = uu____19652;
                  FStar_Syntax_Syntax.null_wp = uu____19653;
                  FStar_Syntax_Syntax.trivial = uu____19654;
                  FStar_Syntax_Syntax.repr = uu____19655;
                  FStar_Syntax_Syntax.return_repr = uu____19656;
                  FStar_Syntax_Syntax.bind_repr = uu____19657;
                  FStar_Syntax_Syntax.actions = uu____19658
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19670 = se  in
                  let uu____19671 =
                    let uu____19672 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19672  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19671;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19670.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19670.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19670.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19670.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19676 = se  in
                  let uu____19677 =
                    let uu____19678 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19678
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19677;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19676.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19676.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19676.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19676.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19680 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____19681 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19681 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19693 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19693
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____19695 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19695)
  