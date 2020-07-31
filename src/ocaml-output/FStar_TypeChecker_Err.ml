open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string, FStar_Ident.lid) FStar_Util.either *
            FStar_Syntax_Syntax.typ * FStar_Range.range)
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun file ->
      fun row ->
        fun col ->
          let uu____32 =
            let uu____35 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____35 file row col in
          match uu____32 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____78 =
                     let uu____89 =
                       let uu____94 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____94 in
                     let uu____95 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____89,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____95) in
                   FStar_Pervasives_Native.Some uu____78
               | FStar_Util.Inr fv ->
                   let uu____111 =
                     let uu____122 =
                       let uu____127 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____127 in
                     let uu____128 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____122,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____128) in
                   FStar_Pervasives_Native.Some uu____111)
let print_discrepancy :
  'a . ('a -> Prims.string) -> 'a -> 'a -> (Prims.string * Prims.string) =
  fun f ->
    fun x ->
      fun y ->
        let print uu____187 =
          let xs = f x in let ys = f y in (xs, ys, (xs <> ys)) in
        let rec blist_leq l1 l2 =
          match (l1, l2) with
          | (h1::t1, h2::t2) ->
              ((Prims.op_Negation h1) || h2) && (blist_leq t1 t2)
          | ([], []) -> true
          | uu____235 -> failwith "print_discrepancy: bad lists" in
        let rec succ l =
          match l with
          | (false)::t -> true :: t
          | (true)::t -> let uu____264 = succ t in false :: uu____264
          | [] -> failwith "" in
        let full l = FStar_List.for_all (fun b -> b) l in
        let get_bool_option s =
          let uu____287 = FStar_Options.get_option s in
          match uu____287 with
          | FStar_Options.Bool b -> b
          | uu____289 -> failwith "print_discrepancy: impossible" in
        let set_bool_option s b =
          FStar_Options.set_option s (FStar_Options.Bool b) in
        let get uu____308 =
          let pi = get_bool_option "print_implicits" in
          let pu = get_bool_option "print_universes" in
          let pea = get_bool_option "print_effect_args" in
          let pf = get_bool_option "print_full_names" in [pi; pu; pea; pf] in
        let set l =
          match l with
          | pi::pu::pea::pf::[] ->
              (set_bool_option "print_implicits" pi;
               set_bool_option "print_universes" pu;
               set_bool_option "print_effect_args" pea;
               set_bool_option "print_full_names " pf)
          | uu____332 -> failwith "impossible: print_discrepancy" in
        let bas = get () in
        let rec go cur =
          match () with
          | () when full cur ->
              let uu____356 = print () in
              (match uu____356 with | (xs, ys, uu____369) -> (xs, ys))
          | () when
              let uu____370 = blist_leq bas cur in
              Prims.op_Negation uu____370 ->
              let uu____371 = succ cur in go uu____371
          | () ->
              (set cur;
               (let uu____375 = print () in
                match uu____375 with
                | (xs, ys, true) -> (xs, ys)
                | uu____388 -> let uu____395 = succ cur in go uu____395)) in
        FStar_Options.with_saved_options (fun uu____403 -> go bas)
let (errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    FStar_Errors.error Prims.list ->
      (Prims.string, Prims.string) FStar_Util.either ->
        FStar_Errors.error Prims.list)
  =
  fun env ->
    fun errs ->
      fun smt_detail ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Util.Inr d -> Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
          | FStar_Util.Inl d when (FStar_Util.trim_string d) <> "" ->
              Prims.op_Hat msg (Prims.op_Hat "; " d)
          | uu____443 -> msg in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu____495 ->
                  match uu____495 with
                  | (e, msg, r, ctx) ->
                      let uu____524 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu____545 = FStar_TypeChecker_Env.get_range env in
                          (e, msg, uu____545, ctx)
                        else
                          (let r' =
                             let uu____550 = FStar_Range.use_range r in
                             FStar_Range.set_def_range r uu____550 in
                           let uu____551 =
                             let uu____552 = FStar_Range.file_of_range r' in
                             let uu____553 =
                               let uu____554 =
                                 FStar_TypeChecker_Env.get_range env in
                               FStar_Range.file_of_range uu____554 in
                             uu____552 <> uu____553 in
                           if uu____551
                           then
                             let uu____565 =
                               let uu____566 =
                                 let uu____567 =
                                   let uu____568 =
                                     FStar_Range.string_of_use_range r in
                                   let uu____569 =
                                     let uu____570 =
                                       let uu____571 =
                                         let uu____572 =
                                           FStar_Range.use_range r in
                                         let uu____573 =
                                           FStar_Range.def_range r in
                                         uu____572 <> uu____573 in
                                       if uu____571
                                       then
                                         let uu____574 =
                                           let uu____575 =
                                             FStar_Range.string_of_def_range
                                               r in
                                           Prims.op_Hat uu____575 ")" in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu____574
                                       else "" in
                                     Prims.op_Hat ")" uu____570 in
                                   Prims.op_Hat uu____568 uu____569 in
                                 Prims.op_Hat " (Also see: " uu____567 in
                               Prims.op_Hat msg uu____566 in
                             let uu____577 =
                               FStar_TypeChecker_Env.get_range env in
                             (e, uu____565, uu____577, ctx)
                           else (e, msg, r, ctx)) in
                      (match uu____524 with
                       | (e1, msg1, r1, ctx1) ->
                           (e1, (maybe_add_smt_detail msg1), r1, ctx1)))) in
        errs1
let (add_errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    FStar_Errors.error Prims.list ->
      (Prims.string, Prims.string) FStar_Util.either -> unit)
  =
  fun env ->
    fun errs ->
      fun smt_detail ->
        let uu____630 = errors_smt_detail env errs smt_detail in
        FStar_Errors.add_errors uu____630
let (add_errors :
  FStar_TypeChecker_Env.env -> FStar_Errors.error Prims.list -> unit) =
  fun env -> fun errs -> add_errors_smt_detail env errs (FStar_Util.Inl "")
let (log_issue :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> (FStar_Errors.raw_error * Prims.string) -> unit)
  =
  fun env ->
    fun r ->
      fun uu____665 ->
        match uu____665 with
        | (e, m) ->
            let uu____672 =
              let uu____675 =
                let uu____676 = FStar_Errors.get_ctx () in
                (e, m, r, uu____676) in
              [uu____675] in
            add_errors env uu____672
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        print_discrepancy (FStar_TypeChecker_Normalize.term_to_string env) t1
          t2
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        print_discrepancy (FStar_TypeChecker_Normalize.comp_to_string env) c1
          c2
let (exhaustiveness_check : Prims.string) = "Patterns are incomplete"
let (subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun uu____746 ->
          let uu____747 = err_msg_type_strings env t1 t2 in
          match uu____747 with
          | (s1, s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
let (ill_kinded_type : Prims.string) = "Ill-kinded type"
let (totality_check : Prims.string) = "This term may not terminate"
let (unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun m ->
      fun k ->
        let uu____773 =
          let uu____774 = FStar_Ident.string_of_lid m in
          let uu____775 = FStar_TypeChecker_Normalize.term_to_string env k in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type -> WP a -> Effect); got %s"
            uu____774 uu____775 in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____773)
let (expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun msg ->
      fun t ->
        fun e ->
          let uu____800 =
            let uu____801 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____802 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____801 uu____802 msg in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____800)
let (unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string))
  =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
let (expected_expression_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu____831 = err_msg_type_strings env t1 t2 in
          match uu____831 with
          | (s1, s2) ->
              let uu____842 =
                let uu____843 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____843 s2 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____842)
let (expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu____868 = err_msg_type_strings env t1 t2 in
          match uu____868 with
          | (s1, s2) ->
              let uu____879 =
                let uu____880 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____880 s2 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____879)
let (basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun eopt ->
      fun t1 ->
        fun t2 ->
          let uu____909 = err_msg_type_strings env t1 t2 in
          match uu____909 with
          | (s1, s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____922 =
                      FStar_TypeChecker_Normalize.term_to_string env e in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____922 s2 in
              (FStar_Errors.Error_TypeError, msg)
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let constructor_fails_the_positivity_check :
  'uuuuuu935 .
    'uuuuuu935 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun d ->
      fun l ->
        let uu____955 =
          let uu____956 = FStar_Syntax_Print.term_to_string d in
          let uu____957 = FStar_Syntax_Print.lid_to_string l in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____956 uu____957 in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____955)
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu____967 =
      let uu____968 = FStar_Syntax_Print.lid_to_string l in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____968 in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____967)
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      fun x ->
        let uu____988 =
          let uu____989 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____990 = FStar_Syntax_Print.bv_to_string x in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____989 uu____990 in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____988)
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      let uu____1005 =
        let uu____1006 = FStar_TypeChecker_Normalize.term_to_string env t in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____1006 in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____1005)
let (expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun f ->
      fun t ->
        fun targ ->
          let uu____1031 =
            let uu____1032 = FStar_Syntax_Print.term_to_string f in
            let uu____1033 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____1034 =
              FStar_TypeChecker_Normalize.term_to_string env targ in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____1032 uu____1033 uu____1034 in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____1031)
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1 ->
    fun v2 ->
      let vars v =
        let uu____1067 =
          FStar_All.pipe_right v
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____1067 (FStar_String.concat ", ") in
      let uu____1076 =
        let uu____1077 = vars v1 in
        let uu____1078 = vars v2 in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____1077 uu____1078 in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____1076)
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____1101) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t, uu____1113) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____1125 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____1125, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation :
  'uuuuuu1138 .
    FStar_TypeChecker_Env.env ->
      'uuuuuu1138 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____1171 = name_and_result c in
          match uu____1171 with
          | (f1, r1) ->
              let uu____1188 = name_and_result c' in
              (match uu____1188 with
               | (f2, r2) ->
                   let uu____1205 = err_msg_type_strings env r1 r2 in
                   (match uu____1205 with
                    | (s1, s2) ->
                        let uu____1216 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2 in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1216)))
let computed_computation_type_does_not_match_annotation_eq :
  'uuuuuu1227 .
    FStar_TypeChecker_Env.env ->
      'uuuuuu1227 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____1252 = err_msg_comp_strings env c c' in
          match uu____1252 with
          | (s1, s2) ->
              let uu____1263 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1263)
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun f ->
      let uu____1278 =
        let uu____1279 = FStar_TypeChecker_Normalize.term_to_string env f in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1279 in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1278)
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      Prims.string -> (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      fun reason ->
        let msg = "Expected a pure expression" in
        let msg1 =
          if reason = ""
          then msg
          else FStar_Util.format1 (Prims.op_Hat msg " (%s)") reason in
        let uu____1306 =
          let uu____1307 = FStar_Syntax_Print.term_to_string e in
          let uu____1308 =
            let uu____1309 = name_and_result c in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1309 in
          FStar_Util.format2
            (Prims.op_Hat msg1
               "; got an expression \"%s\" with effect \"%s\"") uu____1307
            uu____1308 in
        (FStar_Errors.Fatal_ExpectedPureExpression, uu____1306)
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      Prims.string -> (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      fun reason ->
        let msg = "Expected a ghost expression" in
        let msg1 =
          if reason = ""
          then msg
          else FStar_Util.format1 (Prims.op_Hat msg " (%s)") reason in
        let uu____1350 =
          let uu____1351 = FStar_Syntax_Print.term_to_string e in
          let uu____1352 =
            let uu____1353 = name_and_result c in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1353 in
          FStar_Util.format2
            (Prims.op_Hat msg1
               "; got an expression \"%s\" with effect \"%s\"") uu____1351
            uu____1352 in
        (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1350)
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1 ->
    fun c2 ->
      let uu____1382 =
        let uu____1383 = FStar_Syntax_Print.lid_to_string c1 in
        let uu____1384 = FStar_Syntax_Print.lid_to_string c2 in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1383 uu____1384 in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1382)
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l ->
    fun lbls ->
      let uu____1403 =
        let uu____1404 = FStar_Syntax_Print.lbname_to_string l in
        let uu____1405 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1404 uu____1405 in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1403)
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1422 ->
          let uu____1425 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1425 in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
let (top_level_effect : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
let (cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun l ->
    fun a ->
      let uu____1450 =
        let uu____1451 = FStar_Syntax_Print.lid_to_string l in
        let uu____1452 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1451 uu____1452 in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1450)