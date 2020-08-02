open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___8_5 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___8_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___8_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___8_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___8_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___8_5.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___8_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___8_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___8_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___8_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___8_5.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___8_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___8_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___8_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___8_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___8_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___8_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___8_5.FStar_TypeChecker_Env.use_eq_strict);
      FStar_TypeChecker_Env.is_iface =
        (uu___8_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___8_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___8_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___8_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 = (uu___8_5.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___8_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___8_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___8_5.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___8_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___8_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___8_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___8_5.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___8_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___8_5.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___8_5.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___8_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___8_5.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___8_5.FStar_TypeChecker_Env.try_solve_implicits_hook);
      FStar_TypeChecker_Env.splice = (uu___8_5.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___8_5.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.identifier_info =
        (uu___8_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___8_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___8_5.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___8_5.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___8_5.FStar_TypeChecker_Env.erasable_types_tab);
      FStar_TypeChecker_Env.enable_defer_to_tac =
        (uu___8_5.FStar_TypeChecker_Env.enable_defer_to_tac)
    }
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___11_11 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_11.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_11.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_11.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_11.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_11.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_11.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_11.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_11.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_11.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_11.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_11.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_11.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_11.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_11.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_11.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_11.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___11_11.FStar_TypeChecker_Env.use_eq_strict);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_11.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_11.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_11.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_11.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_11.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_11.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_11.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_11.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_11.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_11.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_11.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_11.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_11.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_11.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_11.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_11.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_11.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_11.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___11_11.FStar_TypeChecker_Env.try_solve_implicits_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_11.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_11.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_11.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_11.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_11.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_11.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_11.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___11_11.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___11_11.FStar_TypeChecker_Env.erasable_types_tab);
      FStar_TypeChecker_Env.enable_defer_to_tac =
        (uu___11_11.FStar_TypeChecker_Env.enable_defer_to_tac)
    }
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun vs ->
    FStar_List.fold_right
      (fun v ->
         fun tl ->
           let r =
             if tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                 tl.FStar_Syntax_Syntax.pos in
           let uu____43 =
             let uu____44 = FStar_Syntax_Syntax.as_arg v in
             let uu____53 =
               let uu____64 = FStar_Syntax_Syntax.as_arg tl in [uu____64] in
             uu____44 :: uu____53 in
           FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____43
             r) vs FStar_Syntax_Util.lex_top
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_103 ->
    match uu___0_103 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> true
    | uu____106 -> false
let steps : 'uuuuuu113 . 'uuuuuu113 -> FStar_TypeChecker_Env.step Prims.list
  =
  fun env ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env -> fun t -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun c -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun head_opt ->
    fun env ->
      fun fvs ->
        fun kt ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____196 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____208 =
                  FStar_List.tryFind (fun x -> FStar_Util.set_mem x fvs') fvs in
                (match uu____208 with
                 | FStar_Pervasives_Native.None ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____232 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None ->
                                let uu____234 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____234
                            | FStar_Pervasives_Native.Some head ->
                                let uu____236 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____237 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____236 uu____237 in
                          let uu____238 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____238 in
                        let uu____243 =
                          let uu____256 = FStar_TypeChecker_Env.get_range env in
                          let uu____257 =
                            let uu____258 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____258 in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____256 env uu____257 in
                        match uu____243 with
                        | (s, uu____272, g0) ->
                            let uu____286 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s in
                            (match uu____286 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____295 =
                                     FStar_TypeChecker_Env.conj_guard g g0 in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____295 in
                                 (s, g1)
                             | uu____296 -> fail ()))) in
          aux false kt
let push_binding :
  'uuuuuu305 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu305) -> FStar_TypeChecker_Env.env
  =
  fun env ->
    fun b ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s ->
    fun b ->
      fun v ->
        let uu____359 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____359
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v)) ::
          s
let (set_lcomp_result :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_TypeChecker_Common.lcomp)
  =
  fun lc ->
    fun t ->
      FStar_TypeChecker_Common.apply_lcomp
        (fun c -> FStar_Syntax_Util.set_result_typ c t) (fun g -> g)
        (let uu___66_385 = lc in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_385.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_385.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_385.FStar_TypeChecker_Common.comp_thunk)
         })
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> e
let (maybe_warn_on_use :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv -> unit) =
  fun env ->
    fun fv ->
      let uu____406 =
        FStar_TypeChecker_Env.lookup_attrs_of_lid env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____406 with
      | FStar_Pervasives_Native.None -> ()
      | FStar_Pervasives_Native.Some attrs ->
          FStar_All.pipe_right attrs
            (FStar_List.iter
               (fun a ->
                  let uu____429 = FStar_Syntax_Util.head_and_args a in
                  match uu____429 with
                  | (head, args) ->
                      let msg_arg m =
                        match args with
                        | ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_string (s, uu____479));
                             FStar_Syntax_Syntax.pos = uu____480;
                             FStar_Syntax_Syntax.vars = uu____481;_},
                           uu____482)::[] ->
                            Prims.op_Hat m (Prims.op_Hat ": " s)
                        | uu____507 -> m in
                      (match head.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.warn_on_use_attr
                           ->
                           let m =
                             let uu____520 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Util.format1
                               "Every use of %s triggers a warning" uu____520 in
                           let uu____521 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                           FStar_Errors.log_issue uu____521
                             (FStar_Errors.Warning_WarnOnUse, (msg_arg m))
                       | FStar_Syntax_Syntax.Tm_fvar attr_fv when
                           FStar_Ident.lid_equals
                             (attr_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let m =
                             let uu____524 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Util.format1 "%s is deprecated" uu____524 in
                           let uu____525 =
                             FStar_Ident.range_of_lid
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                           FStar_Errors.log_issue uu____525
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               (msg_arg m))
                       | uu____526 -> ())))
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_TypeChecker_Common.lcomp)
        FStar_Util.either ->
        FStar_TypeChecker_Common.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun tlc ->
        fun guard ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____570 = FStar_Syntax_Syntax.mk_Total t in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____570
             | FStar_Util.Inr lc -> lc in
           let t = lc.FStar_TypeChecker_Common.res_typ in
           let uu____573 =
             let uu____580 = FStar_TypeChecker_Env.expected_typ env in
             match uu____580 with
             | FStar_Pervasives_Native.None -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____590 =
                   FStar_TypeChecker_Util.check_has_type env e lc t' in
                 (match uu____590 with
                  | (e1, lc1, g) ->
                      ((let uu____607 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium in
                        if uu____607
                        then
                          let uu____608 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1 in
                          let uu____609 =
                            FStar_Syntax_Print.term_to_string t' in
                          let uu____610 =
                            FStar_TypeChecker_Rel.guard_to_string env g in
                          let uu____611 =
                            FStar_TypeChecker_Rel.guard_to_string env guard in
                          FStar_Util.print4
                            "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
                            uu____608 uu____609 uu____610 uu____611
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard in
                        let msg =
                          let uu____621 =
                            FStar_TypeChecker_Env.is_trivial_guard_formula g1 in
                          if uu____621
                          then FStar_Pervasives_Native.None
                          else
                            FStar_All.pipe_left
                              (fun uu____642 ->
                                 FStar_Pervasives_Native.Some uu____642)
                              (FStar_TypeChecker_Err.subtyping_failed env t1
                                 t') in
                        let uu____643 =
                          FStar_TypeChecker_Util.strengthen_precondition msg
                            env e1 lc1 g1 in
                        match uu____643 with
                        | (lc2, g2) ->
                            let uu____656 = set_lcomp_result lc2 t' in
                            ((memo_tk e1 t'), uu____656, g2)))) in
           match uu____573 with | (e1, lc1, g) -> (e1, lc1, g))
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        let uu____693 = FStar_TypeChecker_Env.expected_typ env in
        match uu____693 with
        | FStar_Pervasives_Native.None ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____703 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t in
            (match uu____703 with
             | (e1, lc1, g_c) ->
                 let uu____719 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t in
                 (match uu____719 with
                  | (e2, lc2, g) ->
                      let uu____735 = FStar_TypeChecker_Env.conj_guard g g_c in
                      (e2, lc2, uu____735)))
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun copt ->
      fun ec ->
        let uu____775 = ec in
        match uu____775 with
        | (e, c) ->
            let tot_or_gtot c1 =
              let uu____798 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____798
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____800 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____800
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____802 =
              let ct = FStar_Syntax_Util.comp_result c in
              match copt with
              | FStar_Pervasives_Native.Some uu____826 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None ->
                  let uu____831 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____833 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____833)) in
                  if uu____831
                  then
                    let uu____844 =
                      let uu____847 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____847 in
                    (uu____844, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____853 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____853
                     then
                       let uu____864 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____864,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____870 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____870
                        then
                          let uu____881 =
                            let uu____884 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____884 in
                          (uu____881, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____890 =
                             let uu____891 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env) in
                             FStar_All.pipe_right uu____891
                               (FStar_TypeChecker_Env.is_layered_effect env) in
                           if uu____890
                           then
                             let uu____902 =
                               let uu____907 =
                                 let uu____908 =
                                   let uu____909 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____909
                                     FStar_Ident.string_of_lid in
                                 let uu____912 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____908 uu____912 in
                               (FStar_Errors.Fatal_IllTyped, uu____907) in
                             FStar_Errors.raise_error uu____902
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____924 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  () in
                              if uu____924
                              then
                                let uu____935 =
                                  let uu____938 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c in
                                  match uu____938 with
                                  | (uu____947, uu____948, g) ->
                                      FStar_Pervasives_Native.Some g in
                                (FStar_Pervasives_Native.None, c, uu____935)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None))))) in
            (match uu____802 with
             | (expected_c_opt, c1, gopt) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None ->
                      (e, c2,
                        ((match gopt with
                          | FStar_Pervasives_Native.None ->
                              FStar_TypeChecker_Env.trivial_guard
                          | FStar_Pervasives_Native.Some g -> g)))
                  | FStar_Pervasives_Native.Some expected_c ->
                      ((match gopt with
                        | FStar_Pervasives_Native.None -> ()
                        | FStar_Pervasives_Native.Some uu____986 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____988 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2 in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____988 in
                        let uu____989 =
                          FStar_TypeChecker_Common.lcomp_comp c3 in
                        match uu____989 with
                        | (c4, g_c) ->
                            ((let uu____1003 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium in
                              if uu____1003
                              then
                                let uu____1004 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____1005 =
                                  FStar_Syntax_Print.comp_to_string c4 in
                                let uu____1006 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1004 uu____1005 uu____1006
                              else ());
                             (let uu____1008 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c in
                              match uu____1008 with
                              | (e1, uu____1022, g) ->
                                  let g1 =
                                    let uu____1025 =
                                      FStar_TypeChecker_Env.get_range env in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1025
                                      "could not prove post-condition" g in
                                  ((let uu____1027 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium in
                                    if uu____1027
                                    then
                                      let uu____1028 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos in
                                      let uu____1029 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1 in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1028 uu____1029
                                    else ());
                                   (let e2 =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        e1
                                        (FStar_Syntax_Util.comp_effect_name
                                           c4)
                                        (FStar_Syntax_Util.comp_effect_name
                                           expected_c)
                                        (FStar_Syntax_Util.comp_result c4) in
                                    let uu____1032 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1 in
                                    (e2, expected_c, uu____1032)))))))))
let no_logical_guard :
  'uuuuuu1041 'uuuuuu1042 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1041 * 'uuuuuu1042 * FStar_TypeChecker_Env.guard_t) ->
        ('uuuuuu1041 * 'uuuuuu1042 * FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun uu____1064 ->
      match uu____1064 with
      | (te, kt, f) ->
          let uu____1074 = FStar_TypeChecker_Env.guard_form f in
          (match uu____1074 with
           | FStar_TypeChecker_Common.Trivial -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1082 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____1087 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____1082 uu____1087)
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____1099 = FStar_TypeChecker_Env.expected_typ env in
    match uu____1099 with
    | FStar_Pervasives_Native.None ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1103 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____1103
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all ->
    fun andlist ->
      fun pats ->
        let pats1 = FStar_Syntax_Util.unmeta pats in
        let uu____1128 = FStar_Syntax_Util.head_and_args pats1 in
        match uu____1128 with
        | (head, args) ->
            let uu____1173 =
              let uu____1188 =
                let uu____1189 = FStar_Syntax_Util.un_uinst head in
                uu____1189.FStar_Syntax_Syntax.n in
              (uu____1188, args) in
            (match uu____1173 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1205) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1230, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1231))::(hd,
                                                              FStar_Pervasives_Native.None)::
                (tl, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd in
                 let tlvs = get_pat_vars' all andlist tl in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1304, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1305))::(pat,
                                                              FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1387 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all -> fun pats -> get_pat_vars' all false pats
let check_pat_fvs :
  'uuuuuu1428 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'uuuuuu1428) Prims.list -> unit
  =
  fun rng ->
    fun env ->
      fun pats ->
        fun bs ->
          let pat_vars =
            let uu____1464 = FStar_List.map FStar_Pervasives_Native.fst bs in
            let uu____1471 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats in
            get_pat_vars uu____1464 uu____1471 in
          let uu____1472 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1499 ->
                    match uu____1499 with
                    | (b, uu____1505) ->
                        let uu____1506 = FStar_Util.set_mem b pat_vars in
                        Prims.op_Negation uu____1506)) in
          match uu____1472 with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (x, uu____1512) ->
              let uu____1517 =
                let uu____1522 =
                  let uu____1523 = FStar_Syntax_Print.bv_to_string x in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1523 in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1522) in
              FStar_Errors.log_issue rng uu____1517
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en ->
    fun t ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1 in
        let uu____1545 = FStar_Syntax_Util.head_and_args t2 in
        match uu____1545 with
        | (head, args) ->
            let uu____1590 =
              let uu____1605 =
                let uu____1606 = FStar_Syntax_Util.un_uinst head in
                uu____1606.FStar_Syntax_Syntax.n in
              (uu____1605, args) in
            (match uu____1590 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1622) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1644::(hd, uu____1646)::(tl, uu____1648)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1715 = pat_terms hd in
                 let uu____1718 = pat_terms tl in
                 FStar_List.append uu____1715 uu____1718
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1722::(pat, uu____1724)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1809 -> []) in
      let rec aux t1 =
        let uu____1834 =
          let uu____1835 = FStar_Syntax_Subst.compress t1 in
          uu____1835.FStar_Syntax_Syntax.n in
        match uu____1834 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1840 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1841 -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1842 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1843 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1844 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1857 -> []
        | FStar_Syntax_Syntax.Tm_unknown -> []
        | FStar_Syntax_Syntax.Tm_abs uu____1858 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1877 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1892 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1899 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1922 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1935 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1950 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1958 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid in
            if uu____1958 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2, args) ->
            let uu____1988 = aux t2 in
            FStar_List.fold_left
              (fun acc ->
                 fun uu____2005 ->
                   match uu____2005 with
                   | (t3, uu____2017) ->
                       let uu____2022 = aux t3 in
                       FStar_List.append acc uu____2022) uu____1988 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2026, uu____2027) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2069) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____2075) -> aux t2 in
      let tlist =
        let uu____2083 = FStar_All.pipe_right t pat_terms in
        FStar_All.pipe_right uu____2083 (FStar_List.collect aux) in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s ->
                fun t1 ->
                  let uu____2099 =
                    let uu____2100 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat " " uu____2100 in
                  Prims.op_Hat s uu____2099) "" tlist in
         let uu____2101 =
           let uu____2106 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2106) in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2101)
let check_smt_pat :
  'uuuuuu2117 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2117) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env ->
    fun t ->
      fun bs ->
        fun c ->
          let uu____2158 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____2158
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2159;
                  FStar_Syntax_Syntax.effect_name = uu____2160;
                  FStar_Syntax_Syntax.result_typ = uu____2161;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats, uu____2165)::[];
                  FStar_Syntax_Syntax.flags = uu____2166;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2228 -> failwith "Impossible"
          else ()
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env ->
    fun actuals ->
      fun expected_c ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___396_2292 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___396_2292.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___396_2292.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___396_2292.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___396_2292.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___396_2292.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___396_2292.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___396_2292.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___396_2292.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___396_2292.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___396_2292.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___396_2292.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___396_2292.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___396_2292.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___396_2292.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.use_eq_strict =
                  (uu___396_2292.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (uu___396_2292.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___396_2292.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___396_2292.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___396_2292.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___396_2292.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___396_2292.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___396_2292.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___396_2292.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___396_2292.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___396_2292.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___396_2292.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___396_2292.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___396_2292.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___396_2292.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___396_2292.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___396_2292.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___396_2292.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___396_2292.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___396_2292.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___396_2292.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___396_2292.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___396_2292.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___396_2292.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___396_2292.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___396_2292.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___396_2292.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___396_2292.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___396_2292.FStar_TypeChecker_Env.erasable_types_tab);
                FStar_TypeChecker_Env.enable_defer_to_tac =
                  (uu___396_2292.FStar_TypeChecker_Env.enable_defer_to_tac)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____2320 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____2320
               then
                 let uu____2321 =
                   FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____2322 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2321 uu____2322
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2353 ->
                         match uu____2353 with
                         | (b, uu____2363) ->
                             let t =
                               let uu____2369 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2369 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2372 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2373 -> []
                              | uu____2388 ->
                                  let uu____2389 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____2389]))) in
               let as_lex_list dec =
                 let uu____2402 = FStar_Syntax_Util.head_and_args dec in
                 match uu____2402 with
                 | (head, uu____2422) ->
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2450 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____2458 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2467 ->
                         match uu___1_2467 with
                         | FStar_Syntax_Syntax.DECREASES uu____2468 -> true
                         | uu____2471 -> false)) in
               match uu____2458 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2477 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   mk_lex_list xs) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____2513 =
              match uu____2513 with
              | (l, arity, t, u_names) ->
                  let uu____2534 =
                    FStar_TypeChecker_Normalize.get_n_binders env1 arity t in
                  (match uu____2534 with
                   | (formals, c) ->
                       (if arity > (FStar_List.length formals)
                        then
                          failwith
                            "impossible: bad formals arity, guard_one_letrec"
                        else ();
                        (let formals1 =
                           FStar_All.pipe_right formals
                             (FStar_List.map
                                (fun uu____2599 ->
                                   match uu____2599 with
                                   | (x, imp) ->
                                       let uu____2618 =
                                         FStar_Syntax_Syntax.is_null_bv x in
                                       if uu____2618
                                       then
                                         let uu____2625 =
                                           let uu____2626 =
                                             let uu____2629 =
                                               FStar_Syntax_Syntax.range_of_bv
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____2629 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____2626
                                             x.FStar_Syntax_Syntax.sort in
                                         (uu____2625, imp)
                                       else (x, imp))) in
                         let dec = decreases_clause formals1 c in
                         let precedes1 =
                           let uu____2639 =
                             let uu____2640 = FStar_Syntax_Syntax.as_arg dec in
                             let uu____2649 =
                               let uu____2660 =
                                 FStar_Syntax_Syntax.as_arg previous_dec in
                               [uu____2660] in
                             uu____2640 :: uu____2649 in
                           FStar_Syntax_Syntax.mk_Tm_app precedes uu____2639
                             r in
                         let precedes2 =
                           FStar_TypeChecker_Util.label
                             "Could not prove termination of this recursive call"
                             r precedes1 in
                         let uu____2694 = FStar_Util.prefix formals1 in
                         match uu____2694 with
                         | (bs, (last, imp)) ->
                             let last1 =
                               let uu___459_2757 = last in
                               let uu____2758 =
                                 FStar_Syntax_Util.refine last precedes2 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___459_2757.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___459_2757.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____2758
                               } in
                             let refined_formals =
                               FStar_List.append bs [(last1, imp)] in
                             let t' =
                               FStar_Syntax_Util.arrow refined_formals c in
                             ((let uu____2794 =
                                 FStar_TypeChecker_Env.debug env1
                                   FStar_Options.Medium in
                               if uu____2794
                               then
                                 let uu____2795 =
                                   FStar_Syntax_Print.lbname_to_string l in
                                 let uu____2796 =
                                   FStar_Syntax_Print.term_to_string t in
                                 let uu____2797 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print3
                                   "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                   uu____2795 uu____2796 uu____2797
                               else ());
                              (l, t', u_names))))) in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt ->
    fun g ->
      match topt with
      | FStar_Pervasives_Native.None -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1 ->
               let uu____2853 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1 in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2853)
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____2875 =
      let uu____2876 = FStar_Syntax_Subst.compress e in
      uu____2876.FStar_Syntax_Syntax.n in
    match uu____2875 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1, (FStar_Util.Inr uu____2888, uu____2889), uu____2890) ->
        let uu____2937 =
          let uu____2938 = FStar_Syntax_Subst.compress e1 in
          uu____2938.FStar_Syntax_Syntax.n in
        (match uu____2937 with
         | FStar_Syntax_Syntax.Tm_app (head, args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____2983 =
               let uu____2984 = FStar_Syntax_Subst.compress head in
               uu____2984.FStar_Syntax_Syntax.n in
             (match uu____2983 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____2996 =
                    let uu____3003 = FStar_All.pipe_right args FStar_List.hd in
                    FStar_All.pipe_right uu____3003
                      (fun uu____3059 ->
                         match uu____3059 with
                         | (e2, aqual) -> (l, e2, aqual)) in
                  FStar_All.pipe_right uu____2996
                    (fun uu____3112 ->
                       FStar_Pervasives_Native.Some uu____3112)
              | uu____3113 -> FStar_Pervasives_Native.None)
         | uu____3120 -> FStar_Pervasives_Native.None)
    | uu____3127 -> FStar_Pervasives_Native.None
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____3868 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
       if uu____3868
       then
         let uu____3869 =
           let uu____3870 = FStar_TypeChecker_Env.get_range env in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3870 in
         let uu____3871 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1 in
         let uu____3872 = FStar_Syntax_Print.term_to_string e in
         let uu____3873 =
           let uu____3874 = FStar_Syntax_Subst.compress e in
           FStar_Syntax_Print.tag_of_term uu____3874 in
         let uu____3875 =
           let uu____3876 = FStar_TypeChecker_Env.expected_typ env in
           match uu____3876 with
           | FStar_Pervasives_Native.None -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3869 uu____3871 uu____3872 uu____3873 uu____3875
       else ());
      (let uu____3881 =
         FStar_Util.record_time
           (fun uu____3899 ->
              tc_maybe_toplevel_term
                (let uu___502_3902 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___502_3902.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___502_3902.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___502_3902.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___502_3902.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___502_3902.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___502_3902.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___502_3902.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___502_3902.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___502_3902.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___502_3902.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___502_3902.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___502_3902.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___502_3902.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___502_3902.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___502_3902.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___502_3902.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___502_3902.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___502_3902.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___502_3902.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___502_3902.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___502_3902.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___502_3902.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___502_3902.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___502_3902.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___502_3902.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___502_3902.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___502_3902.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___502_3902.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___502_3902.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___502_3902.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___502_3902.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___502_3902.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___502_3902.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___502_3902.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___502_3902.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___502_3902.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___502_3902.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___502_3902.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___502_3902.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___502_3902.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___502_3902.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___502_3902.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___502_3902.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___502_3902.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___502_3902.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___502_3902.FStar_TypeChecker_Env.enable_defer_to_tac)
                 }) e) in
       match uu____3881 with
       | (r, ms) ->
           ((let uu____3924 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____3924
             then
               ((let uu____3926 =
                   let uu____3927 = FStar_TypeChecker_Env.get_range env in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3927 in
                 let uu____3928 = FStar_Syntax_Print.term_to_string e in
                 let uu____3929 =
                   let uu____3930 = FStar_Syntax_Subst.compress e in
                   FStar_Syntax_Print.tag_of_term uu____3930 in
                 let uu____3931 = FStar_Util.string_of_int ms in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3926 uu____3928 uu____3929 uu____3931);
                (let uu____3932 = r in
                 match uu____3932 with
                 | (e1, lc, uu____3941) ->
                     let uu____3942 =
                       let uu____3943 = FStar_TypeChecker_Env.get_range env in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3943 in
                     let uu____3944 = FStar_Syntax_Print.term_to_string e1 in
                     let uu____3945 =
                       FStar_TypeChecker_Common.lcomp_to_string lc in
                     let uu____3946 =
                       let uu____3947 = FStar_Syntax_Subst.compress e1 in
                       FStar_Syntax_Print.tag_of_term uu____3947 in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____3942 uu____3944 uu____3945 uu____3946))
             else ());
            r))
and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      (let uu____3961 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
       if uu____3961
       then
         let uu____3962 =
           let uu____3963 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3963 in
         let uu____3964 = FStar_Syntax_Print.tag_of_term top in
         let uu____3965 = FStar_Syntax_Print.term_to_string top in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3962 uu____3964
           uu____3965
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3973 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3994 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4001 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4014 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4015 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4016 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4017 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4018 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4037 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4052 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4059 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
           let projl uu___2_4075 =
             match uu___2_4075 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4081 -> failwith "projl fail" in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4094 =
                 let uu____4095 = FStar_Syntax_Subst.compress t in
                 uu____4095.FStar_Syntax_Syntax.n in
               match uu____4094 with
               | FStar_Syntax_Syntax.Tm_name uu____4098 -> true
               | uu____4099 -> false in
             FStar_Util.for_some
               (fun uu____4108 ->
                  match uu____4108 with
                  | (uu____4113, t) ->
                      let uu____4115 = is_name t in
                      Prims.op_Negation uu____4115)
               qi1.FStar_Syntax_Syntax.antiquotes in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static when non_trivial_antiquotes qi
                ->
                let e0 = e in
                let newbvs =
                  FStar_List.map
                    (fun uu____4133 ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs in
                let lbs =
                  FStar_List.map
                    (fun uu____4176 ->
                       match uu____4176 with
                       | ((bv, t), bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z in
                let qi1 =
                  let uu___575_4205 = qi in
                  let uu____4206 =
                    FStar_List.map
                      (fun uu____4234 ->
                         match uu____4234 with
                         | ((bv, uu____4250), bv') ->
                             let uu____4262 =
                               FStar_Syntax_Syntax.bv_to_name bv' in
                             (bv, uu____4262)) z in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___575_4205.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4206
                  } in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    top.FStar_Syntax_Syntax.pos in
                let e1 =
                  FStar_List.fold_left
                    (fun t ->
                       fun lb ->
                         let uu____4274 =
                           let uu____4275 =
                             let uu____4288 =
                               let uu____4291 =
                                 let uu____4292 =
                                   let uu____4299 =
                                     projl lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Syntax_Syntax.mk_binder uu____4299 in
                                 [uu____4292] in
                               FStar_Syntax_Subst.close uu____4291 t in
                             ((false, [lb]), uu____4288) in
                           FStar_Syntax_Syntax.Tm_let uu____4275 in
                         FStar_Syntax_Syntax.mk uu____4274
                           top.FStar_Syntax_Syntax.pos) nq lbs in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term in
                let uu____4332 =
                  FStar_List.fold_right
                    (fun uu____4368 ->
                       fun uu____4369 ->
                         match (uu____4368, uu____4369) with
                         | ((bv, tm), (aqs_rev, guard)) ->
                             let uu____4438 = tc_term env_tm tm in
                             (match uu____4438 with
                              | (tm1, uu____4456, g) ->
                                  let uu____4458 =
                                    FStar_TypeChecker_Env.conj_guard g guard in
                                  (((bv, tm1) :: aqs_rev), uu____4458))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard) in
                (match uu____4332 with
                 | (aqs_rev, guard) ->
                     let qi1 =
                       let uu___603_4500 = qi in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___603_4500.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       } in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         top.FStar_Syntax_Syntax.pos in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic ->
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term in
                let uu____4511 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____4511 with
                 | (env', uu____4525) ->
                     let uu____4530 =
                       tc_term
                         (let uu___612_4539 = env' in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___612_4539.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___612_4539.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___612_4539.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___612_4539.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___612_4539.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___612_4539.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___612_4539.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___612_4539.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___612_4539.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___612_4539.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___612_4539.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___612_4539.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___612_4539.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___612_4539.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___612_4539.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___612_4539.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___612_4539.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___612_4539.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___612_4539.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___612_4539.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___612_4539.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___612_4539.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___612_4539.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___612_4539.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___612_4539.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___612_4539.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___612_4539.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___612_4539.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___612_4539.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___612_4539.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___612_4539.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___612_4539.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___612_4539.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___612_4539.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___612_4539.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___612_4539.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___612_4539.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___612_4539.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___612_4539.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___612_4539.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___612_4539.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___612_4539.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___612_4539.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___612_4539.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___612_4539.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___612_4539.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) qt in
                     (match uu____4530 with
                      | (qt1, uu____4547, uu____4548) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4554 =
                            let uu____4561 =
                              let uu____4566 =
                                FStar_TypeChecker_Common.lcomp_of_comp c in
                              FStar_Util.Inr uu____4566 in
                            value_check_expected_typ env1 top uu____4561
                              FStar_TypeChecker_Env.trivial_guard in
                          (match uu____4554 with
                           | (t1, lc, g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   t1.FStar_Syntax_Syntax.pos in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4583;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4584;
             FStar_Syntax_Syntax.ltyp = uu____4585;
             FStar_Syntax_Syntax.rng = uu____4586;_}
           ->
           let uu____4597 = FStar_Syntax_Util.unlazy top in
           tc_term env1 uu____4597
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat))
           ->
           let uu____4604 = tc_tot_or_gtot_term env1 e1 in
           (match uu____4604 with
            | (e2, c, g) ->
                let g1 =
                  let uu___642_4621 = g in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___642_4621.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___642_4621.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___642_4621.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___642_4621.FStar_TypeChecker_Common.implicits)
                  } in
                let uu____4622 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    top.FStar_Syntax_Syntax.pos in
                (uu____4622, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_pattern (names, pats)) ->
           let uu____4664 = FStar_Syntax_Util.type_u () in
           (match uu____4664 with
            | (t, u) ->
                let uu____4677 = tc_check_tot_or_gtot_term env1 e1 t "" in
                (match uu____4677 with
                 | (e2, c, g) ->
                     let uu____4693 =
                       let uu____4710 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____4710 with
                       | (env2, uu____4734) -> tc_smt_pats env2 pats in
                     (match uu____4693 with
                      | (pats1, g') ->
                          let g'1 =
                            let uu___665_4772 = g' in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (uu___665_4772.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (uu___665_4772.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___665_4772.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___665_4772.FStar_TypeChecker_Common.implicits)
                            } in
                          let uu____4773 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4792 =
                            FStar_TypeChecker_Env.conj_guard g g'1 in
                          (uu____4773, c, uu____4792))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence))
           ->
           let uu____4798 =
             let uu____4799 = FStar_Syntax_Subst.compress e1 in
             uu____4799.FStar_Syntax_Syntax.n in
           (match uu____4798 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4808,
                  { FStar_Syntax_Syntax.lbname = x;
                    FStar_Syntax_Syntax.lbunivs = uu____4810;
                    FStar_Syntax_Syntax.lbtyp = uu____4811;
                    FStar_Syntax_Syntax.lbeff = uu____4812;
                    FStar_Syntax_Syntax.lbdef = e11;
                    FStar_Syntax_Syntax.lbattrs = uu____4814;
                    FStar_Syntax_Syntax.lbpos = uu____4815;_}::[]),
                 e2)
                ->
                let uu____4843 =
                  let uu____4850 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____4850 e11 in
                (match uu____4843 with
                 | (e12, c1, g1) ->
                     let uu____4860 = tc_term env1 e2 in
                     (match uu____4860 with
                      | (e21, c2, g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2) in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c2.FStar_TypeChecker_Common.res_typ in
                          let attrs =
                            let uu____4884 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name in
                            if uu____4884
                            then [FStar_Syntax_Util.inline_let_attr]
                            else [] in
                          let e3 =
                            let uu____4891 =
                              let uu____4892 =
                                let uu____4905 =
                                  let uu____4912 =
                                    let uu____4915 =
                                      FStar_Syntax_Syntax.mk_lb
                                        (x, [],
                                          (c.FStar_TypeChecker_Common.eff_name),
                                          FStar_Syntax_Syntax.t_unit, e13,
                                          attrs,
                                          (e13.FStar_Syntax_Syntax.pos)) in
                                    [uu____4915] in
                                  (false, uu____4912) in
                                (uu____4905, e22) in
                              FStar_Syntax_Syntax.Tm_let uu____4892 in
                            FStar_Syntax_Syntax.mk uu____4891
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.res_typ in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4936 =
                            FStar_TypeChecker_Env.conj_guard g1 g2 in
                          (e5, c, uu____4936)))
            | uu____4937 ->
                let uu____4938 = tc_term env1 e1 in
                (match uu____4938 with
                 | (e2, c, g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic uu____4960) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic_lift uu____4972) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
           let uu____4991 = tc_term env1 e1 in
           (match uu____4991 with
            | (e2, c, g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (asc, FStar_Pervasives_Native.Some tac), labopt) ->
           let uu____5064 =
             tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
               env1 tac in
           (match uu____5064 with
            | (tac1, uu____5078, g_tac) ->
                let t' =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_ascribed
                       (e1, (asc, FStar_Pervasives_Native.None), labopt))
                    top.FStar_Syntax_Syntax.pos in
                let uu____5117 = tc_term env1 t' in
                (match uu____5117 with
                 | (t'1, c, g) ->
                     let t'2 =
                       let uu____5134 =
                         let uu____5135 = FStar_Syntax_Subst.compress t'1 in
                         uu____5135.FStar_Syntax_Syntax.n in
                       match uu____5134 with
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (e2, (asc1, FStar_Pervasives_Native.None),
                            labopt1)
                           ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_ascribed
                                (e2,
                                  (asc1, (FStar_Pervasives_Native.Some tac1)),
                                  labopt1)) t'1.FStar_Syntax_Syntax.pos
                       | uu____5221 -> failwith "impossible" in
                     let g1 =
                       wrap_guard_with_tactic_opt
                         (FStar_Pervasives_Native.Some tac1) g in
                     let uu____5223 =
                       FStar_TypeChecker_Env.conj_guard g1 g_tac in
                     (t'2, c, uu____5223)))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5224,
            (FStar_Util.Inr expected_c, FStar_Pervasives_Native.None),
            uu____5226)
           when
           let uu____5271 = FStar_All.pipe_right top is_comp_ascribed_reflect in
           FStar_All.pipe_right uu____5271 FStar_Util.is_some ->
           let uu____5302 =
             let uu____5313 =
               FStar_All.pipe_right top is_comp_ascribed_reflect in
             FStar_All.pipe_right uu____5313 FStar_Util.must in
           (match uu____5302 with
            | (effect_lid, e1, aqual) ->
                let uu____5387 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____5387 with
                 | (env0, uu____5401) ->
                     let uu____5406 = tc_comp env0 expected_c in
                     (match uu____5406 with
                      | (expected_c1, uu____5420, g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1 in
                          ((let uu____5424 =
                              let uu____5425 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name in
                              Prims.op_Negation uu____5425 in
                            if uu____5424
                            then
                              let uu____5426 =
                                let uu____5431 =
                                  let uu____5432 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  let uu____5433 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5432 uu____5433 in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5431) in
                              FStar_Errors.raise_error uu____5426
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5436 =
                              let uu____5437 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid in
                              Prims.op_Negation uu____5437 in
                            if uu____5436
                            then
                              let uu____5438 =
                                let uu____5443 =
                                  let uu____5444 =
                                    FStar_Ident.string_of_lid effect_lid in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5444 in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5443) in
                              FStar_Errors.raise_error uu____5438
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd in
                            let repr =
                              let uu____5450 =
                                let uu____5453 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5453 u_c in
                              FStar_All.pipe_right uu____5450 FStar_Util.must in
                            let e2 =
                              let uu____5459 =
                                let uu____5460 =
                                  let uu____5487 =
                                    let uu____5504 =
                                      let uu____5513 =
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          (FStar_Pervasives_Native.Some u_c) in
                                      FStar_Util.Inr uu____5513 in
                                    (uu____5504,
                                      FStar_Pervasives_Native.None) in
                                  (e1, uu____5487,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____5460 in
                              FStar_Syntax_Syntax.mk uu____5459
                                e1.FStar_Syntax_Syntax.pos in
                            (let uu____5555 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme in
                             if uu____5555
                             then
                               let uu____5556 =
                                 FStar_Syntax_Print.term_to_string e2 in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5556
                             else ());
                            (let uu____5558 = tc_tot_or_gtot_term env0 e2 in
                             match uu____5558 with
                             | (e3, uu____5572, g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3 in
                                 ((let uu____5576 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme in
                                   if uu____5576
                                   then
                                     let uu____5577 =
                                       FStar_Syntax_Print.term_to_string e4 in
                                     let uu____5578 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5577 uu____5578
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid)) r in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)])) r in
                                     let uu____5622 =
                                       let uu____5623 =
                                         let uu____5650 =
                                           let uu____5653 =
                                             FStar_All.pipe_right expected_c1
                                               FStar_Syntax_Util.comp_effect_name in
                                           FStar_All.pipe_right uu____5653
                                             (fun uu____5658 ->
                                                FStar_Pervasives_Native.Some
                                                  uu____5658) in
                                         (tm1,
                                           ((FStar_Util.Inr expected_c1),
                                             FStar_Pervasives_Native.None),
                                           uu____5650) in
                                       FStar_Syntax_Syntax.Tm_ascribed
                                         uu____5623 in
                                     FStar_Syntax_Syntax.mk uu____5622 r in
                                   let uu____5697 =
                                     let uu____5704 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     comp_check_expected_typ env1 top1
                                       uu____5704 in
                                   match uu____5697 with
                                   | (top2, c, g_env) ->
                                       let uu____5714 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env] in
                                       (top2, c, uu____5714)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inr expected_c, FStar_Pervasives_Native.None),
            uu____5717)
           ->
           let uu____5762 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____5762 with
            | (env0, uu____5776) ->
                let uu____5781 = tc_comp env0 expected_c in
                (match uu____5781 with
                 | (expected_c1, uu____5795, g) ->
                     let uu____5797 =
                       let uu____5804 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0) in
                       tc_term uu____5804 e1 in
                     (match uu____5797 with
                      | (e2, c', g') ->
                          let uu____5814 =
                            let uu____5825 =
                              FStar_TypeChecker_Common.lcomp_comp c' in
                            match uu____5825 with
                            | (c'1, g_c') ->
                                let uu____5842 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1) in
                                (match uu____5842 with
                                 | (e3, expected_c2, g'') ->
                                     let uu____5862 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g'' in
                                     (e3, expected_c2, uu____5862)) in
                          (match uu____5814 with
                           | (e3, expected_c2, g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_TypeChecker_Common.lcomp_of_comp
                                   expected_c2 in
                               let f =
                                 let uu____5927 =
                                   FStar_TypeChecker_Env.conj_guard g' g'' in
                                 FStar_TypeChecker_Env.conj_guard g
                                   uu____5927 in
                               let uu____5928 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____5928 with
                                | (e5, c, f2) ->
                                    let uu____5944 =
                                      FStar_TypeChecker_Env.conj_guard f f2 in
                                    (e5, c, uu____5944))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inl t, FStar_Pervasives_Native.None), uu____5947)
           ->
           let uu____5992 = FStar_Syntax_Util.type_u () in
           (match uu____5992 with
            | (k, u) ->
                let uu____6005 = tc_check_tot_or_gtot_term env1 t k "" in
                (match uu____6005 with
                 | (t1, uu____6019, f) ->
                     let uu____6021 =
                       let uu____6028 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____6028 e1 in
                     (match uu____6021 with
                      | (e2, c, g) ->
                          let uu____6038 =
                            let uu____6043 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____6048 ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____6043 e2 c f in
                          (match uu____6038 with
                           | (c1, f1) ->
                               let uu____6057 =
                                 let uu____6064 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_TypeChecker_Common.eff_name))))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____6064 c1 in
                               (match uu____6057 with
                                | (e3, c2, f2) ->
                                    let uu____6112 =
                                      let uu____6113 =
                                        FStar_TypeChecker_Env.conj_guard g f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____6113 in
                                    (e3, c2, uu____6112))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6114;
              FStar_Syntax_Syntax.vars = uu____6115;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6194 = FStar_Syntax_Util.head_and_args top in
           (match uu____6194 with
            | (unary_op, uu____6218) ->
                let head =
                  let uu____6246 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6246 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____6294;
              FStar_Syntax_Syntax.vars = uu____6295;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6374 = FStar_Syntax_Util.head_and_args top in
           (match uu____6374 with
            | (unary_op, uu____6398) ->
                let head =
                  let uu____6426 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6426 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6474);
              FStar_Syntax_Syntax.pos = uu____6475;
              FStar_Syntax_Syntax.vars = uu____6476;_},
            a::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6555 = FStar_Syntax_Util.head_and_args top in
           (match uu____6555 with
            | (unary_op, uu____6579) ->
                let head =
                  let uu____6607 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____6607 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6655;
              FStar_Syntax_Syntax.vars = uu____6656;_},
            a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest in
           let uu____6752 = FStar_Syntax_Util.head_and_args top in
           (match uu____6752 with
            | (unary_op, uu____6776) ->
                let head =
                  let uu____6804 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    uu____6804 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6860;
              FStar_Syntax_Syntax.vars = uu____6861;_},
            (e1, FStar_Pervasives_Native.None)::[])
           ->
           let uu____6899 =
             let uu____6906 =
               let uu____6907 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6907 in
             tc_term uu____6906 e1 in
           (match uu____6899 with
            | (e2, c, g) ->
                let uu____6931 = FStar_Syntax_Util.head_and_args top in
                (match uu____6931 with
                 | (head, uu____6955) ->
                     let uu____6980 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         top.FStar_Syntax_Syntax.pos in
                     let uu____7013 =
                       let uu____7014 =
                         let uu____7015 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____7015 in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7014 in
                     (uu____6980, uu____7013, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____7016;
              FStar_Syntax_Syntax.vars = uu____7017;_},
            (t, FStar_Pervasives_Native.None)::(r,
                                                FStar_Pervasives_Native.None)::[])
           ->
           let uu____7070 = FStar_Syntax_Util.head_and_args top in
           (match uu____7070 with
            | (head, uu____7094) ->
                let env' =
                  let uu____7120 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7120 in
                let uu____7121 = tc_term env' r in
                (match uu____7121 with
                 | (er, uu____7135, gr) ->
                     let uu____7137 = tc_term env1 t in
                     (match uu____7137 with
                      | (t1, tt, gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt in
                          let uu____7154 =
                            let uu____7155 =
                              let uu____7156 = FStar_Syntax_Syntax.as_arg t1 in
                              let uu____7165 =
                                let uu____7176 = FStar_Syntax_Syntax.as_arg r in
                                [uu____7176] in
                              uu____7156 :: uu____7165 in
                            FStar_Syntax_Syntax.mk_Tm_app head uu____7155
                              top.FStar_Syntax_Syntax.pos in
                          (uu____7154, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____7209;
              FStar_Syntax_Syntax.vars = uu____7210;_},
            uu____7211)
           ->
           let uu____7236 =
             let uu____7241 =
               let uu____7242 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7242 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7241) in
           FStar_Errors.raise_error uu____7236 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____7249;
              FStar_Syntax_Syntax.vars = uu____7250;_},
            uu____7251)
           ->
           let uu____7276 =
             let uu____7281 =
               let uu____7282 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____7282 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7281) in
           FStar_Errors.raise_error uu____7276 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____7289;
              FStar_Syntax_Syntax.vars = uu____7290;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7333 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____7333 with
             | (env0, uu____7347) ->
                 let uu____7352 = tc_term env0 e1 in
                 (match uu____7352 with
                  | (e2, c, g) ->
                      let uu____7368 = FStar_Syntax_Util.head_and_args top in
                      (match uu____7368 with
                       | (reify_op, uu____7392) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ in
                           let uu____7418 =
                             FStar_TypeChecker_Common.lcomp_comp c in
                           (match uu____7418 with
                            | (c1, g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1 in
                                ((let uu____7433 =
                                    let uu____7434 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef in
                                    Prims.op_Negation uu____7434 in
                                  if uu____7433
                                  then
                                    let uu____7435 =
                                      let uu____7440 =
                                        let uu____7441 =
                                          FStar_Ident.string_of_lid ef in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7441 in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7440) in
                                    FStar_Errors.raise_error uu____7435
                                      e2.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let repr =
                                    FStar_TypeChecker_Env.reify_comp env1 c1
                                      u_c in
                                  let e3 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (reify_op, [(e2, aqual)]))
                                      top.FStar_Syntax_Syntax.pos in
                                  let c2 =
                                    let uu____7480 =
                                      FStar_TypeChecker_Env.is_total_effect
                                        env1 ef in
                                    if uu____7480
                                    then
                                      let uu____7481 =
                                        FStar_Syntax_Syntax.mk_Total repr in
                                      FStar_All.pipe_right uu____7481
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                    else
                                      (let ct =
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_c];
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Dv_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             repr;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       let uu____7492 =
                                         FStar_Syntax_Syntax.mk_Comp ct in
                                       FStar_All.pipe_right uu____7492
                                         FStar_TypeChecker_Common.lcomp_of_comp) in
                                  let uu____7493 =
                                    comp_check_expected_typ env1 e3 c2 in
                                  match uu____7493 with
                                  | (e4, c3, g') ->
                                      let uu____7509 =
                                        let uu____7510 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g' in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7510 in
                                      (e4, c3, uu____7509))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7512;
              FStar_Syntax_Syntax.vars = uu____7513;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7557 =
               let uu____7558 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l in
               Prims.op_Negation uu____7558 in
             if uu____7557
             then
               let uu____7559 =
                 let uu____7564 =
                   let uu____7565 = FStar_Ident.string_of_lid l in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7565 in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7564) in
               FStar_Errors.raise_error uu____7559 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7567 = FStar_Syntax_Util.head_and_args top in
             match uu____7567 with
             | (reflect_op, uu____7591) ->
                 let uu____7616 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____7616 with
                  | FStar_Pervasives_Native.None ->
                      let uu____7637 =
                        let uu____7642 =
                          let uu____7643 = FStar_Ident.string_of_lid l in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7643 in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7642) in
                      FStar_Errors.raise_error uu____7637
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____7662 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____7662 with
                       | (env_no_ex, uu____7676) ->
                           let uu____7681 =
                             let uu____7690 =
                               tc_tot_or_gtot_term env_no_ex e1 in
                             match uu____7690 with
                             | (e2, c, g) ->
                                 ((let uu____7709 =
                                     let uu____7710 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7710 in
                                   if uu____7709
                                   then
                                     FStar_Errors.log_issue
                                       e2.FStar_Syntax_Syntax.pos
                                       (FStar_Errors.Error_UnexpectedGTotComputation,
                                         "Expected Tot, got a GTot computation")
                                   else ());
                                  (e2, c, g)) in
                           (match uu____7681 with
                            | (e2, c_e, g_e) ->
                                let uu____7727 =
                                  let uu____7742 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____7742 with
                                  | (a, u_a) ->
                                      let uu____7763 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a in
                                      (match uu____7763 with
                                       | (a_uvar, uu____7791, g_a) ->
                                           let uu____7805 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar in
                                           (uu____7805, u_a, a_uvar, g_a)) in
                                (match uu____7727 with
                                 | ((expected_repr_typ, g_repr), u_a, a, g_a)
                                     ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ in
                                     let eff_args =
                                       let uu____7847 =
                                         let uu____7848 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ in
                                         uu____7848.FStar_Syntax_Syntax.n in
                                       match uu____7847 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7861, uu____7862::args) ->
                                           args
                                       | uu____7904 ->
                                           let uu____7905 =
                                             let uu____7910 =
                                               let uu____7911 =
                                                 FStar_Ident.string_of_lid l in
                                               let uu____7912 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ in
                                               let uu____7913 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7911 uu____7912
                                                 uu____7913 in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7910) in
                                           FStar_Errors.raise_error
                                             uu____7905
                                             top.FStar_Syntax_Syntax.pos in
                                     let c =
                                       let uu____7925 =
                                         FStar_Syntax_Syntax.mk_Comp
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [u_a];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               a;
                                             FStar_Syntax_Syntax.effect_args
                                               = eff_args;
                                             FStar_Syntax_Syntax.flags = []
                                           } in
                                       FStar_All.pipe_right uu____7925
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____7961 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____7961 with
                                      | (e4, c1, g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              e4.FStar_Syntax_Syntax.pos in
                                          let uu____7984 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g'] in
                                          (e5, c1, uu____7984))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8023 = FStar_Syntax_Util.head_and_args top in
           (match uu____8023 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,
            (uu____8073, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____8074))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8126 = FStar_Syntax_Util.head_and_args top in
           (match uu____8126 with
            | (head1, args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8201 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8410 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____8201 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let env0 = env1 in
           let env2 =
             let uu____8527 =
               let uu____8528 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____8528 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____8527 instantiate_both in
           ((let uu____8544 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____8544
             then
               let uu____8545 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____8546 = FStar_Syntax_Print.term_to_string top in
               let uu____8547 =
                 let uu____8548 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____8548
                   (fun uu___3_8554 ->
                      match uu___3_8554 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8545
                 uu____8546 uu____8547
             else ());
            (let uu____8559 = tc_term (no_inst env2) head in
             match uu____8559 with
             | (head1, chead, g_head) ->
                 let uu____8575 =
                   let uu____8580 = FStar_TypeChecker_Common.lcomp_comp chead in
                   FStar_All.pipe_right uu____8580
                     (fun uu____8597 ->
                        match uu____8597 with
                        | (c, g) ->
                            let uu____8608 =
                              FStar_TypeChecker_Env.conj_guard g_head g in
                            (c, uu____8608)) in
                 (match uu____8575 with
                  | (chead1, g_head1) ->
                      let uu____8617 =
                        let uu____8624 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8626 = FStar_Options.lax () in
                              Prims.op_Negation uu____8626))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1) in
                        if uu____8624
                        then
                          let uu____8633 =
                            let uu____8640 =
                              FStar_TypeChecker_Env.expected_typ env0 in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8640 in
                          match uu____8633 with | (e1, c, g) -> (e1, c, g)
                        else
                          (let uu____8653 =
                             FStar_TypeChecker_Env.expected_typ env0 in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8653) in
                      (match uu____8617 with
                       | (e1, c, g) ->
                           let uu____8665 =
                             let uu____8672 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c in
                             if uu____8672
                             then
                               let uu____8679 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ in
                               match uu____8679 with
                               | (e2, res_typ, implicits) ->
                                   let uu____8695 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ in
                                   (e2, uu____8695, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                           (match uu____8665 with
                            | (e2, c1, implicits) ->
                                ((let uu____8707 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme in
                                  if uu____8707
                                  then
                                    let uu____8708 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8708
                                  else ());
                                 (let uu____8710 =
                                    comp_check_expected_typ env0 e2 c1 in
                                  match uu____8710 with
                                  | (e3, c2, g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits in
                                      ((let uu____8729 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme in
                                        if uu____8729
                                        then
                                          let uu____8730 =
                                            FStar_Syntax_Print.term_to_string
                                              e3 in
                                          let uu____8731 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1 in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8730 uu____8731
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8733 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8756;
               FStar_Syntax_Syntax.lbunivs = uu____8757;
               FStar_Syntax_Syntax.lbtyp = uu____8758;
               FStar_Syntax_Syntax.lbeff = uu____8759;
               FStar_Syntax_Syntax.lbdef = uu____8760;
               FStar_Syntax_Syntax.lbattrs = uu____8761;
               FStar_Syntax_Syntax.lbpos = uu____8762;_}::[]),
            uu____8763)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8786), uu____8787) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8802;
               FStar_Syntax_Syntax.lbunivs = uu____8803;
               FStar_Syntax_Syntax.lbtyp = uu____8804;
               FStar_Syntax_Syntax.lbeff = uu____8805;
               FStar_Syntax_Syntax.lbdef = uu____8806;
               FStar_Syntax_Syntax.lbattrs = uu____8807;
               FStar_Syntax_Syntax.lbpos = uu____8808;_}::uu____8809),
            uu____8810)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____8835), uu____8836) ->
           check_inner_let_rec env1 top)
and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let uu____8859 =
        let uu____8860 = FStar_Syntax_Subst.compress top in
        uu____8860.FStar_Syntax_Syntax.n in
      match uu____8859 with
      | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
          let uu____8907 = FStar_TypeChecker_Env.clear_expected_typ env in
          (match uu____8907 with
           | (env1, topt) ->
               let env11 = instantiate_both env1 in
               let uu____8927 = tc_term env11 e1 in
               (match uu____8927 with
                | (e11, c1, g1) ->
                    let uu____8943 =
                      let uu____8954 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1 in
                      match uu____8954 with
                      | FStar_Pervasives_Native.Some (e12, c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None -> (e11, c1, eqns) in
                    (match uu____8943 with
                     | (e12, c11, eqns1) ->
                         let eqns2 = eqns1 in
                         let uu____9009 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None ->
                               let uu____9023 = FStar_Syntax_Util.type_u () in
                               (match uu____9023 with
                                | (k, uu____9035) ->
                                    let uu____9036 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k in
                                    (match uu____9036 with
                                     | (res_t, uu____9056, g) ->
                                         let uu____9070 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t in
                                         let uu____9071 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g in
                                         (uu____9070, res_t, uu____9071))) in
                         (match uu____9009 with
                          | (env_branches, res_t, g11) ->
                              ((let uu____9082 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme in
                                if uu____9082
                                then
                                  let uu____9083 =
                                    FStar_Syntax_Print.term_to_string res_t in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9083
                                else ());
                               (let guard_x =
                                  FStar_Syntax_Syntax.new_bv
                                    (FStar_Pervasives_Native.Some
                                       (e12.FStar_Syntax_Syntax.pos))
                                    c11.FStar_TypeChecker_Common.res_typ in
                                let t_eqns =
                                  FStar_All.pipe_right eqns2
                                    (FStar_List.map
                                       (tc_eqn guard_x env_branches)) in
                                let uu____9182 =
                                  let uu____9189 =
                                    FStar_List.fold_right
                                      (fun uu____9276 ->
                                         fun uu____9277 ->
                                           match (uu____9276, uu____9277)
                                           with
                                           | ((branch, f, eff_label, cflags,
                                               c, g, erasable_branch),
                                              (caccum, gaccum, erasable)) ->
                                               let uu____9527 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9527,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false) in
                                  match uu____9189 with
                                  | (cases, g, erasable) ->
                                      let uu____9628 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x in
                                      (uu____9628, g, erasable) in
                                match uu____9182 with
                                | (c_branches, g_branches, erasable) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches) in
                                    let cres1 =
                                      if erasable
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero) in
                                        let uu____9644 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9644
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9781 ->
                                                  match uu____9781 with
                                                  | ((pat, wopt, br),
                                                     uu____9827, eff_label,
                                                     uu____9829, uu____9830,
                                                     uu____9831, uu____9832)
                                                      ->
                                                      let uu____9867 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t in
                                                      (pat, wopt, uu____9867))) in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
                                            top.FStar_Syntax_Syntax.pos in
                                        let e2 =
                                          FStar_TypeChecker_Util.maybe_monadic
                                            env e
                                            cres1.FStar_TypeChecker_Common.eff_name
                                            cres1.FStar_TypeChecker_Common.res_typ in
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl
                                                   (cres1.FStar_TypeChecker_Common.res_typ)),
                                                 FStar_Pervasives_Native.None),
                                               (FStar_Pervasives_Native.Some
                                                  (cres1.FStar_TypeChecker_Common.eff_name))))
                                          e2.FStar_Syntax_Syntax.pos in
                                      let uu____9934 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name in
                                      if uu____9934
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____9939 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x in
                                           mk_match uu____9939 in
                                         let lb =
                                           let uu____9943 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____9943 e12 []
                                             e12.FStar_Syntax_Syntax.pos in
                                         let e =
                                           let uu____9949 =
                                             let uu____9950 =
                                               let uu____9963 =
                                                 let uu____9966 =
                                                   let uu____9967 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       guard_x in
                                                   [uu____9967] in
                                                 FStar_Syntax_Subst.close
                                                   uu____9966 e_match in
                                               ((false, [lb]), uu____9963) in
                                             FStar_Syntax_Syntax.Tm_let
                                               uu____9950 in
                                           FStar_Syntax_Syntax.mk uu____9949
                                             top.FStar_Syntax_Syntax.pos in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ) in
                                    ((let uu____9997 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme in
                                      if uu____9997
                                      then
                                        let uu____9998 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos in
                                        let uu____9999 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1 in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____9998 uu____9999
                                      else ());
                                     (let uu____10001 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches in
                                      (e, cres1, uu____10001)))))))))
      | uu____10002 ->
          let uu____10003 =
            let uu____10004 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format1 "tc_match called on %s\n" uu____10004 in
          failwith uu____10003
and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun head ->
    fun env ->
      fun args ->
        fun rng ->
          let uu____10027 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10066))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10106 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____10027 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____10137 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____10137 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____10141 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10141) in
              let uu____10142 =
                let uu____10149 =
                  let uu____10150 =
                    let uu____10151 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10151 in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10150 in
                tc_term uu____10149 typ in
              (match uu____10142 with
               | (typ1, uu____10167, g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10170 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau in
                     match uu____10170 with
                     | (tau1, uu____10184, g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1360_10189 = tau1 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1360_10189.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1360_10189.FStar_Syntax_Syntax.vars)
                                }) in
                           (let uu____10191 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac") in
                            if uu____10191
                            then
                              let uu____10192 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print1 "Got %s\n" uu____10192
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10195 =
                              let uu____10196 =
                                FStar_Syntax_Syntax.mk_Total typ1 in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10196 in
                            (t, uu____10195,
                              FStar_TypeChecker_Env.trivial_guard)))))))
and (tc_tactic :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun a ->
    fun b ->
      fun env ->
        fun tau ->
          let env1 =
            let uu___1370_10202 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1370_10202.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1370_10202.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1370_10202.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1370_10202.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1370_10202.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1370_10202.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1370_10202.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1370_10202.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1370_10202.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1370_10202.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1370_10202.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1370_10202.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1370_10202.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1370_10202.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1370_10202.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1370_10202.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1370_10202.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1370_10202.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1370_10202.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1370_10202.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1370_10202.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1370_10202.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1370_10202.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1370_10202.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1370_10202.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1370_10202.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1370_10202.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1370_10202.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1370_10202.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1370_10202.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1370_10202.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1370_10202.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1370_10202.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1370_10202.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1370_10202.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1370_10202.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1370_10202.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1370_10202.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1370_10202.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1370_10202.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1370_10202.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1370_10202.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1370_10202.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1370_10202.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1370_10202.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1370_10202.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____10203 = FStar_Syntax_Syntax.t_tac_of a b in
          tc_check_tot_or_gtot_term env1 tau uu____10203 ""
and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun topt ->
      match topt with
      | FStar_Pervasives_Native.None ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____10217 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic in
          (match uu____10217 with
           | (tactic1, uu____10231, g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))
and (check_instantiated_fvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.var ->
      FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun v ->
      fun q ->
        fun e ->
          fun t0 ->
            let is_data_ctor uu___4_10255 =
              match uu___4_10255 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10258) -> true
              | uu____10265 -> false in
            (let uu____10269 =
               (is_data_ctor q) &&
                 (let uu____10271 =
                    FStar_TypeChecker_Env.is_datacon env
                      v.FStar_Syntax_Syntax.v in
                  Prims.op_Negation uu____10271) in
             if uu____10269
             then
               let uu____10272 =
                 let uu____10277 =
                   let uu____10278 =
                     FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v in
                   FStar_Util.format1 "Expected a data constructor; got %s"
                     uu____10278 in
                 (FStar_Errors.Fatal_MissingDataConstructor, uu____10277) in
               let uu____10279 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____10272 uu____10279
             else ());
            (let t = FStar_Syntax_Util.remove_inacc t0 in
             let uu____10282 =
               FStar_TypeChecker_Util.maybe_instantiate env e t in
             match uu____10282 with
             | (e1, t1, implicits) ->
                 let tc =
                   let uu____10303 = FStar_TypeChecker_Env.should_verify env in
                   if uu____10303
                   then FStar_Util.Inl t1
                   else
                     (let uu____10309 =
                        let uu____10310 = FStar_Syntax_Syntax.mk_Total t1 in
                        FStar_All.pipe_left
                          FStar_TypeChecker_Common.lcomp_of_comp uu____10310 in
                      FStar_Util.Inr uu____10309) in
                 value_check_expected_typ env e1 tc implicits)
and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10328 =
            let uu____10333 =
              let uu____10334 = FStar_Syntax_Print.term_to_string top in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10334 in
            (FStar_Errors.Error_IllScopedTerm, uu____10333) in
          FStar_Errors.raise_error uu____10328 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____10359 =
            let uu____10364 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____10364 in
          value_check_expected_typ env1 e uu____10359
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____10366 =
            let uu____10379 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____10379 with
            | FStar_Pervasives_Native.None ->
                let uu____10394 = FStar_Syntax_Util.type_u () in
                (match uu____10394 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____10366 with
           | (t, uu____10431, g0) ->
               let uu____10445 =
                 let uu____10458 =
                   let uu____10459 = FStar_Range.string_of_range r in
                   Prims.op_Hat "user-provided implicit term at " uu____10459 in
                 FStar_TypeChecker_Util.new_implicit_var uu____10458 r env1 t in
               (match uu____10445 with
                | (e1, uu____10467, g1) ->
                    let uu____10481 =
                      let uu____10482 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____10482
                        FStar_TypeChecker_Common.lcomp_of_comp in
                    let uu____10483 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____10481, uu____10483)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10485 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10494 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____10494)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____10485 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1436_10507 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1436_10507.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1436_10507.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____10510 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____10510 with
                 | (e2, t1, implicits) ->
                     let tc =
                       let uu____10531 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____10531
                       then FStar_Util.Inl t1
                       else
                         (let uu____10537 =
                            let uu____10538 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10538 in
                          FStar_Util.Inr uu____10537) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10540;
             FStar_Syntax_Syntax.vars = uu____10541;_},
           uu____10542)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10547 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10547
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10555 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10555
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10563;
             FStar_Syntax_Syntax.vars = uu____10564;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____10573 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10573 with
           | ((us', t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10598 =
                     let uu____10603 =
                       let uu____10604 = FStar_Syntax_Print.fv_to_string fv1 in
                       let uu____10605 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____10606 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10604 uu____10605 uu____10606 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10603) in
                   let uu____10607 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____10598 uu____10607)
                else ();
                FStar_List.iter2
                  (fun ul ->
                     fun ur ->
                       match (ul, ur) with
                       | (FStar_Syntax_Syntax.U_unif u'', uu____10617) ->
                           FStar_Syntax_Unionfind.univ_change u'' ur
                       | (FStar_Syntax_Syntax.U_name n1,
                          FStar_Syntax_Syntax.U_name n2) when
                           FStar_Ident.ident_equals n1 n2 -> ()
                       | uu____10630 ->
                           let uu____10635 =
                             let uu____10640 =
                               let uu____10641 =
                                 FStar_Syntax_Print.fv_to_string fv1 in
                               let uu____10642 =
                                 FStar_Syntax_Print.univ_to_string ul in
                               let uu____10643 =
                                 FStar_Syntax_Print.univ_to_string ur in
                               FStar_Util.format3
                                 "Incompatible universe application for %s, expected %s got %s\n"
                                 uu____10641 uu____10642 uu____10643 in
                             (FStar_Errors.Fatal_IncompatibleUniverse,
                               uu____10640) in
                           let uu____10644 =
                             FStar_TypeChecker_Env.get_range env1 in
                           FStar_Errors.raise_error uu____10635 uu____10644)
                  us' us1;
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10647 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10647 us1 in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10648, us) ->
          let uu____10654 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10654
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10662 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10662 with
           | ((us, t), range) ->
               let fv1 = FStar_Syntax_Syntax.set_range_of_fv fv range in
               (maybe_warn_on_use env1 fv1;
                (let uu____10687 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____10687
                 then
                   let uu____10688 =
                     let uu____10689 = FStar_Syntax_Syntax.lid_of_fv fv1 in
                     FStar_Syntax_Print.lid_to_string uu____10689 in
                   let uu____10690 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____10691 = FStar_Range.string_of_range range in
                   let uu____10692 = FStar_Range.string_of_use_range range in
                   let uu____10693 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s\n"
                     uu____10688 uu____10690 uu____10691 uu____10692
                     uu____10693
                 else ());
                FStar_TypeChecker_Env.insert_fv_info env1 fv1 t;
                (let e1 =
                   let uu____10697 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____10697 us in
                 check_instantiated_fvar env1 fv1.FStar_Syntax_Syntax.fv_name
                   fv1.FStar_Syntax_Syntax.fv_qual e1 t)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____10725 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10725 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____10739 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10739 with
                | (env2, uu____10753) ->
                    let uu____10758 = tc_binders env2 bs1 in
                    (match uu____10758 with
                     | (bs2, env3, g, us) ->
                         let uu____10777 = tc_comp env3 c1 in
                         (match uu____10777 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___1530_10796 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1530_10796.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1530_10796.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____10807 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10807 in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 false bs2 g1 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____10823 =
            let uu____10828 =
              let uu____10829 = FStar_Syntax_Syntax.mk_binder x in
              [uu____10829] in
            FStar_Syntax_Subst.open_term uu____10828 phi in
          (match uu____10823 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____10857 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____10857 with
                | (env2, uu____10871) ->
                    let uu____10876 =
                      let uu____10891 = FStar_List.hd x1 in
                      tc_binder env2 uu____10891 in
                    (match uu____10876 with
                     | (x2, env3, f1, u) ->
                         ((let uu____10927 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____10927
                           then
                             let uu____10928 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____10929 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____10930 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10928 uu____10929 uu____10930
                           else ());
                          (let uu____10934 = FStar_Syntax_Util.type_u () in
                           match uu____10934 with
                           | (t_phi, uu____10946) ->
                               let uu____10947 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost" in
                               (match uu____10947 with
                                | (phi2, uu____10961, f2) ->
                                    let e1 =
                                      let uu___1568_10966 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1568_10966.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1568_10966.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____10975 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10975 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____11003) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____11030 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
            if uu____11030
            then
              let uu____11031 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1581_11034 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1581_11034.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1581_11034.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11031
            else ());
           (let uu____11048 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____11048 with
            | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____11061 ->
          let uu____11062 =
            let uu____11063 = FStar_Syntax_Print.term_to_string top in
            let uu____11064 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11063
              uu____11064 in
          failwith uu____11062
and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun r ->
      fun c ->
        let res =
          match c with
          | FStar_Const.Const_unit -> FStar_Syntax_Syntax.t_unit
          | FStar_Const.Const_bool uu____11075 -> FStar_Syntax_Util.t_bool
          | FStar_Const.Const_int (uu____11076, FStar_Pervasives_Native.None)
              -> FStar_Syntax_Syntax.t_int
          | FStar_Const.Const_int
              (uu____11087, FStar_Pervasives_Native.Some msize) ->
              FStar_Syntax_Syntax.tconst
                (match msize with
                 | (FStar_Const.Signed, FStar_Const.Int8) ->
                     FStar_Parser_Const.int8_lid
                 | (FStar_Const.Signed, FStar_Const.Int16) ->
                     FStar_Parser_Const.int16_lid
                 | (FStar_Const.Signed, FStar_Const.Int32) ->
                     FStar_Parser_Const.int32_lid
                 | (FStar_Const.Signed, FStar_Const.Int64) ->
                     FStar_Parser_Const.int64_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int8) ->
                     FStar_Parser_Const.uint8_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int16) ->
                     FStar_Parser_Const.uint16_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int32) ->
                     FStar_Parser_Const.uint32_lid
                 | (FStar_Const.Unsigned, FStar_Const.Int64) ->
                     FStar_Parser_Const.uint64_lid)
          | FStar_Const.Const_string uu____11103 ->
              FStar_Syntax_Syntax.t_string
          | FStar_Const.Const_real uu____11108 -> FStar_Syntax_Syntax.t_real
          | FStar_Const.Const_float uu____11109 ->
              FStar_Syntax_Syntax.t_float
          | FStar_Const.Const_char uu____11110 ->
              let uu____11111 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____11111 FStar_Util.must
          | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
          | FStar_Const.Const_range uu____11116 ->
              FStar_Syntax_Syntax.t_range
          | FStar_Const.Const_range_of ->
              let uu____11117 =
                let uu____11122 =
                  let uu____11123 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11123 in
                (FStar_Errors.Fatal_IllTyped, uu____11122) in
              FStar_Errors.raise_error uu____11117 r
          | FStar_Const.Const_set_range_of ->
              let uu____11124 =
                let uu____11129 =
                  let uu____11130 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11130 in
                (FStar_Errors.Fatal_IllTyped, uu____11129) in
              FStar_Errors.raise_error uu____11124 r
          | FStar_Const.Const_reify ->
              let uu____11131 =
                let uu____11136 =
                  let uu____11137 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11137 in
                (FStar_Errors.Fatal_IllTyped, uu____11136) in
              FStar_Errors.raise_error uu____11131 r
          | FStar_Const.Const_reflect uu____11138 ->
              let uu____11139 =
                let uu____11144 =
                  let uu____11145 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____11145 in
                (FStar_Errors.Fatal_IllTyped, uu____11144) in
              FStar_Errors.raise_error uu____11139 r
          | uu____11146 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnsupportedConstant,
                  "Unsupported constant") r in
        FStar_Syntax_Subst.set_use_range r res
and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uu____11163) ->
          let uu____11172 = FStar_Syntax_Util.type_u () in
          (match uu____11172 with
           | (k, u) ->
               let uu____11185 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11185 with
                | (t1, uu____11199, g) ->
                    let uu____11201 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11201, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____11203) ->
          let uu____11212 = FStar_Syntax_Util.type_u () in
          (match uu____11212 with
           | (k, u) ->
               let uu____11225 = tc_check_tot_or_gtot_term env t k "" in
               (match uu____11225 with
                | (t1, uu____11239, g) ->
                    let uu____11241 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____11241, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let head1 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head, us))
                  c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____11249 =
              let uu____11250 =
                FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ in
              uu____11250 :: (c1.FStar_Syntax_Syntax.effect_args) in
            FStar_Syntax_Syntax.mk_Tm_app head1 uu____11249
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____11267 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff "" in
          (match uu____11267 with
           | (tc1, uu____11281, f) ->
               let uu____11283 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____11283 with
                | (head2, args) ->
                    let comp_univs =
                      let uu____11333 =
                        let uu____11334 = FStar_Syntax_Subst.compress head2 in
                        uu____11334.FStar_Syntax_Syntax.n in
                      match uu____11333 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11337, us) -> us
                      | uu____11343 -> [] in
                    let uu____11344 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____11344 with
                     | (uu____11367, args1) ->
                         let uu____11393 =
                           let uu____11416 = FStar_List.hd args1 in
                           let uu____11433 = FStar_List.tl args1 in
                           (uu____11416, uu____11433) in
                         (match uu____11393 with
                          | (res, args2) ->
                              let uu____11514 =
                                let uu____11523 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11551 ->
                                          match uu___5_11551 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11559 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____11559 with
                                               | (env1, uu____11571) ->
                                                   let uu____11576 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____11576 with
                                                    | (e1, uu____11588, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____11523
                                  FStar_List.unzip in
                              (match uu____11514 with
                               | (flags, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1711_11629 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1711_11629.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags = flags
                                        }) in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u) in
                                   let uu____11635 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____11635))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11645 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11646 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11658 = aux u3 in
            FStar_Syntax_Syntax.U_succ uu____11658
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11662 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____11662
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11666 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____11666
            then u2
            else
              (let uu____11668 =
                 let uu____11669 =
                   let uu____11670 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.op_Hat uu____11670 " not found" in
                 Prims.op_Hat "Universe variable " uu____11669 in
               failwith uu____11668) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____11672 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____11672 FStar_Pervasives_Native.snd
         | uu____11681 -> aux u)
and (tc_abs_expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option *
            FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun bs ->
      fun t0 ->
        fun body ->
          match t0 with
          | FStar_Pervasives_Native.None ->
              ((match env.FStar_TypeChecker_Env.letrecs with
                | [] -> ()
                | uu____11715 ->
                    failwith
                      "Impossible: Can't have a let rec annotation but no expected type");
               (let uu____11726 = tc_binders env bs in
                match uu____11726 with
                | (bs1, envbody, g_env, uu____11756) ->
                    (FStar_Pervasives_Native.None, bs1, [],
                      FStar_Pervasives_Native.None, envbody, body, g_env)))
          | FStar_Pervasives_Native.Some t ->
              let t1 = FStar_Syntax_Subst.compress t in
              let rec as_function_typ norm1 t2 =
                let uu____11800 =
                  let uu____11801 = FStar_Syntax_Subst.compress t2 in
                  uu____11801.FStar_Syntax_Syntax.n in
                match uu____11800 with
                | FStar_Syntax_Syntax.Tm_uvar uu____11824 ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11846 -> failwith "Impossible");
                     (let uu____11857 = tc_binders env bs in
                      match uu____11857 with
                      | (bs1, envbody, g_env, uu____11889) ->
                          let uu____11890 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____11890 with
                           | (envbody1, uu____11918) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____11929;
                       FStar_Syntax_Syntax.pos = uu____11930;
                       FStar_Syntax_Syntax.vars = uu____11931;_},
                     uu____11932)
                    ->
                    ((match env.FStar_TypeChecker_Env.letrecs with
                      | [] -> ()
                      | uu____11978 -> failwith "Impossible");
                     (let uu____11989 = tc_binders env bs in
                      match uu____11989 with
                      | (bs1, envbody, g_env, uu____12021) ->
                          let uu____12022 =
                            FStar_TypeChecker_Env.clear_expected_typ envbody in
                          (match uu____12022 with
                           | (envbody1, uu____12050) ->
                               ((FStar_Pervasives_Native.Some t2), bs1, [],
                                 FStar_Pervasives_Native.None, envbody1,
                                 body, g_env))))
                | FStar_Syntax_Syntax.Tm_refine (b, uu____12062) ->
                    let uu____12067 =
                      as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                    (match uu____12067 with
                     | (uu____12108, bs1, bs', copt, env_body, body1, g_env)
                         ->
                         ((FStar_Pervasives_Native.Some t2), bs1, bs', copt,
                           env_body, body1, g_env))
                | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                    let uu____12155 =
                      FStar_Syntax_Subst.open_comp bs_expected c_expected in
                    (match uu____12155 with
                     | (bs_expected1, c_expected1) ->
                         let check_actuals_against_formals env1 bs1
                           bs_expected2 body1 =
                           let rec handle_more uu____12290 c_expected2 body2
                             =
                             match uu____12290 with
                             | (env_bs, bs2, more, guard_env, subst) ->
                                 (match more with
                                  | FStar_Pervasives_Native.None ->
                                      let uu____12404 =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      (env_bs, bs2, guard_env, uu____12404,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inr more_bs_expected) ->
                                      let c =
                                        let uu____12421 =
                                          FStar_Syntax_Util.arrow
                                            more_bs_expected c_expected2 in
                                        FStar_Syntax_Syntax.mk_Total
                                          uu____12421 in
                                      let uu____12422 =
                                        FStar_Syntax_Subst.subst_comp subst c in
                                      (env_bs, bs2, guard_env, uu____12422,
                                        body2)
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Util.Inl more_bs) ->
                                      let c =
                                        FStar_Syntax_Subst.subst_comp subst
                                          c_expected2 in
                                      let uu____12439 =
                                        (FStar_Options.ml_ish ()) ||
                                          (FStar_Syntax_Util.is_named_tot c) in
                                      if uu____12439
                                      then
                                        let t3 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env_bs
                                            (FStar_Syntax_Util.comp_result c) in
                                        (match t3.FStar_Syntax_Syntax.n with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs_expected3, c_expected3) ->
                                             let uu____12503 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs_expected3 c_expected3 in
                                             (match uu____12503 with
                                              | (bs_expected4, c_expected4)
                                                  ->
                                                  let uu____12530 =
                                                    tc_abs_check_binders
                                                      env_bs more_bs
                                                      bs_expected4 in
                                                  (match uu____12530 with
                                                   | (env_bs_bs', bs', more1,
                                                      guard'_env_bs, subst1)
                                                       ->
                                                       let guard'_env =
                                                         FStar_TypeChecker_Env.close_guard
                                                           env_bs bs2
                                                           guard'_env_bs in
                                                       let uu____12585 =
                                                         let uu____12612 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard_env
                                                             guard'_env in
                                                         (env_bs_bs',
                                                           (FStar_List.append
                                                              bs2 bs'),
                                                           more1,
                                                           uu____12612,
                                                           subst1) in
                                                       handle_more
                                                         uu____12585
                                                         c_expected4 body2))
                                         | uu____12635 ->
                                             let body3 =
                                               FStar_Syntax_Util.abs more_bs
                                                 body2
                                                 FStar_Pervasives_Native.None in
                                             (env_bs, bs2, guard_env, c,
                                               body3))
                                      else
                                        (let body3 =
                                           FStar_Syntax_Util.abs more_bs
                                             body2
                                             FStar_Pervasives_Native.None in
                                         (env_bs, bs2, guard_env, c, body3))) in
                           let uu____12663 =
                             tc_abs_check_binders env1 bs1 bs_expected2 in
                           handle_more uu____12663 c_expected1 body1 in
                         let mk_letrec_env envbody bs1 c =
                           let letrecs = guard_letrecs envbody bs1 c in
                           let envbody1 =
                             let uu___1842_12728 = envbody in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1842_12728.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1842_12728.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1842_12728.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1842_12728.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1842_12728.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1842_12728.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1842_12728.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1842_12728.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1842_12728.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1842_12728.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1842_12728.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1842_12728.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1842_12728.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs = [];
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1842_12728.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1842_12728.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1842_12728.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1842_12728.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1842_12728.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1842_12728.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1842_12728.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1842_12728.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1842_12728.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1842_12728.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1842_12728.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1842_12728.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1842_12728.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1842_12728.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1842_12728.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1842_12728.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1842_12728.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1842_12728.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1842_12728.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1842_12728.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1842_12728.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1842_12728.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1842_12728.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1842_12728.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1842_12728.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1842_12728.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1842_12728.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1842_12728.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1842_12728.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1842_12728.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1842_12728.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1842_12728.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (uu___1842_12728.FStar_TypeChecker_Env.enable_defer_to_tac)
                             } in
                           let uu____12737 =
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____12803 ->
                                     fun uu____12804 ->
                                       match (uu____12803, uu____12804) with
                                       | ((env1, letrec_binders, g),
                                          (l, t3, u_names)) ->
                                           let uu____12895 =
                                             let uu____12902 =
                                               let uu____12903 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env1 in
                                               FStar_All.pipe_right
                                                 uu____12903
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____12902 t3 in
                                           (match uu____12895 with
                                            | (t4, uu____12927, g') ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env1 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____12940 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___1860_12943
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___1860_12943.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___1860_12943.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____12940 ::
                                                        letrec_binders
                                                  | uu____12944 ->
                                                      letrec_binders in
                                                let uu____12949 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g' in
                                                (env2, lb, uu____12949)))
                                  (envbody1, [],
                                    FStar_TypeChecker_Env.trivial_guard)) in
                           match uu____12737 with
                           | (envbody2, letrec_binders, g) ->
                               let uu____12969 =
                                 FStar_TypeChecker_Env.close_guard envbody2
                                   bs1 g in
                               (envbody2, letrec_binders, uu____12969) in
                         let envbody =
                           let uu___1868_12973 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1868_12973.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1868_12973.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1868_12973.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1868_12973.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1868_12973.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1868_12973.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1868_12973.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1868_12973.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1868_12973.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1868_12973.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1868_12973.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1868_12973.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1868_12973.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs = [];
                             FStar_TypeChecker_Env.top_level =
                               (uu___1868_12973.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1868_12973.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1868_12973.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1868_12973.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1868_12973.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1868_12973.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___1868_12973.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1868_12973.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1868_12973.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1868_12973.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1868_12973.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1868_12973.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1868_12973.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1868_12973.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1868_12973.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1868_12973.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1868_12973.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1868_12973.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1868_12973.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1868_12973.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1868_12973.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1868_12973.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1868_12973.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1868_12973.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1868_12973.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1868_12973.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1868_12973.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1868_12973.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1868_12973.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1868_12973.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1868_12973.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1868_12973.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1868_12973.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let uu____12982 =
                           check_actuals_against_formals envbody bs
                             bs_expected1 body in
                         (match uu____12982 with
                          | (envbody1, bs1, g_env, c, body1) ->
                              let envbody2 =
                                let uu___1877_13019 = envbody1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1877_13019.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1877_13019.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1877_13019.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1877_13019.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1877_13019.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1877_13019.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1877_13019.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1877_13019.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1877_13019.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1877_13019.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1877_13019.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1877_13019.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1877_13019.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1877_13019.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1877_13019.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1877_13019.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1877_13019.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1877_13019.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1877_13019.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1877_13019.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1877_13019.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1877_13019.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1877_13019.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1877_13019.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1877_13019.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1877_13019.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1877_13019.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1877_13019.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1877_13019.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1877_13019.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1877_13019.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1877_13019.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1877_13019.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1877_13019.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1877_13019.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1877_13019.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1877_13019.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1877_13019.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1877_13019.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1877_13019.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1877_13019.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1877_13019.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1877_13019.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1877_13019.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1877_13019.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1877_13019.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____13020 = mk_letrec_env envbody2 bs1 c in
                              (match uu____13020 with
                               | (envbody3, letrecs, g_annots) ->
                                   let envbody4 =
                                     FStar_TypeChecker_Env.set_expected_typ
                                       envbody3
                                       (FStar_Syntax_Util.comp_result c) in
                                   let uu____13057 =
                                     FStar_TypeChecker_Env.conj_guard g_env
                                       g_annots in
                                   ((FStar_Pervasives_Native.Some t2), bs1,
                                     letrecs,
                                     (FStar_Pervasives_Native.Some c),
                                     envbody4, body1, uu____13057))))
                | uu____13064 ->
                    if Prims.op_Negation norm1
                    then
                      let uu____13085 =
                        let uu____13086 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.unfold_whnf env) in
                        FStar_All.pipe_right uu____13086
                          FStar_Syntax_Util.unascribe in
                      as_function_typ true uu____13085
                    else
                      (let uu____13088 =
                         tc_abs_expected_function_typ env bs
                           FStar_Pervasives_Native.None body in
                       match uu____13088 with
                       | (uu____13127, bs1, uu____13129, c_opt, envbody,
                          body1, g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, [],
                             c_opt, envbody, body1, g_env)) in
              as_function_typ false t1
and (tc_abs_check_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binders *
          (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.binders)
          FStar_Util.either FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.subst_t))
  =
  fun env ->
    fun bs ->
      fun bs_expected ->
        let rec aux uu____13202 bs1 bs_expected1 =
          match uu____13202 with
          | (env1, subst) ->
              (match (bs1, bs_expected1) with
               | ([], []) ->
                   (env1, [], FStar_Pervasives_Native.None,
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ((uu____13309, FStar_Pervasives_Native.None)::uu____13310,
                  (hd_e, q)::uu____13313) when
                   FStar_Syntax_Syntax.is_implicit_or_meta q ->
                   let bv =
                     let uu____13365 =
                       let uu____13368 =
                         FStar_Ident.range_of_id
                           hd_e.FStar_Syntax_Syntax.ppname in
                       FStar_Pervasives_Native.Some uu____13368 in
                     let uu____13369 =
                       FStar_Syntax_Subst.subst subst
                         hd_e.FStar_Syntax_Syntax.sort in
                     FStar_Syntax_Syntax.new_bv uu____13365 uu____13369 in
                   aux (env1, subst) ((bv, q) :: bs1) bs_expected1
               | ((hd, imp)::bs2, (hd_expected, imp')::bs_expected2) ->
                   ((let special q1 q2 =
                       match (q1, q2) with
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13462),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13463)) -> true
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Equality)) -> true
                       | (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13472),
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____13473)) -> true
                       | uu____13478 -> false in
                     let uu____13487 =
                       (Prims.op_Negation (special imp imp')) &&
                         (let uu____13489 =
                            FStar_Syntax_Util.eq_aqual imp imp' in
                          uu____13489 <> FStar_Syntax_Util.Equal) in
                     if uu____13487
                     then
                       let uu____13490 =
                         let uu____13495 =
                           let uu____13496 =
                             FStar_Syntax_Print.bv_to_string hd in
                           FStar_Util.format1
                             "Inconsistent implicit argument annotation on argument %s"
                             uu____13496 in
                         (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                           uu____13495) in
                       let uu____13497 = FStar_Syntax_Syntax.range_of_bv hd in
                       FStar_Errors.raise_error uu____13490 uu____13497
                     else ());
                    (let expected_t =
                       FStar_Syntax_Subst.subst subst
                         hd_expected.FStar_Syntax_Syntax.sort in
                     let uu____13500 =
                       let uu____13507 =
                         let uu____13508 =
                           FStar_Syntax_Util.unmeta
                             hd.FStar_Syntax_Syntax.sort in
                         uu____13508.FStar_Syntax_Syntax.n in
                       match uu____13507 with
                       | FStar_Syntax_Syntax.Tm_unknown ->
                           (expected_t, FStar_TypeChecker_Env.trivial_guard)
                       | uu____13519 ->
                           ((let uu____13521 =
                               FStar_TypeChecker_Env.debug env1
                                 FStar_Options.High in
                             if uu____13521
                             then
                               let uu____13522 =
                                 FStar_Syntax_Print.bv_to_string hd in
                               FStar_Util.print1 "Checking binder %s\n"
                                 uu____13522
                             else ());
                            (let uu____13524 =
                               tc_tot_or_gtot_term env1
                                 hd.FStar_Syntax_Syntax.sort in
                             match uu____13524 with
                             | (t, uu____13538, g1_env) ->
                                 let g2_env =
                                   let uu____13541 =
                                     FStar_TypeChecker_Rel.teq_nosmt env1 t
                                       expected_t in
                                   match uu____13541 with
                                   | FStar_Pervasives_Native.Some g ->
                                       FStar_All.pipe_right g
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env1)
                                   | FStar_Pervasives_Native.None ->
                                       let uu____13545 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env1 expected_t t in
                                       (match uu____13545 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____13548 =
                                              FStar_TypeChecker_Err.basic_type_error
                                                env1
                                                FStar_Pervasives_Native.None
                                                expected_t t in
                                            let uu____13553 =
                                              FStar_TypeChecker_Env.get_range
                                                env1 in
                                            FStar_Errors.raise_error
                                              uu____13548 uu____13553
                                        | FStar_Pervasives_Native.Some g_env
                                            ->
                                            FStar_TypeChecker_Util.label_guard
                                              (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                              "Type annotation on parameter incompatible with the expected type"
                                              g_env) in
                                 let uu____13555 =
                                   FStar_TypeChecker_Env.conj_guard g1_env
                                     g2_env in
                                 (t, uu____13555))) in
                     match uu____13500 with
                     | (t, g_env) ->
                         let hd1 =
                           let uu___1973_13581 = hd in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1973_13581.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1973_13581.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t
                           } in
                         let b = (hd1, imp) in
                         let b_expected = (hd_expected, imp') in
                         let env_b = push_binding env1 b in
                         let subst1 =
                           let uu____13604 =
                             FStar_Syntax_Syntax.bv_to_name hd1 in
                           maybe_extend_subst subst b_expected uu____13604 in
                         let uu____13607 =
                           aux (env_b, subst1) bs2 bs_expected2 in
                         (match uu____13607 with
                          | (env_bs, bs3, rest, g'_env_b, subst2) ->
                              let g'_env =
                                FStar_TypeChecker_Env.close_guard env_bs 
                                  [b] g'_env_b in
                              let uu____13672 =
                                FStar_TypeChecker_Env.conj_guard g_env g'_env in
                              (env_bs, (b :: bs3), rest, uu____13672, subst2))))
               | (rest, []) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst)
               | ([], rest) ->
                   (env1, [],
                     (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                     FStar_TypeChecker_Env.trivial_guard, subst)) in
        aux (env, []) bs bs_expected
and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      fun bs ->
        fun body ->
          let fail msg t =
            let uu____13809 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____13809 top.FStar_Syntax_Syntax.pos in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____13815 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____13815 with
          | (env1, topt) ->
              ((let uu____13835 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____13835
                then
                  let uu____13836 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13836
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13840 =
                  tc_abs_expected_function_typ env1 bs topt body in
                match uu____13840 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____13881 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme in
                      if uu____13881
                      then
                        let uu____13882 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        let uu____13884 =
                          match c_opt with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t in
                        let uu____13886 =
                          let uu____13887 =
                            FStar_TypeChecker_Env.expected_typ envbody in
                          match uu____13887 with
                          | FStar_Pervasives_Native.None -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13882 uu____13884 uu____13886
                      else ());
                     (let uu____13893 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____13893
                      then
                        let uu____13894 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____13895 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13894 uu____13895
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____13898 =
                        let uu____13909 =
                          let uu____13916 =
                            (FStar_All.pipe_right c_opt FStar_Util.is_some)
                              &&
                              (let uu____13924 =
                                 let uu____13925 =
                                   FStar_Syntax_Subst.compress body1 in
                                 uu____13925.FStar_Syntax_Syntax.n in
                               match uu____13924 with
                               | FStar_Syntax_Syntax.Tm_app (head, args) when
                                   (FStar_List.length args) = Prims.int_one
                                   ->
                                   let uu____13962 =
                                     let uu____13963 =
                                       FStar_Syntax_Subst.compress head in
                                     uu____13963.FStar_Syntax_Syntax.n in
                                   (match uu____13962 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reflect
                                        uu____13966) -> true
                                    | uu____13967 -> false)
                               | uu____13968 -> false) in
                          if uu____13916
                          then
                            let uu____13975 =
                              let uu____13976 =
                                FStar_TypeChecker_Env.clear_expected_typ
                                  envbody1 in
                              FStar_All.pipe_right uu____13976
                                FStar_Pervasives_Native.fst in
                            let uu____13991 =
                              let uu____13992 =
                                let uu____13993 =
                                  let uu____14020 =
                                    let uu____14037 =
                                      let uu____14046 =
                                        FStar_All.pipe_right c_opt
                                          FStar_Util.must in
                                      FStar_Util.Inr uu____14046 in
                                    (uu____14037,
                                      FStar_Pervasives_Native.None) in
                                  (body1, uu____14020,
                                    FStar_Pervasives_Native.None) in
                                FStar_Syntax_Syntax.Tm_ascribed uu____13993 in
                              FStar_Syntax_Syntax.mk uu____13992
                                FStar_Range.dummyRange in
                            (uu____13975, uu____13991, false)
                          else
                            (let uu____14092 =
                               let uu____14093 =
                                 let uu____14100 =
                                   let uu____14101 =
                                     FStar_Syntax_Subst.compress body1 in
                                   uu____14101.FStar_Syntax_Syntax.n in
                                 (c_opt, uu____14100) in
                               match uu____14093 with
                               | (FStar_Pervasives_Native.None,
                                  FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____14106,
                                   (FStar_Util.Inr expected_c, uu____14108),
                                   uu____14109)) -> false
                               | uu____14158 -> true in
                             (envbody1, body1, uu____14092)) in
                        match uu____13909 with
                        | (envbody2, body2, should_check_expected_effect) ->
                            let uu____14178 =
                              tc_term
                                (let uu___2058_14187 = envbody2 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2058_14187.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2058_14187.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2058_14187.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2058_14187.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2058_14187.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2058_14187.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2058_14187.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2058_14187.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2058_14187.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2058_14187.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2058_14187.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2058_14187.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2058_14187.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2058_14187.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level = false;
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2058_14187.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___2058_14187.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2058_14187.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2058_14187.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___2058_14187.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2058_14187.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2058_14187.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2058_14187.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2058_14187.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2058_14187.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2058_14187.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2058_14187.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2058_14187.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2058_14187.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2058_14187.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2058_14187.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2058_14187.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2058_14187.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2058_14187.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2058_14187.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___2058_14187.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2058_14187.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___2058_14187.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2058_14187.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2058_14187.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2058_14187.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2058_14187.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2058_14187.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___2058_14187.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___2058_14187.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___2058_14187.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) body2 in
                            (match uu____14178 with
                             | (body3, cbody, guard_body) ->
                                 let guard_body1 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     envbody2 guard_body in
                                 if should_check_expected_effect
                                 then
                                   let uu____14212 =
                                     FStar_TypeChecker_Common.lcomp_comp
                                       cbody in
                                   (match uu____14212 with
                                    | (cbody1, g_lc) ->
                                        let uu____14229 =
                                          check_expected_effect
                                            (let uu___2069_14238 = envbody2 in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 use_eq;
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.lax);
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.phase1);
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___2069_14238.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) c_opt (body3, cbody1) in
                                        (match uu____14229 with
                                         | (body4, cbody2, guard) ->
                                             let uu____14252 =
                                               let uu____14253 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_lc guard in
                                               FStar_TypeChecker_Env.conj_guard
                                                 guard_body1 uu____14253 in
                                             (body4, cbody2, uu____14252)))
                                 else
                                   (let uu____14259 =
                                      FStar_TypeChecker_Common.lcomp_comp
                                        cbody in
                                    match uu____14259 with
                                    | (cbody1, g_lc) ->
                                        let uu____14276 =
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 g_lc in
                                        (body3, cbody1, uu____14276))) in
                      match uu____13898 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____14299 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14301 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____14301) in
                            if uu____14299
                            then
                              let uu____14302 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____14303 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____14302
                                uu____14303
                            else
                              (let guard =
                                 let uu____14306 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14306 in
                               guard) in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              false bs1 guard in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt))) in
                          let uu____14320 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t in
                                let t_annot =
                                  match topt with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None ->
                                      failwith
                                        "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some" in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14343
                                     -> (e, t_annot, guard1)
                                 | uu____14358 ->
                                     let lc =
                                       let uu____14360 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed in
                                       FStar_All.pipe_right uu____14360
                                         FStar_TypeChecker_Common.lcomp_of_comp in
                                     let uu____14361 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1 in
                                     (match uu____14361 with
                                      | (e1, uu____14375, guard') ->
                                          let uu____14377 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t_annot, uu____14377)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____14320 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____14388 =
                                 let uu____14393 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14393 guard2 in
                               (match uu____14388 with
                                | (c1, g) -> (e1, c1, g)))))))
and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun head ->
      fun chead ->
        fun ghead ->
          fun args ->
            fun expected_topt ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = FStar_Syntax_Util.comp_result chead in
              (let uu____14443 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____14443
               then
                 let uu____14444 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos in
                 let uu____14445 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14444
                   uu____14445
               else ());
              (let monadic_application uu____14524 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14524 with
                 | (head1, chead1, ghead1, cres) ->
                     let uu____14593 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres) in
                     (match uu____14593 with
                      | (rt, g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt in
                          let uu____14607 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14623 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14623 in
                                (cres1, g)
                            | uu____14624 ->
                                let g =
                                  let uu____14634 =
                                    let uu____14635 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____14635
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14634 in
                                let uu____14636 =
                                  let uu____14637 =
                                    FStar_Syntax_Util.arrow bs cres1 in
                                  FStar_Syntax_Syntax.mk_Total uu____14637 in
                                (uu____14636, g) in
                          (match uu____14607 with
                           | (cres2, guard1) ->
                               ((let uu____14647 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium in
                                 if uu____14647
                                 then
                                   let uu____14648 =
                                     FStar_Syntax_Print.comp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14648
                                 else ());
                                (let uu____14650 =
                                   let uu____14655 =
                                     let uu____14656 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1 in
                                     FStar_All.pipe_right uu____14656
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   let uu____14657 =
                                     let uu____14658 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2 in
                                     FStar_All.pipe_right uu____14658
                                       FStar_TypeChecker_Common.lcomp_of_comp in
                                   (uu____14655, uu____14657) in
                                 match uu____14650 with
                                 | (chead2, cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14681 ->
                                                 match uu____14681 with
                                                 | (uu____14690, uu____14691,
                                                    lc) ->
                                                     (let uu____14699 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc in
                                                      Prims.op_Negation
                                                        uu____14699)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev) in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           head1.FStar_Syntax_Syntax.pos in
                                       let uu____14709 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful in
                                       if uu____14709
                                       then
                                         ((let uu____14711 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14711
                                           then
                                             let uu____14712 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14712
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14716 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____14716
                                           then
                                             let uu____14717 =
                                               FStar_Syntax_Print.term_to_string
                                                 term in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14717
                                           else ());
                                          cres3) in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c ->
                                            fun uu____14745 ->
                                              match uu____14745 with
                                              | ((e, q), x, c) ->
                                                  ((let uu____14787 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14787
                                                    then
                                                      let uu____14788 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                            -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1 in
                                                      let uu____14790 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14791 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14788
                                                        uu____14790
                                                        uu____14791
                                                    else ());
                                                   (let uu____14793 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14793
                                                    then
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        (FStar_Pervasives_Native.Some
                                                           e) c (x, out_c)
                                                    else
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        FStar_Pervasives_Native.None
                                                        c (x, out_c)))) cres4
                                         arg_comps_rev in
                                     let comp1 =
                                       (let uu____14801 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme in
                                        if uu____14801
                                        then
                                          let uu____14802 =
                                            FStar_Syntax_Print.term_to_string
                                              head1 in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14802
                                        else ());
                                       (let uu____14804 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2 in
                                        if uu____14804
                                        then
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some
                                               head1) chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)
                                        else
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            FStar_Pervasives_Native.None
                                            chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)) in
                                     let shortcuts_evaluation_order =
                                       let uu____14811 =
                                         let uu____14812 =
                                           FStar_Syntax_Subst.compress head1 in
                                         uu____14812.FStar_Syntax_Syntax.n in
                                       match uu____14811 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14816 -> false in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1 ->
                                                fun uu____14837 ->
                                                  match uu____14837 with
                                                  | (arg, uu____14851,
                                                     uu____14852) -> arg ::
                                                      args1) [] arg_comps_rev in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head1 args1 r in
                                         let app1 =
                                           FStar_TypeChecker_Util.maybe_lift
                                             env app
                                             cres4.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.res_typ in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app1
                                           comp1.FStar_TypeChecker_Common.eff_name
                                           comp1.FStar_TypeChecker_Common.res_typ
                                       else
                                         (let uu____14860 =
                                            let map_fun uu____14926 =
                                              match uu____14926 with
                                              | ((e, q), uu____14967, c) ->
                                                  ((let uu____14990 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14990
                                                    then
                                                      let uu____14991 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e in
                                                      let uu____14992 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14991
                                                        uu____14992
                                                    else ());
                                                   (let uu____14994 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c in
                                                    if uu____14994
                                                    then
                                                      ((let uu____15018 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____15018
                                                        then
                                                          FStar_Util.print_string
                                                            "... not lifting\n"
                                                        else ());
                                                       (FStar_Pervasives_Native.None,
                                                         (e, q)))
                                                    else
                                                      (let warn_effectful_args
                                                         =
                                                         (FStar_TypeChecker_Util.must_erase_for_extraction
                                                            env
                                                            chead2.FStar_TypeChecker_Common.res_typ)
                                                           &&
                                                           (let uu____15053 =
                                                              let uu____15054
                                                                =
                                                                let uu____15055
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1 in
                                                                uu____15055.FStar_Syntax_Syntax.n in
                                                              match uu____15054
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15059
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore" in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15059
                                                              | uu____15060
                                                                  -> true in
                                                            Prims.op_Negation
                                                              uu____15053) in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15062 =
                                                            let uu____15067 =
                                                              let uu____15068
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e in
                                                              let uu____15069
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name in
                                                              let uu____15070
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15068
                                                                uu____15069
                                                                uu____15070 in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15067) in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15062)
                                                       else ();
                                                       (let uu____15073 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme in
                                                        if uu____15073
                                                        then
                                                          FStar_Util.print_string
                                                            "... lifting!\n"
                                                        else ());
                                                       (let x =
                                                          FStar_Syntax_Syntax.new_bv
                                                            FStar_Pervasives_Native.None
                                                            c.FStar_TypeChecker_Common.res_typ in
                                                        let e1 =
                                                          FStar_TypeChecker_Util.maybe_lift
                                                            env e
                                                            c.FStar_TypeChecker_Common.eff_name
                                                            comp1.FStar_TypeChecker_Common.eff_name
                                                            c.FStar_TypeChecker_Common.res_typ in
                                                        let uu____15077 =
                                                          let uu____15086 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          (uu____15086, q) in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15077))))) in
                                            let uu____15115 =
                                              let uu____15146 =
                                                let uu____15175 =
                                                  let uu____15186 =
                                                    let uu____15195 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1 in
                                                    (uu____15195,
                                                      FStar_Pervasives_Native.None,
                                                      chead2) in
                                                  uu____15186 ::
                                                    arg_comps_rev in
                                                FStar_List.map map_fun
                                                  uu____15175 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15146 in
                                            match uu____15115 with
                                            | (lifted_args, reverse_args) ->
                                                let uu____15396 =
                                                  let uu____15397 =
                                                    FStar_List.hd
                                                      reverse_args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15397 in
                                                let uu____15418 =
                                                  let uu____15419 =
                                                    FStar_List.tl
                                                      reverse_args in
                                                  FStar_List.rev uu____15419 in
                                                (lifted_args, uu____15396,
                                                  uu____15418) in
                                          match uu____14860 with
                                          | (lifted_args, head2, args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head2 args1 r in
                                              let app1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env app
                                                  cres4.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ in
                                              let app2 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env app1
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ in
                                              let bind_lifted_args e
                                                uu___6_15528 =
                                                match uu___6_15528 with
                                                | FStar_Pervasives_Native.None
                                                    -> e
                                                | FStar_Pervasives_Native.Some
                                                    (x, m, t, e1) ->
                                                    let lb =
                                                      FStar_Syntax_Util.mk_letbinding
                                                        (FStar_Util.Inl x) []
                                                        t m e1 []
                                                        e1.FStar_Syntax_Syntax.pos in
                                                    let letbinding =
                                                      let uu____15589 =
                                                        let uu____15590 =
                                                          let uu____15603 =
                                                            let uu____15606 =
                                                              let uu____15607
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____15607] in
                                                            FStar_Syntax_Subst.close
                                                              uu____15606 e in
                                                          ((false, [lb]),
                                                            uu____15603) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15590 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15589
                                                        e.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      e.FStar_Syntax_Syntax.pos in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args) in
                                     let uu____15656 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1 in
                                     (match uu____15656 with
                                      | (comp2, g) ->
                                          ((let uu____15673 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme in
                                            if uu____15673
                                            then
                                              let uu____15674 =
                                                FStar_Syntax_Print.term_to_string
                                                  app in
                                              let uu____15675 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15674 uu____15675
                                            else ());
                                           (app, comp2, g))))))) in
               let rec tc_args head_info uu____15761 bs args1 =
                 match uu____15761 with
                 | (subst, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15924))::rest,
                         (uu____15926, FStar_Pervasives_Native.None)::uu____15927)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort in
                          let uu____15987 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t in
                          (match uu____15987 with
                           | (t1, g_ex) ->
                               let r1 =
                                 match outargs with
                                 | [] -> head.FStar_Syntax_Syntax.pos
                                 | ((t2, uu____16018), uu____16019,
                                    uu____16020)::uu____16021 ->
                                     let uu____16076 =
                                       FStar_Range.def_range
                                         head.FStar_Syntax_Syntax.pos in
                                     let uu____16077 =
                                       let uu____16078 =
                                         FStar_Range.use_range
                                           head.FStar_Syntax_Syntax.pos in
                                       let uu____16079 =
                                         FStar_Range.use_range
                                           t2.FStar_Syntax_Syntax.pos in
                                       FStar_Range.union_rng uu____16078
                                         uu____16079 in
                                     FStar_Range.range_of_rng uu____16076
                                       uu____16077 in
                               let uu____16080 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   r1 env t1 in
                               (match uu____16080 with
                                | (varg, uu____16100, implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst in
                                    let arg =
                                      let uu____16128 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____16128) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____16136 =
                                      let uu____16179 =
                                        let uu____16198 =
                                          let uu____16215 =
                                            let uu____16216 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____16216
                                              FStar_TypeChecker_Common.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16215) in
                                        uu____16198 :: outargs in
                                      (subst1, uu____16179, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____16136 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau_or_attr))::rest,
                         (uu____16286, FStar_Pervasives_Native.None)::uu____16287)
                          ->
                          let uu____16346 =
                            match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let tau1 = FStar_Syntax_Subst.subst subst tau in
                                let uu____16359 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau1 in
                                (match uu____16359 with
                                 | (tau2, uu____16371, g_tau) ->
                                     let uu____16373 =
                                       let uu____16374 =
                                         let uu____16381 =
                                           FStar_Dyn.mkdyn env in
                                         (uu____16381, tau2) in
                                       FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                         uu____16374 in
                                     (uu____16373, g_tau))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let attr1 =
                                  FStar_Syntax_Subst.subst subst attr in
                                let uu____16388 =
                                  tc_tot_or_gtot_term env attr1 in
                                (match uu____16388 with
                                 | (attr2, uu____16400, g_attr) ->
                                     ((FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         attr2), g_attr)) in
                          (match uu____16346 with
                           | (ctx_uvar_meta, g_tau_or_attr) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____16411 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t in
                               (match uu____16411 with
                                | (t1, g_ex) ->
                                    let r1 =
                                      match outargs with
                                      | [] -> head.FStar_Syntax_Syntax.pos
                                      | ((t2, uu____16442), uu____16443,
                                         uu____16444)::uu____16445 ->
                                          let uu____16500 =
                                            FStar_Range.def_range
                                              head.FStar_Syntax_Syntax.pos in
                                          let uu____16501 =
                                            let uu____16502 =
                                              FStar_Range.use_range
                                                head.FStar_Syntax_Syntax.pos in
                                            let uu____16503 =
                                              FStar_Range.use_range
                                                t2.FStar_Syntax_Syntax.pos in
                                            FStar_Range.union_rng uu____16502
                                              uu____16503 in
                                          FStar_Range.range_of_rng
                                            uu____16500 uu____16501 in
                                    let uu____16504 =
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        r1 env t1 FStar_Syntax_Syntax.Strict
                                        (FStar_Pervasives_Native.Some
                                           ctx_uvar_meta) in
                                    (match uu____16504 with
                                     | (varg, uu____16524, implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst in
                                         let arg =
                                           let uu____16552 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____16552) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau_or_attr]
                                             implicits in
                                         let uu____16560 =
                                           let uu____16603 =
                                             let uu____16622 =
                                               let uu____16639 =
                                                 let uu____16640 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____16640
                                                   FStar_TypeChecker_Common.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16639) in
                                             uu____16622 :: outargs in
                                           (subst1, uu____16603, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____16560 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16780, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16781)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16788),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16789)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16794),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16795)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____16808 ->
                                let uu____16817 =
                                  let uu____16822 =
                                    let uu____16823 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____16824 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____16825 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____16826 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; expected `%s` got `%s` for bvar %s and term %s"
                                      uu____16823 uu____16824 uu____16825
                                      uu____16826 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16822) in
                                FStar_Errors.raise_error uu____16817
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual in
                            let x1 =
                              let uu___2380_16830 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2380_16830.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2380_16830.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____16832 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____16832
                             then
                               let uu____16833 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____16834 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____16835 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____16836 =
                                 FStar_Syntax_Print.subst_to_string subst in
                               let uu____16837 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16833 uu____16834 uu____16835
                                 uu____16836 uu____16837
                             else ());
                            (let uu____16839 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ in
                             match uu____16839 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___2389_16854 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2389_16854.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2389_16854.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2389_16854.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2389_16854.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2389_16854.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2389_16854.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2389_16854.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2389_16854.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2389_16854.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2389_16854.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2389_16854.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2389_16854.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2389_16854.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2389_16854.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2389_16854.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2389_16854.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2389_16854.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2389_16854.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2389_16854.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2389_16854.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2389_16854.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2389_16854.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2389_16854.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2389_16854.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2389_16854.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2389_16854.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2389_16854.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2389_16854.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2389_16854.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2389_16854.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2389_16854.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2389_16854.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2389_16854.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2389_16854.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2389_16854.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2389_16854.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2389_16854.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2389_16854.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2389_16854.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2389_16854.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2389_16854.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2389_16854.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2389_16854.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2389_16854.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2389_16854.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___2389_16854.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   } in
                                 ((let uu____16856 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____16856
                                   then
                                     let uu____16857 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____16858 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____16859 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     let uu____16860 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____16857 uu____16858 uu____16859
                                       uu____16860
                                   else ());
                                  (let uu____16862 = tc_term env2 e in
                                   match uu____16862 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____16879 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16879 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____16902 =
                                           let uu____16905 =
                                             let uu____16914 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16914 in
                                           FStar_Pervasives_Native.fst
                                             uu____16905 in
                                         (uu____16902, aq) in
                                       let uu____16923 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name) in
                                       if uu____16923
                                       then
                                         let subst1 =
                                           let uu____16931 = FStar_List.hd bs in
                                           maybe_extend_subst subst
                                             uu____16931 e1 in
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____17077, []) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____17113) ->
                          let uu____17164 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs [] in
                          (match uu____17164 with
                           | (head1, chead1, ghead1) ->
                               let uu____17186 =
                                 let uu____17191 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1 in
                                 FStar_All.pipe_right uu____17191
                                   (fun uu____17208 ->
                                      match uu____17208 with
                                      | (c, g1) ->
                                          let uu____17219 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1 in
                                          (c, uu____17219)) in
                               (match uu____17186 with
                                | (chead2, ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17258 =
                                          FStar_Syntax_Subst.compress tres in
                                        FStar_All.pipe_right uu____17258
                                          FStar_Syntax_Util.unrefine in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1, cres') ->
                                          let uu____17289 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres' in
                                          (match uu____17289 with
                                           | (bs2, cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1) in
                                               ((let uu____17312 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low in
                                                 if uu____17312
                                                 then
                                                   FStar_Errors.log_issue
                                                     tres1.FStar_Syntax_Syntax.pos
                                                     (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                       "Potentially redundant explicit currying of a function type")
                                                 else ());
                                                tc_args head_info1
                                                  ([], [], [],
                                                    FStar_TypeChecker_Env.trivial_guard,
                                                    []) bs2 args1))
                                      | uu____17370 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17378 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env) in
                                              FStar_All.pipe_right
                                                uu____17378
                                                FStar_Syntax_Util.unascribe in
                                            let uu____17379 =
                                              let uu____17380 =
                                                FStar_Syntax_Subst.compress
                                                  tres3 in
                                              uu____17380.FStar_Syntax_Syntax.n in
                                            match uu____17379 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17383;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17384;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},
                                                 uu____17386)
                                                -> norm_tres tres4
                                            | uu____17393 -> tres3 in
                                          let uu____17394 = norm_tres tres1 in
                                          aux true solve ghead3 uu____17394
                                      | uu____17395 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3 in
                                          aux norm1 true ghead4 tres1
                                      | uu____17397 ->
                                          let uu____17398 =
                                            let uu____17403 =
                                              let uu____17404 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead in
                                              let uu____17405 =
                                                FStar_Util.string_of_int
                                                  n_args in
                                              let uu____17406 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17404 uu____17405
                                                uu____17406 in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17403) in
                                          let uu____17407 =
                                            FStar_Syntax_Syntax.argpos arg in
                                          FStar_Errors.raise_error
                                            uu____17398 uu____17407 in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2)))) in
               let rec check_function_app tf guard =
                 let uu____17435 =
                   let uu____17436 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____17436.FStar_Syntax_Syntax.n in
                 match uu____17435 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17445 ->
                     let uu____17458 =
                       FStar_List.fold_right
                         (fun uu____17489 ->
                            fun uu____17490 ->
                              match uu____17490 with
                              | (bs, guard1) ->
                                  let uu____17517 =
                                    let uu____17530 =
                                      let uu____17531 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17531
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17530 in
                                  (match uu____17517 with
                                   | (t, uu____17547, g) ->
                                       let uu____17561 =
                                         let uu____17564 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17564 :: bs in
                                       let uu____17565 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17561, uu____17565))) args
                         ([], guard) in
                     (match uu____17458 with
                      | (bs, guard1) ->
                          let uu____17582 =
                            let uu____17589 =
                              let uu____17602 =
                                let uu____17603 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17603
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17602 in
                            match uu____17589 with
                            | (t, uu____17619, g) ->
                                let uu____17633 = FStar_Options.ml_ish () in
                                if uu____17633
                                then
                                  let uu____17640 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17643 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17640, uu____17643)
                                else
                                  (let uu____17647 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17650 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17647, uu____17650)) in
                          (match uu____17582 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17669 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17669
                                 then
                                   let uu____17670 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17671 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17672 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17670 uu____17671 uu____17672
                                 else ());
                                (let g =
                                   let uu____17675 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17675 in
                                 let uu____17676 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17676))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17677;
                        FStar_Syntax_Syntax.pos = uu____17678;
                        FStar_Syntax_Syntax.vars = uu____17679;_},
                      uu____17680)
                     ->
                     let uu____17717 =
                       FStar_List.fold_right
                         (fun uu____17748 ->
                            fun uu____17749 ->
                              match uu____17749 with
                              | (bs, guard1) ->
                                  let uu____17776 =
                                    let uu____17789 =
                                      let uu____17790 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____17790
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17789 in
                                  (match uu____17776 with
                                   | (t, uu____17806, g) ->
                                       let uu____17820 =
                                         let uu____17823 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____17823 :: bs in
                                       let uu____17824 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____17820, uu____17824))) args
                         ([], guard) in
                     (match uu____17717 with
                      | (bs, guard1) ->
                          let uu____17841 =
                            let uu____17848 =
                              let uu____17861 =
                                let uu____17862 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____17862
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17861 in
                            match uu____17848 with
                            | (t, uu____17878, g) ->
                                let uu____17892 = FStar_Options.ml_ish () in
                                if uu____17892
                                then
                                  let uu____17899 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____17902 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____17899, uu____17902)
                                else
                                  (let uu____17906 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____17909 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____17906, uu____17909)) in
                          (match uu____17841 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____17928 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____17928
                                 then
                                   let uu____17929 =
                                     FStar_Syntax_Print.term_to_string head in
                                   let uu____17930 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____17931 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17929 uu____17930 uu____17931
                                 else ());
                                (let g =
                                   let uu____17934 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17934 in
                                 let uu____17935 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____17935))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____17958 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____17958 with
                      | (bs1, c1) ->
                          let head_info = (head, chead, ghead, c1) in
                          ((let uu____17981 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____17981
                            then
                              let uu____17982 =
                                FStar_Syntax_Print.term_to_string head in
                              let uu____17983 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____17984 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____17985 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17982 uu____17983 uu____17984
                                uu____17985
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____18044) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____18050, uu____18051) ->
                     check_function_app t guard
                 | uu____18092 ->
                     let uu____18093 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____18093
                       head.FStar_Syntax_Syntax.pos in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)
and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun head ->
      fun chead ->
        fun g_head ->
          fun args ->
            fun expected_topt ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress
                  (FStar_Syntax_Util.comp_result chead) in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____18175 =
                    FStar_List.fold_left2
                      (fun uu____18242 ->
                         fun uu____18243 ->
                           fun uu____18244 ->
                             match (uu____18242, uu____18243, uu____18244)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____18391 =
                                     let uu____18392 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____18392 <> FStar_Syntax_Util.Equal in
                                   if uu____18391
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18394 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost" in
                                   match uu____18394 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen in
                                       let g1 =
                                         let uu____18422 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18422 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18426 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____18426)
                                              &&
                                              (let uu____18428 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name in
                                               Prims.op_Negation uu____18428)) in
                                       let uu____18429 =
                                         let uu____18440 =
                                           let uu____18451 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____18451] in
                                         FStar_List.append seen uu____18440 in
                                       let uu____18484 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____18429, uu____18484, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____18175 with
                   | (args1, guard, ghost) ->
                       let e = FStar_Syntax_Syntax.mk_Tm_app head args1 r in
                       let c1 =
                         if ghost
                         then
                           let uu____18544 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____18544
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c in
                       let uu____18546 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____18546 with | (c2, g) -> (e, c2, g)))
              | uu____18562 ->
                  check_application_args env head chead g_head args
                    expected_topt
and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_Syntax_Syntax.term Prims.list * FStar_TypeChecker_Env.env *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun env ->
    fun pat_t ->
      fun p0 ->
        let fail msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t in
            let uu____18654 = FStar_Syntax_Util.head_and_args t1 in
            match uu____18654 with
            | (head, args) ->
                let uu____18697 =
                  let uu____18698 = FStar_Syntax_Subst.compress head in
                  uu____18698.FStar_Syntax_Syntax.n in
                (match uu____18697 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18702;
                        FStar_Syntax_Syntax.vars = uu____18703;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18710 ->
                     if norm1
                     then t1
                     else
                       (let uu____18712 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____18712))
          and unfold_once t f us args =
            let uu____18729 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____18729
            then t
            else
              (let uu____18731 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____18731 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18751 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____18751 with
                    | (uu____18756, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____18760 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____18760 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18778 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____18778
           then
             let uu____18779 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____18780 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18779 uu____18780
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____18794 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____18795 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18794 uu____18795 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____18796 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____18796 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____18840 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____18840 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18841;
                    FStar_Syntax_Syntax.pos = uu____18842;
                    FStar_Syntax_Syntax.vars = uu____18843;_} ->
                    let uu____18846 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____18846 with
                     | (head_p, args_p) ->
                         let uu____18889 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____18889
                         then
                           let uu____18890 =
                             let uu____18891 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____18891.FStar_Syntax_Syntax.n in
                           (match uu____18890 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18896 =
                                    let uu____18897 =
                                      let uu____18898 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18898 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18897 in
                                  if uu____18896
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____18918 =
                                    let uu____18943 =
                                      let uu____18946 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18946 in
                                    match uu____18943 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____18992 =
                                          FStar_Util.first_N n args_p in
                                        (match uu____18992 with
                                         | (params_p, uu____19050) ->
                                             let uu____19091 =
                                               FStar_Util.first_N n args_s in
                                             (match uu____19091 with
                                              | (params_s, uu____19149) ->
                                                  (params_p, params_s))) in
                                  match uu____18918 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____19278 ->
                                             fun uu____19279 ->
                                               match (uu____19278,
                                                       uu____19279)
                                               with
                                               | ((p, uu____19313),
                                                  (s, uu____19315)) ->
                                                   let uu____19348 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____19348 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____19351 =
                                                          let uu____19352 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____19353 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19352
                                                            uu____19353 in
                                                        fail1 uu____19351
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____19356 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19358 =
                              let uu____19359 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____19360 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19359 uu____19360 in
                            fail1 uu____19358))
                | uu____19361 ->
                    let uu____19362 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____19362 with
                     | FStar_Pervasives_Native.None -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____19402 = FStar_Syntax_Util.head_and_args e in
          match uu____19402 with
          | (head, args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19470 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____19470 with
                    | (us, t_f) ->
                        let uu____19489 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____19489 with
                         | (formals, t) ->
                             let erasable =
                               FStar_TypeChecker_Env.non_informative env1 t in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____19594 formals1 args1 =
                                 match uu____19594 with
                                 | (subst, args_out, bvs, guard) ->
                                     (match (formals1, args1) with
                                      | ([], []) ->
                                          let head1 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head us in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head1 args_out
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____19737 =
                                            FStar_Syntax_Subst.subst subst t in
                                          (pat_e, uu____19737, bvs, guard,
                                            erasable)
                                      | ((f1, uu____19741)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____19799 =
                                            let uu____19820 =
                                              let uu____19821 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____19821.FStar_Syntax_Syntax.n in
                                            match uu____19820 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2696_19846 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2696_19846.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2696_19846.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  } in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1 in
                                                let subst1 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst in
                                                ((a1, imp_a), subst1,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____19869 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____19883 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____19883 with
                                                 | (a1, uu____19911, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____19935 ->
                                                fail "Not a simple pattern" in
                                          (match uu____19799 with
                                           | (a1, subst1, bvs1, g) ->
                                               let uu____19996 =
                                                 let uu____20019 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20019) in
                                               aux uu____19996 formals2 args2)
                                      | uu____20058 ->
                                          fail "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20113 -> fail "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____20175 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____20175
           then
             let uu____20176 = FStar_Syntax_Print.pat_to_string p in
             let uu____20177 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20176
               uu____20177
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20198 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t in
               FStar_All.pipe_right uu____20198 FStar_Syntax_Syntax.mk_binder in
             let tm =
               let uu____20206 =
                 let uu____20207 =
                   let uu____20216 =
                     let uu____20217 =
                       FStar_All.pipe_right x_b FStar_Pervasives_Native.fst in
                     FStar_All.pipe_right uu____20217
                       FStar_Syntax_Syntax.bv_to_name in
                   FStar_All.pipe_right uu____20216
                     FStar_Syntax_Syntax.as_arg in
                 [uu____20207] in
               FStar_Syntax_Syntax.mk_Tm_app disc uu____20206
                 FStar_Range.dummyRange in
             let tm1 =
               let uu____20251 =
                 let uu____20252 =
                   FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg in
                 [uu____20252] in
               FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20251
                 FStar_Range.dummyRange in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20313 ->
               let uu____20320 =
                 let uu____20321 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20321 in
               failwith uu____20320
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2735_20340 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2735_20340.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2735_20340.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20341 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20341,
                 (let uu___2738_20347 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2738_20347.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2742_20350 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2742_20350.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2742_20350.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____20351 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], [id], uu____20351,
                 (let uu___2745_20357 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2745_20357.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant c ->
               ((match c with
                 | FStar_Const.Const_unit -> ()
                 | FStar_Const.Const_bool uu____20360 -> ()
                 | FStar_Const.Const_int uu____20361 -> ()
                 | FStar_Const.Const_char uu____20372 -> ()
                 | FStar_Const.Const_float uu____20373 -> ()
                 | FStar_Const.Const_string uu____20374 -> ()
                 | uu____20379 ->
                     let uu____20380 =
                       let uu____20381 = FStar_Syntax_Print.const_to_string c in
                       FStar_Util.format1
                         "Pattern matching a constant that does not have decidable equality: %s"
                         uu____20381 in
                     fail uu____20380);
                (let uu____20382 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
                 match uu____20382 with
                 | (uu____20409, e_c, uu____20411, uu____20412) ->
                     let uu____20417 = tc_tot_or_gtot_term env1 e_c in
                     (match uu____20417 with
                      | (e_c1, lc, g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                           (let expected_t =
                              expected_pat_typ env1 p0.FStar_Syntax_Syntax.p
                                t in
                            (let uu____20446 =
                               let uu____20447 =
                                 FStar_TypeChecker_Rel.teq_nosmt_force env1
                                   lc.FStar_TypeChecker_Common.res_typ
                                   expected_t in
                               Prims.op_Negation uu____20447 in
                             if uu____20446
                             then
                               let uu____20448 =
                                 let uu____20449 =
                                   FStar_Syntax_Print.term_to_string
                                     lc.FStar_TypeChecker_Common.res_typ in
                                 let uu____20450 =
                                   FStar_Syntax_Print.term_to_string
                                     expected_t in
                                 FStar_Util.format2
                                   "Type of pattern (%s) does not match type of scrutinee (%s)"
                                   uu____20449 uu____20450 in
                               fail uu____20448
                             else ());
                            ([], [], e_c1, p,
                              FStar_TypeChecker_Env.trivial_guard, false))))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20502 ->
                        match uu____20502 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20527
                                 -> (p1, b)
                             | uu____20536 ->
                                 let uu____20537 =
                                   let uu____20540 =
                                     let uu____20541 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____20541 in
                                   FStar_Syntax_Syntax.withinfo uu____20540
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____20537, b))) sub_pats in
                 let uu___2786_20544 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2786_20544.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20584 ->
                         match uu____20584 with
                         | (x, uu____20592) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20597
                                  -> false
                              | uu____20604 -> true))) in
               let uu____20605 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____20605 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20645 =
                          let uu____20646 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____20647 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____20648 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____20653 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20646 uu____20647 uu____20648 uu____20653 in
                        failwith uu____20645)
                     else ();
                     (let uu____20655 =
                        let uu____20666 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____20666 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard,
                           erasable) ->
                            let g' =
                              let uu____20699 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____20699 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____20702 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____20702
                              then
                                let uu____20703 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____20704 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____20705 =
                                  let uu____20706 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____20712 =
                                           let uu____20713 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____20714 =
                                             let uu____20715 =
                                               let uu____20716 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.op_Hat uu____20716 ")" in
                                             Prims.op_Hat " : " uu____20715 in
                                           Prims.op_Hat uu____20713
                                             uu____20714 in
                                         Prims.op_Hat "(" uu____20712)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____20706
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____20703 uu____20704 uu____20705
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable)) in
                      match uu____20655 with
                      | (simple_pat_e1, simple_bvs1, g1, erasable) ->
                          let uu____20746 =
                            let uu____20775 =
                              let uu____20804 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], [], uu____20804, erasable,
                                Prims.int_zero) in
                            FStar_List.fold_left2
                              (fun uu____20877 ->
                                 fun uu____20878 ->
                                   fun x ->
                                     match (uu____20877, uu____20878) with
                                     | ((env2, bvs, tms, pats, subst, g,
                                         erasable1, i),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____21039 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____21039 with
                                          | (bvs_p, tms_p, e_p, p2, g',
                                             erasable_p) ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21103 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21103 i in
                                                let uu____21104 =
                                                  let uu____21113 =
                                                    let uu____21118 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None in
                                                    mk_disc_t uu____21118 in
                                                  FStar_List.map uu____21113 in
                                                FStar_All.pipe_right tms_p
                                                  uu____21104 in
                                              let uu____21123 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____21123,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____20775 sub_pats1 simple_bvs1 in
                          (match uu____20746 with
                           | (_env, bvs, tms, checked_sub_pats, subst, g,
                              erasable1, uu____21173) ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst simple_pat_e1 in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd, b)::simple_pats1 ->
                                       (match hd.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x, e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst
                                                e in
                                            let hd1 =
                                              let uu___2870_21330 = hd in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2870_21330.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____21335 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd1, b) :: uu____21335
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd1, uu____21374)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21406 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd1, b) :: uu____21406
                                             | uu____21423 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21446 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___2891_21484 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2891_21484.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21495 -> failwith "Impossible" in
                               let uu____21498 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, tms, pat_e, uu____21498, g, erasable1)))))) in
        (let uu____21504 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____21504
         then
           let uu____21505 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21505
         else ());
        (let uu____21507 =
           let uu____21524 =
             let uu___2896_21525 =
               let uu____21526 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____21526 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2896_21525.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2896_21525.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2896_21525.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2896_21525.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2896_21525.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2896_21525.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2896_21525.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2896_21525.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2896_21525.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2896_21525.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2896_21525.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2896_21525.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2896_21525.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2896_21525.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2896_21525.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2896_21525.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2896_21525.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2896_21525.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2896_21525.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2896_21525.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2896_21525.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2896_21525.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2896_21525.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2896_21525.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2896_21525.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2896_21525.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2896_21525.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2896_21525.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2896_21525.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2896_21525.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2896_21525.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2896_21525.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2896_21525.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2896_21525.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2896_21525.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2896_21525.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2896_21525.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2896_21525.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2896_21525.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2896_21525.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2896_21525.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2896_21525.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2896_21525.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2896_21525.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2896_21525.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___2896_21525.FStar_TypeChecker_Env.enable_defer_to_tac)
             } in
           let uu____21541 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____21524 uu____21541 pat_t in
         match uu____21507 with
         | (bvs, tms, pat_e, pat, g, erasable) ->
             ((let uu____21577 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____21577
               then
                 let uu____21578 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____21579 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____21578
                   uu____21579
               else ());
              (let uu____21581 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____21582 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, tms, uu____21581, pat_e, uu____21582, g, erasable))))
and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.branch ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          FStar_Syntax_Syntax.term * FStar_Ident.lident *
          FStar_Syntax_Syntax.cflag Prims.list *
          (Prims.bool -> FStar_TypeChecker_Common.lcomp) *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun scrutinee ->
    fun env ->
      fun branch ->
        let uu____21617 = FStar_Syntax_Subst.open_branch branch in
        match uu____21617 with
        | (pattern, when_clause, branch_exp) ->
            let uu____21664 = branch in
            (match uu____21664 with
             | (cpat, uu____21693, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____21715 =
                   let uu____21722 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____21722
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____21715 with
                  | (scrutinee_env, uu____21757) ->
                      let uu____21762 = tc_pat env pat_t pattern in
                      (match uu____21762 with
                       | (pattern1, pat_bvs, pat_bv_tms, pat_env, pat_exp,
                          norm_pat_exp, guard_pat, erasable) ->
                           ((let uu____21827 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____21827
                             then
                               let uu____21828 =
                                 FStar_Syntax_Print.pat_to_string pattern1 in
                               let uu____21829 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs in
                               let uu____21830 =
                                 FStar_List.fold_left
                                   (fun s ->
                                      fun t ->
                                        let uu____21836 =
                                          let uu____21837 =
                                            FStar_Syntax_Print.term_to_string
                                              t in
                                          Prims.op_Hat ";" uu____21837 in
                                        Prims.op_Hat s uu____21836) ""
                                   pat_bv_tms in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____21828 uu____21829 uu____21830
                             else ());
                            (let uu____21839 =
                               match when_clause with
                               | FStar_Pervasives_Native.None ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____21869 =
                                     FStar_TypeChecker_Env.should_verify env in
                                   if uu____21869
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____21887 =
                                        let uu____21894 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool in
                                        tc_term uu____21894 e in
                                      match uu____21887 with
                                      | (e1, c, g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g)) in
                             match uu____21839 with
                             | (when_clause1, g_when) ->
                                 let uu____21949 = tc_term pat_env branch_exp in
                                 (match uu____21949 with
                                  | (branch_exp1, c, g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____22005 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool in
                                              FStar_All.pipe_left
                                                (fun uu____22016 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____22016) uu____22005 in
                                        let branch_guard =
                                          let uu____22020 =
                                            let uu____22021 =
                                              FStar_TypeChecker_Env.should_verify
                                                env in
                                            Prims.op_Negation uu____22021 in
                                          if uu____22020
                                          then
                                            FStar_Syntax_Util.exp_true_bool
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22074 =
                                                   let uu____22081 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22081 in
                                                 match uu____22074 with
                                                 | (is_induc, datacons) ->
                                                     if
                                                       (Prims.op_Negation
                                                          is_induc)
                                                         ||
                                                         ((FStar_List.length
                                                             datacons)
                                                            > Prims.int_one)
                                                     then
                                                       let discriminator =
                                                         FStar_Syntax_Util.mk_discriminator
                                                           f.FStar_Syntax_Syntax.v in
                                                       let uu____22093 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator in
                                                       (match uu____22093
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                            -> []
                                                        | uu____22114 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None in
                                                            let uu____22126 =
                                                              let uu____22127
                                                                =
                                                                let uu____22128
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                [uu____22128] in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____22127
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                            [uu____22126])
                                                     else [] in
                                               let fail uu____22159 =
                                                 let uu____22160 =
                                                   let uu____22161 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos in
                                                   let uu____22162 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1 in
                                                   let uu____22163 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1 in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22161 uu____22162
                                                     uu____22163 in
                                                 failwith uu____22160 in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1, uu____22176) ->
                                                     head_constructor t1
                                                 | uu____22181 -> fail () in
                                               let force_scrutinee
                                                 uu____22187 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let uu____22188 =
                                                       let uu____22189 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p in
                                                       let uu____22190 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2 in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22189
                                                         uu____22190 in
                                                     failwith uu____22188
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t in
                                               let pat_exp2 =
                                                 let uu____22195 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1 in
                                                 FStar_All.pipe_right
                                                   uu____22195
                                                   FStar_Syntax_Util.unmeta in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22200,
                                                  FStar_Syntax_Syntax.Tm_name
                                                  uu____22201) -> []
                                               | (uu____22202,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,
                                                  FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22205 =
                                                     let uu____22206 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1 in
                                                     let uu____22207 =
                                                       force_scrutinee () in
                                                     FStar_Syntax_Util.mk_decidable_eq
                                                       uu____22206
                                                       uu____22207 pat_exp2 in
                                                   [uu____22205]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22210,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22211)),
                                                  uu____22212) ->
                                                   let uu____22227 =
                                                     let uu____22234 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env in
                                                     match uu____22234 with
                                                     | (env1, uu____22248) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2 in
                                                   (match uu____22227 with
                                                    | (uu____22255, t,
                                                       uu____22257) ->
                                                        let uu____22258 =
                                                          let uu____22259 =
                                                            force_scrutinee
                                                              () in
                                                          FStar_Syntax_Util.mk_decidable_eq
                                                            t uu____22259
                                                            pat_exp2 in
                                                        [uu____22258])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22262, []),
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22263) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22285 =
                                                     let uu____22286 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22286 in
                                                   if uu____22285
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22292 =
                                                        force_scrutinee () in
                                                      let uu____22295 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22292
                                                        uu____22295)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22298, []),
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22299) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2 in
                                                   let uu____22315 =
                                                     let uu____22316 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v in
                                                     Prims.op_Negation
                                                       uu____22316 in
                                                   if uu____22315
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22322 =
                                                        force_scrutinee () in
                                                      let uu____22325 =
                                                        head_constructor
                                                          pat_exp2 in
                                                      discriminate
                                                        uu____22322
                                                        uu____22325)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22328, pat_args),
                                                  FStar_Syntax_Syntax.Tm_app
                                                  (head, args)) ->
                                                   let f =
                                                     head_constructor head in
                                                   let uu____22373 =
                                                     (let uu____22376 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v in
                                                      Prims.op_Negation
                                                        uu____22376)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args)) in
                                                   if uu____22373
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22399 =
                                                          let uu____22404 =
                                                            FStar_List.zip
                                                              pat_args args in
                                                          FStar_All.pipe_right
                                                            uu____22404
                                                            (FStar_List.mapi
                                                               (fun i ->
                                                                  fun
                                                                    uu____22486
                                                                    ->
                                                                    match uu____22486
                                                                    with
                                                                    | 
                                                                    ((pi,
                                                                    uu____22506),
                                                                    (ei,
                                                                    uu____22508))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22533
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    match uu____22533
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22554
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22566
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22566
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____22567
                                                                    =
                                                                    let uu____22568
                                                                    =
                                                                    let uu____22569
                                                                    =
                                                                    let uu____22578
                                                                    =
                                                                    force_scrutinee
                                                                    () in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22578 in
                                                                    [uu____22569] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22568
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22567 in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei)) in
                                                        FStar_All.pipe_right
                                                          uu____22399
                                                          FStar_List.flatten in
                                                      let uu____22601 =
                                                        let uu____22604 =
                                                          force_scrutinee () in
                                                        discriminate
                                                          uu____22604 f in
                                                      FStar_List.append
                                                        uu____22601
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____22607, uu____22608)
                                                   -> []
                                               | uu____22615 ->
                                                   let uu____22620 =
                                                     let uu____22621 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2 in
                                                     let uu____22622 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2 in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____22621
                                                       uu____22622 in
                                                   failwith uu____22620 in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____22649 =
                                                 let uu____22650 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____22650 in
                                               if uu____22649
                                               then
                                                 FStar_Syntax_Util.exp_true_bool
                                               else
                                                 (let t =
                                                    let uu____22653 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_and_l
                                                      uu____22653 in
                                                  let uu____22662 =
                                                    tc_check_tot_or_gtot_term
                                                      scrutinee_env t
                                                      FStar_Syntax_Util.t_bool
                                                      "" in
                                                  match uu____22662 with
                                                  | (t1, uu____22670,
                                                     uu____22671) -> t1) in
                                             let branch_guard =
                                               build_and_check_branch_guard
                                                 (FStar_Pervasives_Native.Some
                                                    scrutinee_tm) pattern1
                                                 norm_pat_exp in
                                             let branch_guard1 =
                                               match when_condition with
                                               | FStar_Pervasives_Native.None
                                                   -> branch_guard
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   FStar_Syntax_Util.mk_and
                                                     branch_guard w in
                                             branch_guard1) in
                                        (let uu____22686 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             FStar_Options.Extreme in
                                         if uu____22686
                                         then
                                           let uu____22687 =
                                             FStar_Syntax_Print.term_to_string
                                               branch_guard in
                                           FStar_Util.print1
                                             "tc_eqn: branch guard : %s\n"
                                             uu____22687
                                         else ());
                                        (let uu____22689 =
                                           let eqs =
                                             let uu____22708 =
                                               let uu____22709 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env in
                                               Prims.op_Negation uu____22709 in
                                             if uu____22708
                                             then
                                               FStar_Pervasives_Native.None
                                             else
                                               (let e =
                                                  FStar_Syntax_Subst.compress
                                                    pat_exp in
                                                let uu____22714 =
                                                  let uu____22715 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____22715 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____22714) in
                                           let uu____22716 =
                                             FStar_TypeChecker_Util.strengthen_precondition
                                               FStar_Pervasives_Native.None
                                               env branch_exp1 c g_branch in
                                           match uu____22716 with
                                           | (c1, g_branch1) ->
                                               let branch_has_layered_effect
                                                 =
                                                 let uu____22742 =
                                                   FStar_All.pipe_right
                                                     c1.FStar_TypeChecker_Common.eff_name
                                                     (FStar_TypeChecker_Env.norm_eff_name
                                                        env) in
                                                 FStar_All.pipe_right
                                                   uu____22742
                                                   (FStar_TypeChecker_Env.is_layered_effect
                                                      env) in
                                               let uu____22743 =
                                                 let env1 =
                                                   let uu____22749 =
                                                     FStar_All.pipe_right
                                                       pat_bvs
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder) in
                                                   FStar_TypeChecker_Env.push_binders
                                                     scrutinee_env
                                                     uu____22749 in
                                                 if branch_has_layered_effect
                                                 then
                                                   let c2 =
                                                     let uu____22757 =
                                                       let uu____22758 =
                                                         FStar_Syntax_Util.b2t
                                                           branch_guard in
                                                       FStar_TypeChecker_Common.NonTrivial
                                                         uu____22758 in
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env1 c1 uu____22757 in
                                                   (c2,
                                                     FStar_TypeChecker_Env.trivial_guard)
                                                 else
                                                   (match (eqs,
                                                            when_condition)
                                                    with
                                                    | uu____22770 when
                                                        let uu____22781 =
                                                          FStar_TypeChecker_Env.should_verify
                                                            env1 in
                                                        Prims.op_Negation
                                                          uu____22781
                                                        -> (c1, g_when)
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.None)
                                                        -> (c1, g_when)
                                                    | (FStar_Pervasives_Native.Some
                                                       f,
                                                       FStar_Pervasives_Native.None)
                                                        ->
                                                        let gf =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            f in
                                                        let g =
                                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                                            gf in
                                                        let uu____22801 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 gf in
                                                        let uu____22802 =
                                                          FStar_TypeChecker_Env.imp_guard
                                                            g g_when in
                                                        (uu____22801,
                                                          uu____22802)
                                                    | (FStar_Pervasives_Native.Some
                                                       f,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_f =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            f in
                                                        let g_fw =
                                                          let uu____22817 =
                                                            FStar_Syntax_Util.mk_conj
                                                              f w in
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            uu____22817 in
                                                        let uu____22818 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_fw in
                                                        let uu____22819 =
                                                          let uu____22820 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              g_f in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____22820
                                                            g_when in
                                                        (uu____22818,
                                                          uu____22819)
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.Some
                                                       w) ->
                                                        let g_w =
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            w in
                                                        let g =
                                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                                            g_w in
                                                        let uu____22834 =
                                                          FStar_TypeChecker_Util.weaken_precondition
                                                            env1 c1 g_w in
                                                        (uu____22834, g_when)) in
                                               (match uu____22743 with
                                                | (c_weak, g_when_weak) ->
                                                    let binders =
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.mk_binder
                                                        pat_bvs in
                                                    let maybe_return_c_weak
                                                      should_return =
                                                      let c_weak1 =
                                                        let uu____22874 =
                                                          should_return &&
                                                            (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                               c_weak) in
                                                        if uu____22874
                                                        then
                                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                            env branch_exp1
                                                            c_weak
                                                        else c_weak in
                                                      if
                                                        branch_has_layered_effect
                                                      then
                                                        ((let uu____22877 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects") in
                                                          if uu____22877
                                                          then
                                                            FStar_Util.print_string
                                                              "Typechecking pat_bv_tms ...\n"
                                                          else ());
                                                         (let pat_bv_tms1 =
                                                            FStar_All.pipe_right
                                                              pat_bv_tms
                                                              (FStar_List.map
                                                                 (fun
                                                                    pat_bv_tm
                                                                    ->
                                                                    let uu____22889
                                                                    =
                                                                    let uu____22890
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____22890] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____22889
                                                                    FStar_Range.dummyRange)) in
                                                          let pat_bv_tms2 =
                                                            let env1 =
                                                              let uu___3127_22927
                                                                =
                                                                FStar_TypeChecker_Env.push_bv
                                                                  env
                                                                  scrutinee in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___3127_22927.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              } in
                                                            let uu____22928 =
                                                              let uu____22931
                                                                =
                                                                FStar_List.fold_left2
                                                                  (fun
                                                                    uu____22959
                                                                    ->
                                                                    fun
                                                                    pat_bv_tm
                                                                    ->
                                                                    fun bv ->
                                                                    match uu____22959
                                                                    with
                                                                    | 
                                                                    (substs,
                                                                    acc) ->
                                                                    let expected_t
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    substs
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____23000
                                                                    =
                                                                    let uu____23007
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs) in
                                                                    let uu____23008
                                                                    =
                                                                    let uu____23019
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t in
                                                                    tc_trivial_guard
                                                                    uu____23019 in
                                                                    FStar_All.pipe_right
                                                                    uu____23007
                                                                    uu____23008 in
                                                                    FStar_All.pipe_right
                                                                    uu____23000
                                                                    FStar_Pervasives_Native.fst in
                                                                    ((FStar_List.append
                                                                    substs
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv,
                                                                    pat_bv_tm1)]),
                                                                    (FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])))
                                                                  ([], [])
                                                                  pat_bv_tms1
                                                                  pat_bvs in
                                                              FStar_All.pipe_right
                                                                uu____22931
                                                                FStar_Pervasives_Native.snd in
                                                            FStar_All.pipe_right
                                                              uu____22928
                                                              (FStar_List.map
                                                                 (FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1)) in
                                                          (let uu____23081 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffects") in
                                                           if uu____23081
                                                           then
                                                             let uu____23082
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____23088
                                                                    =
                                                                    let uu____23089
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23089 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23088)
                                                                 ""
                                                                 pat_bv_tms2 in
                                                             let uu____23090
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun s ->
                                                                    fun t ->
                                                                    let uu____23096
                                                                    =
                                                                    let uu____23097
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23097 in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23096)
                                                                 "" pat_bvs in
                                                             FStar_Util.print2
                                                               "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                               uu____23082
                                                               uu____23090
                                                           else ());
                                                          (let uu____23099 =
                                                             FStar_All.pipe_right
                                                               c_weak1
                                                               (FStar_TypeChecker_Common.apply_lcomp
                                                                  (fun c2 ->
                                                                    c2)
                                                                  (fun g ->
                                                                    match eqs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> g
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eqs1 ->
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g eqs1)) in
                                                           let uu____23106 =
                                                             let uu____23111
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee in
                                                             FStar_TypeChecker_Util.close_layered_lcomp
                                                               uu____23111
                                                               pat_bvs
                                                               pat_bv_tms2 in
                                                           FStar_All.pipe_right
                                                             uu____23099
                                                             uu____23106)))
                                                      else
                                                        FStar_TypeChecker_Util.close_wp_lcomp
                                                          env pat_bvs c_weak1 in
                                                    let uu____23113 =
                                                      FStar_TypeChecker_Env.close_guard
                                                        env binders
                                                        g_when_weak in
                                                    let uu____23114 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        guard_pat g_branch1 in
                                                    ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                      (c_weak.FStar_TypeChecker_Common.cflags),
                                                      maybe_return_c_weak,
                                                      uu____23113,
                                                      uu____23114)) in
                                         match uu____22689 with
                                         | (effect_label, cflags,
                                            maybe_return_c, g_when1,
                                            g_branch1) ->
                                             let guard =
                                               FStar_TypeChecker_Env.conj_guard
                                                 g_when1 g_branch1 in
                                             ((let uu____23164 =
                                                 FStar_TypeChecker_Env.debug
                                                   env FStar_Options.High in
                                               if uu____23164
                                               then
                                                 let uu____23165 =
                                                   FStar_TypeChecker_Rel.guard_to_string
                                                     env guard in
                                                 FStar_All.pipe_left
                                                   (FStar_Util.print1
                                                      "Carrying guard from match: %s\n")
                                                   uu____23165
                                               else ());
                                              (let uu____23167 =
                                                 FStar_Syntax_Subst.close_branch
                                                   (pattern1, when_clause1,
                                                     branch_exp1) in
                                               let uu____23184 =
                                                 let uu____23185 =
                                                   FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder
                                                     pat_bvs in
                                                 FStar_TypeChecker_Util.close_guard_implicits
                                                   env false uu____23185
                                                   guard in
                                               (uu____23167, branch_guard,
                                                 effect_label, cflags,
                                                 maybe_return_c, uu____23184,
                                                 erasable))))))))))))
and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let uu____23228 = check_let_bound_def true env1 lb in
          (match uu____23228 with
           | (e1, univ_vars, c1, g1, annotated) ->
               let uu____23250 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23271 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____23271, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23276 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____23276
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____23277 = FStar_TypeChecker_Common.lcomp_comp c1 in
                    match uu____23277 with
                    | (comp1, g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1 in
                        let uu____23295 =
                          let uu____23308 =
                            FStar_TypeChecker_Generalize.generalize env1
                              false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)] in
                          FStar_List.hd uu____23308 in
                        (match uu____23295 with
                         | (uu____23357, univs, e11, c11, gvs) ->
                             let g13 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.map_guard g12)
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta;
                                    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                    FStar_TypeChecker_Env.CompressUvars;
                                    FStar_TypeChecker_Env.NoFullNorm;
                                    FStar_TypeChecker_Env.Exclude
                                      FStar_TypeChecker_Env.Zeta] env1) in
                             let g14 =
                               FStar_TypeChecker_Env.abstract_guard_n gvs g13 in
                             let uu____23371 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11 in
                             (g14, e11, univs, uu____23371))) in
               (match uu____23250 with
                | (g11, e11, univ_vars1, c11) ->
                    let uu____23388 =
                      let uu____23397 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____23397
                      then
                        let uu____23406 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____23406 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____23435 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____23435
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____23436 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____23436, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____23447 =
                            FStar_TypeChecker_Common.lcomp_comp c11 in
                          match uu____23447 with
                          | (comp1, g_comp1) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g_comp1;
                               (let c =
                                  FStar_All.pipe_right comp1
                                    (FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Env.Beta;
                                       FStar_TypeChecker_Env.NoFullNorm;
                                       FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                       env1) in
                                let e21 =
                                  let uu____23471 =
                                    FStar_Syntax_Util.is_pure_comp c in
                                  if uu____23471
                                  then e2
                                  else
                                    ((let uu____23476 =
                                        FStar_TypeChecker_Env.get_range env1 in
                                      FStar_Errors.log_issue uu____23476
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       e2.FStar_Syntax_Syntax.pos) in
                                (e21, c))))) in
                    (match uu____23388 with
                     | (e21, c12) ->
                         ((let uu____23500 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____23500
                           then
                             let uu____23501 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____23501
                           else ());
                          (let e12 =
                             let uu____23504 = FStar_Options.tcnorm () in
                             if uu____23504
                             then
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.UnfoldAttr
                                    [FStar_Parser_Const.tcnorm_attr];
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1 e11
                             else e11 in
                           (let uu____23507 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____23507
                            then
                              let uu____23508 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____23508
                            else ());
                           (let cres =
                              let uu____23511 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12 in
                              if uu____23511
                              then
                                FStar_Syntax_Syntax.mk_Total'
                                  FStar_Syntax_Syntax.t_unit
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.U_zero)
                              else
                                (let c1_comp_typ =
                                   FStar_All.pipe_right c12
                                     (FStar_TypeChecker_Env.unfold_effect_abbrev
                                        env1) in
                                 let c1_wp =
                                   match c1_comp_typ.FStar_Syntax_Syntax.effect_args
                                   with
                                   | (wp, uu____23516)::[] -> wp
                                   | uu____23541 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args" in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator in
                                   let uu____23555 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [FStar_Syntax_Syntax.U_zero] env1
                                       c1_eff_decl ret in
                                   let uu____23556 =
                                     let uu____23557 =
                                       FStar_Syntax_Syntax.as_arg
                                         FStar_Syntax_Syntax.t_unit in
                                     let uu____23566 =
                                       let uu____23577 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.unit_const in
                                       [uu____23577] in
                                     uu____23557 :: uu____23566 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23555
                                     uu____23556 e21.FStar_Syntax_Syntax.pos in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator in
                                   let uu____23612 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       (FStar_List.append
                                          c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                          [FStar_Syntax_Syntax.U_zero]) env1
                                       c1_eff_decl bind in
                                   let uu____23613 =
                                     let uu____23614 =
                                       let uu____23623 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_constant
                                              (FStar_Const.Const_range
                                                 (lb.FStar_Syntax_Syntax.lbpos)))
                                           lb.FStar_Syntax_Syntax.lbpos in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____23623 in
                                     let uu____23632 =
                                       let uu____23643 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                       let uu____23660 =
                                         let uu____23671 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.t_unit in
                                         let uu____23680 =
                                           let uu____23691 =
                                             FStar_Syntax_Syntax.as_arg c1_wp in
                                           let uu____23700 =
                                             let uu____23711 =
                                               let uu____23720 =
                                                 let uu____23721 =
                                                   let uu____23722 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       c1_comp_typ.FStar_Syntax_Syntax.result_typ in
                                                   [uu____23722] in
                                                 FStar_Syntax_Util.abs
                                                   uu____23721 wp2
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Util.mk_residual_comp
                                                         FStar_Parser_Const.effect_Tot_lid
                                                         FStar_Pervasives_Native.None
                                                         [FStar_Syntax_Syntax.TOTAL])) in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23720 in
                                             [uu____23711] in
                                           uu____23691 :: uu____23700 in
                                         uu____23671 :: uu____23680 in
                                       uu____23643 :: uu____23660 in
                                     uu____23614 :: uu____23632 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____23612
                                     uu____23613 lb.FStar_Syntax_Syntax.lbpos in
                                 let uu____23799 =
                                   let uu____23800 =
                                     let uu____23811 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [uu____23811] in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____23800;
                                     FStar_Syntax_Syntax.flags = []
                                   } in
                                 FStar_Syntax_Syntax.mk_Comp uu____23799) in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos in
                            let uu____23839 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                e.FStar_Syntax_Syntax.pos in
                            let uu____23850 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres in
                            (uu____23839, uu____23850,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____23851 -> failwith "Impossible"
and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lem_typ ->
      fun c2 ->
        let uu____23861 = FStar_Syntax_Util.is_smt_lemma lem_typ in
        if uu____23861
        then
          let universe_of_binders bs =
            let uu____23886 =
              FStar_List.fold_left
                (fun uu____23911 ->
                   fun b ->
                     match uu____23911 with
                     | (env1, us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         (env2, (u :: us))) (env, []) bs in
            match uu____23886 with | (uu____23959, us) -> FStar_List.rev us in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2
and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let env2 =
            let uu___3259_23991 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3259_23991.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3259_23991.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3259_23991.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3259_23991.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3259_23991.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3259_23991.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3259_23991.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3259_23991.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3259_23991.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3259_23991.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3259_23991.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3259_23991.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3259_23991.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3259_23991.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3259_23991.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3259_23991.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3259_23991.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3259_23991.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3259_23991.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3259_23991.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3259_23991.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3259_23991.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3259_23991.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3259_23991.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3259_23991.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3259_23991.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3259_23991.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3259_23991.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3259_23991.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3259_23991.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3259_23991.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3259_23991.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3259_23991.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3259_23991.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3259_23991.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3259_23991.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3259_23991.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3259_23991.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3259_23991.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3259_23991.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3259_23991.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3259_23991.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3259_23991.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3259_23991.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3259_23991.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___3259_23991.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let uu____23992 =
            let uu____24003 =
              let uu____24004 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____24004 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____24003 lb in
          (match uu____23992 with
           | (e1, uu____24026, c1, g1, annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1 in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____24035 =
                     let uu____24040 =
                       let uu____24041 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____24042 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24041 uu____24042 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24040) in
                   FStar_Errors.raise_error uu____24035
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24049 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ) in
                   if uu____24049
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs in
                 let x =
                   let uu___3274_24058 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3274_24058.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3274_24058.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   } in
                 let uu____24059 =
                   let uu____24064 =
                     let uu____24065 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____24065] in
                   FStar_Syntax_Subst.open_term uu____24064 e2 in
                 match uu____24059 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____24109 =
                       let uu____24116 = tc_term env_x e21 in
                       FStar_All.pipe_right uu____24116
                         (fun uu____24142 ->
                            match uu____24142 with
                            | (e22, c2, g2) ->
                                let uu____24158 =
                                  let uu____24163 =
                                    FStar_All.pipe_right
                                      (fun uu____24178 ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____24182 ->
                                         FStar_Pervasives_Native.Some
                                           uu____24182) in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____24163 env_x e22 c2 g2 in
                                (match uu____24158 with
                                 | (c21, g21) -> (e22, c21, g21))) in
                     (match uu____24109 with
                      | (e22, c2, g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_TypeChecker_Common.res_typ c2 in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21) in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c21.FStar_TypeChecker_Common.res_typ in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_TypeChecker_Common.res_typ
                              cres.FStar_TypeChecker_Common.eff_name e11
                              attrs lb.FStar_Syntax_Syntax.lbpos in
                          let e3 =
                            let uu____24210 =
                              let uu____24211 =
                                let uu____24224 =
                                  FStar_Syntax_Subst.close xb e23 in
                                ((false, [lb1]), uu____24224) in
                              FStar_Syntax_Syntax.Tm_let uu____24211 in
                            FStar_Syntax_Syntax.mk uu____24210
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ in
                          let g21 =
                            let uu____24239 =
                              let uu____24240 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2) in
                              FStar_All.pipe_right uu____24240
                                (FStar_TypeChecker_Env.is_layered_effect env2) in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24239 xb g2 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21 in
                          let uu____24242 =
                            let uu____24243 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____24243 in
                          if uu____24242
                          then
                            let tt =
                              let uu____24253 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____24253
                                FStar_Option.get in
                            ((let uu____24259 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____24259
                              then
                                let uu____24260 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____24261 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____24260 uu____24261
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____24264 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ in
                             match uu____24264 with
                             | (t, g_ex) ->
                                 ((let uu____24278 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____24278
                                   then
                                     let uu____24279 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ in
                                     let uu____24280 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____24279 uu____24280
                                   else ());
                                  (let uu____24282 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___3313_24284 = cres in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3313_24284.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3313_24284.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3313_24284.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____24282))))))))
      | uu____24285 ->
          failwith "Impossible (inner let with more than one lb)"
and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____24317 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24317 with
           | (lbs1, e21) ->
               let uu____24336 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24336 with
                | (env0, topt) ->
                    let uu____24355 = build_let_rec_env true env0 lbs1 in
                    (match uu____24355 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24377 = check_let_recs rec_env lbs2 in
                         (match uu____24377 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____24397 =
                                  let uu____24398 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____24398
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____24397
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____24404 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____24404
                                  (fun uu____24421 ->
                                     FStar_Pervasives_Native.Some uu____24421) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef
                                              lb.FStar_Syntax_Syntax.lbattrs
                                              lb.FStar_Syntax_Syntax.lbpos))
                                else
                                  (let ecs =
                                     let uu____24454 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____24488 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____24488))) in
                                     FStar_TypeChecker_Generalize.generalize
                                       env1 true uu____24454 in
                                   FStar_List.map2
                                     (fun uu____24522 ->
                                        fun lb ->
                                          match uu____24522 with
                                          | (x, uvs, e, c, gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3) in
                              let cres =
                                let uu____24570 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____24570 in
                              let uu____24571 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____24571 with
                               | (lbs5, e22) ->
                                   ((let uu____24591 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____24591
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____24592 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____24592, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____24603 -> failwith "Impossible"
and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____24635 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____24635 with
           | (lbs1, e21) ->
               let uu____24654 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____24654 with
                | (env0, topt) ->
                    let uu____24673 = build_let_rec_env false env0 lbs1 in
                    (match uu____24673 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____24695 =
                           let uu____24702 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____24702
                             (fun uu____24725 ->
                                match uu____24725 with
                                | (lbs3, g) ->
                                    let uu____24744 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____24744)) in
                         (match uu____24695 with
                          | (lbs3, g_lbs) ->
                              let uu____24759 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___3388_24782 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3388_24782.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3388_24782.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___3391_24784 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3391_24784.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____24759 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____24811 = tc_term env2 e21 in
                                   (match uu____24811 with
                                    | (e22, cres, g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb ->
                                               fun cres1 ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1 in
                                        let cres3 =
                                          FStar_TypeChecker_Common.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____24835 =
                                            let uu____24836 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____24836 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____24835 in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3 in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ in
                                        let cres5 =
                                          let uu___3412_24846 = cres4 in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3412_24846.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3412_24846.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3412_24846.FStar_TypeChecker_Common.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____24854 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24854)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard in
                                        let uu____24855 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____24855 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____24893 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____24894 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____24894 with
                                                   | (tres1, g_ex) ->
                                                       let cres6 =
                                                         let uu___3428_24908
                                                           = cres5 in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3428_24908.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3428_24908.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3428_24908.FStar_TypeChecker_Common.comp_thunk)
                                                         } in
                                                       let uu____24909 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres6,
                                                         uu____24909))))))))))
      | uu____24910 -> failwith "Impossible"
and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun _top_level ->
    fun env ->
      fun lbs ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____24959 = FStar_Options.ml_ish () in
          if uu____24959
          then FStar_Pervasives_Native.None
          else
            (let lbtyp0 = lbtyp in
             let uu____24972 = FStar_Syntax_Util.abs_formals lbdef in
             match uu____24972 with
             | (actuals, body, body_lc) ->
                 let actuals1 =
                   let uu____24995 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____24995 actuals in
                 let nactuals = FStar_List.length actuals1 in
                 let uu____25003 =
                   FStar_TypeChecker_Normalize.get_n_binders env nactuals
                     lbtyp in
                 (match uu____25003 with
                  | (formals, c) ->
                      (if
                         (FStar_List.isEmpty formals) ||
                           (FStar_List.isEmpty actuals1)
                       then
                         (let uu____25029 =
                            let uu____25034 =
                              let uu____25035 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              let uu____25036 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              FStar_Util.format2
                                "Only function literals with arrow types can be defined recursively; got %s : %s"
                                uu____25035 uu____25036 in
                            (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                              uu____25034) in
                          FStar_Errors.raise_error uu____25029
                            lbtyp.FStar_Syntax_Syntax.pos)
                       else ();
                       (let nformals = FStar_List.length formals in
                        let uu____25039 =
                          let uu____25040 =
                            FStar_All.pipe_right
                              (FStar_Syntax_Util.comp_effect_name c)
                              (FStar_TypeChecker_Env.lookup_effect_quals env) in
                          FStar_All.pipe_right uu____25040
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect) in
                        if uu____25039
                        then
                          let uu____25053 =
                            let uu____25058 =
                              FStar_Syntax_Util.abs actuals1 body body_lc in
                            (nformals, uu____25058) in
                          FStar_Pervasives_Native.Some uu____25053
                        else FStar_Pervasives_Native.None)))) in
        let uu____25068 =
          FStar_List.fold_left
            (fun uu____25102 ->
               fun lb ->
                 match uu____25102 with
                 | (lbs1, env1, g_acc) ->
                     let uu____25127 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____25127 with
                      | (univ_vars, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____25147 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars in
                               let uu____25164 =
                                 let uu____25171 =
                                   let uu____25172 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____25172 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3468_25183 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3468_25183.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3468_25183.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3468_25183.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3468_25183.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3468_25183.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3468_25183.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3468_25183.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3468_25183.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3468_25183.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3468_25183.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3468_25183.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3468_25183.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3468_25183.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3468_25183.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3468_25183.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3468_25183.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3468_25183.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3468_25183.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3468_25183.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3468_25183.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3468_25183.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3468_25183.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3468_25183.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3468_25183.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3468_25183.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3468_25183.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3468_25183.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3468_25183.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3468_25183.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3468_25183.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3468_25183.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3468_25183.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3468_25183.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3468_25183.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3468_25183.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3468_25183.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3468_25183.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3468_25183.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3468_25183.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3468_25183.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3468_25183.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3468_25183.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3468_25183.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3468_25183.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3468_25183.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___3468_25183.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }) t uu____25171 "" in
                               match uu____25164 with
                               | (t1, uu____25191, g) ->
                                   let uu____25193 =
                                     let uu____25194 =
                                       let uu____25195 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____25195
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____25194 in
                                   let uu____25196 = norm env01 t1 in
                                   (uu____25193, uu____25196)) in
                          (match uu____25147 with
                           | (g, t1) ->
                               let uu____25215 =
                                 let uu____25220 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 match uu____25220 with
                                 | FStar_Pervasives_Native.Some (arity, def)
                                     ->
                                     let lb1 =
                                       let uu___3481_25238 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3481_25238.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3481_25238.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = def;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3481_25238.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3481_25238.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let env3 =
                                       let uu___3484_25240 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___3484_25240.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___3484_25240.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___3484_25240.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___3484_25240.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_sig =
                                           (uu___3484_25240.FStar_TypeChecker_Env.gamma_sig);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___3484_25240.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___3484_25240.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___3484_25240.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___3484_25240.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.attrtab =
                                           (uu___3484_25240.FStar_TypeChecker_Env.attrtab);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___3484_25240.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___3484_25240.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (((lb1.FStar_Syntax_Syntax.lbname),
                                              arity, t1, univ_vars) ::
                                           (env2.FStar_TypeChecker_Env.letrecs));
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___3484_25240.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___3484_25240.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___3484_25240.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.use_eq_strict
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.use_eq_strict);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___3484_25240.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___3484_25240.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___3484_25240.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.phase1 =
                                           (uu___3484_25240.FStar_TypeChecker_Env.phase1);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___3484_25240.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___3484_25240.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.uvar_subtyping
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.uvar_subtyping);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___3484_25240.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___3484_25240.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___3484_25240.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.check_type_of
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.check_type_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           (uu___3484_25240.FStar_TypeChecker_Env.use_bv_sorts);
                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.qtbl_name_and_index);
                                         FStar_TypeChecker_Env.normalized_eff_names
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.normalized_eff_names);
                                         FStar_TypeChecker_Env.fv_delta_depths
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.fv_delta_depths);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___3484_25240.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth_hook =
                                           (uu___3484_25240.FStar_TypeChecker_Env.synth_hook);
                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                         FStar_TypeChecker_Env.splice =
                                           (uu___3484_25240.FStar_TypeChecker_Env.splice);
                                         FStar_TypeChecker_Env.mpreprocess =
                                           (uu___3484_25240.FStar_TypeChecker_Env.mpreprocess);
                                         FStar_TypeChecker_Env.postprocess =
                                           (uu___3484_25240.FStar_TypeChecker_Env.postprocess);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___3484_25240.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___3484_25240.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.nbe =
                                           (uu___3484_25240.FStar_TypeChecker_Env.nbe);
                                         FStar_TypeChecker_Env.strict_args_tab
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.strict_args_tab);
                                         FStar_TypeChecker_Env.erasable_types_tab
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.erasable_types_tab);
                                         FStar_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (uu___3484_25240.FStar_TypeChecker_Env.enable_defer_to_tac)
                                       } in
                                     (lb1, env3)
                                 | FStar_Pervasives_Native.None ->
                                     let lb1 =
                                       let uu___3488_25254 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___3488_25254.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           univ_vars;
                                         FStar_Syntax_Syntax.lbtyp = t1;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___3488_25254.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___3488_25254.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___3488_25254.FStar_Syntax_Syntax.lbpos)
                                       } in
                                     let uu____25255 =
                                       FStar_TypeChecker_Env.push_let_binding
                                         env2 lb1.FStar_Syntax_Syntax.lbname
                                         (univ_vars, t1) in
                                     (lb1, uu____25255) in
                               (match uu____25215 with
                                | (lb1, env3) -> ((lb1 :: lbs1), env3, g)))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____25068 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun lbs ->
      let uu____25295 =
        let uu____25304 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____25330 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____25330 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____25360 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____25360
                       | uu____25365 ->
                           let arity =
                             let uu____25368 =
                               FStar_TypeChecker_Env.get_letrec_arity env
                                 lb.FStar_Syntax_Syntax.lbname in
                             match uu____25368 with
                             | FStar_Pervasives_Native.Some n -> n
                             | FStar_Pervasives_Native.None ->
                                 FStar_List.length bs in
                           let uu____25378 = FStar_List.splitAt arity bs in
                           (match uu____25378 with
                            | (bs0, bs1) ->
                                let def =
                                  if FStar_List.isEmpty bs1
                                  then FStar_Syntax_Util.abs bs0 t lcomp
                                  else
                                    (let inner =
                                       FStar_Syntax_Util.abs bs1 t lcomp in
                                     let inner1 =
                                       FStar_Syntax_Subst.close bs0 inner in
                                     let bs01 =
                                       FStar_Syntax_Subst.close_binders bs0 in
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_abs
                                          (bs01, inner1,
                                            FStar_Pervasives_Native.None))
                                       inner1.FStar_Syntax_Syntax.pos) in
                                let lb1 =
                                  let uu___3520_25473 = lb in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbtyp);
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___3520_25473.FStar_Syntax_Syntax.lbpos)
                                  } in
                                let uu____25474 =
                                  let uu____25481 =
                                    FStar_TypeChecker_Env.set_expected_typ
                                      env lb1.FStar_Syntax_Syntax.lbtyp in
                                  tc_tot_or_gtot_term uu____25481
                                    lb1.FStar_Syntax_Syntax.lbdef in
                                (match uu____25474 with
                                 | (e, c, g) ->
                                     ((let uu____25490 =
                                         let uu____25491 =
                                           FStar_TypeChecker_Common.is_total_lcomp
                                             c in
                                         Prims.op_Negation uu____25491 in
                                       if uu____25490
                                       then
                                         FStar_Errors.raise_error
                                           (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                             "Expected let rec to be a Tot term; got effect GTot")
                                           e.FStar_Syntax_Syntax.pos
                                       else ());
                                      (let lb2 =
                                         FStar_Syntax_Util.mk_letbinding
                                           lb1.FStar_Syntax_Syntax.lbname
                                           lb1.FStar_Syntax_Syntax.lbunivs
                                           lb1.FStar_Syntax_Syntax.lbtyp
                                           FStar_Parser_Const.effect_Tot_lid
                                           e lb1.FStar_Syntax_Syntax.lbattrs
                                           lb1.FStar_Syntax_Syntax.lbpos in
                                       (lb2, g)))))))) in
        FStar_All.pipe_right uu____25304 FStar_List.unzip in
      match uu____25295 with
      | (lbs1, gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard in
          (lbs1, g_lbs)
and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t *
          Prims.bool))
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let uu____25540 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____25540 with
        | (env1, uu____25558) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____25566 = check_lbtyp top_level env lb in
            (match uu____25566 with
             | (topt, wf_annot, univ_vars, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____25610 =
                     tc_maybe_toplevel_term
                       (let uu___3551_25619 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3551_25619.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3551_25619.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3551_25619.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3551_25619.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3551_25619.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3551_25619.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3551_25619.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3551_25619.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3551_25619.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3551_25619.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3551_25619.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3551_25619.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3551_25619.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3551_25619.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3551_25619.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3551_25619.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3551_25619.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3551_25619.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3551_25619.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3551_25619.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3551_25619.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3551_25619.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3551_25619.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3551_25619.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3551_25619.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3551_25619.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3551_25619.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3551_25619.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3551_25619.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3551_25619.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3551_25619.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3551_25619.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3551_25619.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3551_25619.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3551_25619.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3551_25619.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3551_25619.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3551_25619.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3551_25619.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3551_25619.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3551_25619.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3551_25619.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3551_25619.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3551_25619.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3551_25619.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___3551_25619.FStar_TypeChecker_Env.enable_defer_to_tac)
                        }) e11 in
                   match uu____25610 with
                   | (e12, c1, g1) ->
                       let uu____25633 =
                         let uu____25638 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____25643 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____25638 e12 c1 wf_annot in
                       (match uu____25633 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____25658 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____25658
                              then
                                let uu____25659 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____25660 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11 in
                                let uu____25661 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____25659 uu____25660 uu____25661
                              else ());
                             (e12, univ_vars, c11, g11,
                               (FStar_Option.isSome topt)))))))
and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____25695 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25695 with
             | (univ_opening, univ_vars) ->
                 let uu____25728 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____25728))
        | uu____25733 ->
            let uu____25734 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____25734 with
             | (univ_opening, univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____25783 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____25783)
                 else
                   (let uu____25789 = FStar_Syntax_Util.type_u () in
                    match uu____25789 with
                    | (k, uu____25809) ->
                        let uu____25810 =
                          tc_check_tot_or_gtot_term env1 t1 k "" in
                        (match uu____25810 with
                         | (t2, uu____25832, g) ->
                             ((let uu____25835 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____25835
                               then
                                 let uu____25836 =
                                   let uu____25837 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____25837 in
                                 let uu____25838 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____25836 uu____25838
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____25841 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____25841))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env ->
    fun uu____25847 ->
      match uu____25847 with
      | (x, imp) ->
          let uu____25874 = FStar_Syntax_Util.type_u () in
          (match uu____25874 with
           | (tu, u) ->
               ((let uu____25896 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____25896
                 then
                   let uu____25897 = FStar_Syntax_Print.bv_to_string x in
                   let uu____25898 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____25899 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25897 uu____25898 uu____25899
                 else ());
                (let uu____25901 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu "" in
                 match uu____25901 with
                 | (t, uu____25923, g) ->
                     let uu____25925 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau_or_attr) ->
                           (match tau_or_attr with
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                ->
                                let uu____25948 =
                                  tc_tactic FStar_Syntax_Syntax.t_unit
                                    FStar_Syntax_Syntax.t_unit env tau in
                                (match uu____25948 with
                                 | (tau1, uu____25962, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                               tau1))), g1))
                            | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                attr ->
                                let uu____25969 =
                                  tc_check_tot_or_gtot_term env attr
                                    FStar_Syntax_Syntax.t_unit "" in
                                (match uu____25969 with
                                 | (attr1, uu____25983, g1) ->
                                     ((FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Meta
                                            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                               attr1))),
                                       FStar_TypeChecker_Env.trivial_guard)))
                       | uu____25987 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____25925 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___3621_26022 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3621_26022.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3621_26022.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____26024 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____26024
                            then
                              let uu____26025 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____26028 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26025
                                uu____26028
                            else ());
                           (let uu____26030 = push_binding env x1 in
                            (x1, uu____26030, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun bs ->
      (let uu____26042 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____26042
       then
         let uu____26043 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____26043
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26152 = tc_binder env1 b in
             (match uu____26152 with
              | (b1, env', g, u) ->
                  let uu____26201 = aux env' bs2 in
                  (match uu____26201 with
                   | (bs3, env'1, g', us) ->
                       let uu____26262 =
                         let uu____26263 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____26263 in
                       ((b1 :: bs3), env'1, uu____26262, (u :: us)))) in
       aux env bs)
and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun en ->
    fun pats ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____26371 ->
             fun uu____26372 ->
               match (uu____26371, uu____26372) with
               | ((t, imp), (args1, g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____26464 = tc_term en1 t in
                     match uu____26464 with
                     | (t1, uu____26484, g') ->
                         let uu____26486 =
                           FStar_TypeChecker_Env.conj_guard g g' in
                         (((t1, imp) :: args1), uu____26486)))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____26540 ->
             match uu____26540 with
             | (pats1, g) ->
                 let uu____26567 = tc_args en p in
                 (match uu____26567 with
                  | (args, g') ->
                      let uu____26580 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____26580))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)
and (tc_tot_or_gtot_term' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      Prims.string ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun msg ->
        let uu____26594 = tc_maybe_toplevel_term env e in
        match uu____26594 with
        | (e1, c, g) ->
            let uu____26610 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c in
            if uu____26610
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g in
               let uu____26619 = FStar_TypeChecker_Common.lcomp_comp c in
               match uu____26619 with
               | (c1, g_c) ->
                   let c2 = norm_c env c1 in
                   let uu____26633 =
                     let uu____26638 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2) in
                     if uu____26638
                     then
                       let uu____26643 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2) in
                       (uu____26643, false)
                     else
                       (let uu____26645 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2) in
                        (uu____26645, true)) in
                   (match uu____26633 with
                    | (target_comp, allow_ghost) ->
                        let uu____26654 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                        (match uu____26654 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____26664 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp in
                             let uu____26665 =
                               let uu____26666 =
                                 FStar_TypeChecker_Env.conj_guard g_c g' in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____26666 in
                             (e1, uu____26664, uu____26665)
                         | uu____26667 ->
                             if allow_ghost
                             then
                               let uu____26676 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg in
                               FStar_Errors.raise_error uu____26676
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____26688 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg in
                                FStar_Errors.raise_error uu____26688
                                  e1.FStar_Syntax_Syntax.pos))))
and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  = fun env -> fun e -> tc_tot_or_gtot_term' env e ""
and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.string ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun t ->
        fun msg ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
          tc_tot_or_gtot_term' env1 e msg
and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env ->
    fun t ->
      let uu____26714 = tc_tot_or_gtot_term env t in
      match uu____26714 with
      | (t1, c, g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____26744 = tc_check_tot_or_gtot_term env t k "" in
        match uu____26744 with
        | (t1, uu____26752, g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____26772 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____26772
       then
         let uu____26773 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____26773
       else ());
      (let env1 =
         let uu___3717_26776 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3717_26776.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3717_26776.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3717_26776.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3717_26776.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3717_26776.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3717_26776.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3717_26776.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3717_26776.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3717_26776.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3717_26776.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3717_26776.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3717_26776.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3717_26776.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3717_26776.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3717_26776.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3717_26776.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3717_26776.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3717_26776.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3717_26776.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3717_26776.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3717_26776.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3717_26776.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3717_26776.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3717_26776.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3717_26776.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3717_26776.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3717_26776.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3717_26776.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3717_26776.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3717_26776.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3717_26776.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3717_26776.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3717_26776.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3717_26776.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3717_26776.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3717_26776.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3717_26776.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3717_26776.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3717_26776.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3717_26776.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3717_26776.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3717_26776.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3717_26776.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3717_26776.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___3717_26776.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let uu____26785 =
         try
           (fun uu___3721_26799 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____26821, ctx) ->
             let uu____26827 =
               let uu____26828 =
                 let uu____26829 = FStar_TypeChecker_Env.get_range env1 in
                 (e1, msg, uu____26829, ctx) in
               FStar_Errors.Error uu____26828 in
             FStar_Exn.raise uu____26827 in
       match uu____26785 with
       | (t, c, g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c in
           let uu____26848 = FStar_TypeChecker_Common.is_total_lcomp c1 in
           if uu____26848
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____26856 =
                let uu____26861 =
                  let uu____26862 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____26862 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____26861) in
              let uu____26863 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____26856 uu____26863))
let level_of_type_fail :
  'uuuuuu26878 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu26878
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____26894 =
          let uu____26899 =
            let uu____26900 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26900 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____26899) in
        let uu____26901 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____26894 uu____26901
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____26932 =
            let uu____26933 = FStar_Syntax_Util.unrefine t1 in
            uu____26933.FStar_Syntax_Syntax.n in
          match uu____26932 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26937 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____26940 = FStar_Syntax_Util.type_u () in
                 match uu____26940 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___3754_26948 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3754_26948.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3754_26948.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3754_26948.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3754_26948.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3754_26948.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3754_26948.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3754_26948.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3754_26948.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3754_26948.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3754_26948.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3754_26948.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3754_26948.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3754_26948.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3754_26948.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3754_26948.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3754_26948.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3754_26948.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3754_26948.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3754_26948.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3754_26948.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3754_26948.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3754_26948.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3754_26948.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3754_26948.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3754_26948.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3754_26948.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3754_26948.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3754_26948.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3754_26948.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3754_26948.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3754_26948.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3754_26948.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3754_26948.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3754_26948.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3754_26948.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3754_26948.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3754_26948.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3754_26948.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3754_26948.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3754_26948.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3754_26948.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3754_26948.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3754_26948.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3754_26948.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3754_26948.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3754_26948.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26952 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____26952
                       | uu____26953 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun e ->
      let uu____26968 =
        let uu____26969 = FStar_Syntax_Subst.compress e in
        uu____26969.FStar_Syntax_Syntax.n in
      match uu____26968 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26972 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26973 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26988 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____27004) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____27048) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27055 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____27055 with | ((uu____27064, t), uu____27066) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27072 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____27072
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27075, (FStar_Util.Inl t, uu____27077), uu____27078) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27125, (FStar_Util.Inr c, uu____27127), uu____27128) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27176 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27185;
             FStar_Syntax_Syntax.vars = uu____27186;_},
           us)
          ->
          let uu____27192 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____27192 with
           | ((us', t), uu____27203) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27209 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27209)
                else ();
                FStar_List.iter2
                  (fun ul ->
                     fun ur ->
                       match (ul, ur) with
                       | (FStar_Syntax_Syntax.U_unif u'', uu____27219) ->
                           FStar_Syntax_Unionfind.univ_change u'' ur
                       | (FStar_Syntax_Syntax.U_name n1,
                          FStar_Syntax_Syntax.U_name n2) when
                           FStar_Ident.ident_equals n1 n2 -> ()
                       | uu____27232 ->
                           let uu____27237 =
                             let uu____27242 =
                               let uu____27243 =
                                 FStar_Syntax_Print.fv_to_string fv in
                               let uu____27244 =
                                 FStar_Syntax_Print.univ_to_string ul in
                               let uu____27245 =
                                 FStar_Syntax_Print.univ_to_string ur in
                               FStar_Util.format3
                                 "Incompatible universe application for %s, expected %s got %s\n"
                                 uu____27243 uu____27244 uu____27245 in
                             (FStar_Errors.Fatal_IncompatibleUniverse,
                               uu____27242) in
                           let uu____27246 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Errors.raise_error uu____27237 uu____27246)
                  us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27247 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____27255) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____27282 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____27282 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____27302 ->
                      match uu____27302 with
                      | (b, uu____27310) ->
                          let uu____27315 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____27315) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____27320 = universe_of_aux env res in
                 level_of_type env res uu____27320 in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res) in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let rec type_of_head retry hd1 args1 =
            let hd2 = FStar_Syntax_Subst.compress hd1 in
            match hd2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____27428 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____27443 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____27472 ->
                let uu____27473 = universe_of_aux env hd2 in
                (uu____27473, args1)
            | FStar_Syntax_Syntax.Tm_name uu____27484 ->
                let uu____27485 = universe_of_aux env hd2 in
                (uu____27485, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____27496 ->
                let uu____27509 = universe_of_aux env hd2 in
                (uu____27509, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____27520 ->
                let uu____27527 = universe_of_aux env hd2 in
                (uu____27527, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____27538 ->
                let uu____27565 = universe_of_aux env hd2 in
                (uu____27565, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____27576 ->
                let uu____27583 = universe_of_aux env hd2 in
                (uu____27583, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____27594 ->
                let uu____27595 = universe_of_aux env hd2 in
                (uu____27595, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____27606 ->
                let uu____27621 = universe_of_aux env hd2 in
                (uu____27621, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____27632 ->
                let uu____27639 = universe_of_aux env hd2 in
                (uu____27639, args1)
            | FStar_Syntax_Syntax.Tm_type uu____27650 ->
                let uu____27651 = universe_of_aux env hd2 in
                (uu____27651, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____27662, hd3::uu____27664) ->
                let uu____27729 = FStar_Syntax_Subst.open_branch hd3 in
                (match uu____27729 with
                 | (uu____27744, uu____27745, hd4) ->
                     let uu____27763 = FStar_Syntax_Util.head_and_args hd4 in
                     (match uu____27763 with
                      | (hd5, args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____27828 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____27830 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____27830 with
                 | (hd3, args2) -> type_of_head false hd3 args2)
            | uu____27887 ->
                let uu____27888 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____27888 with
                 | (env1, uu____27910) ->
                     let env2 =
                       let uu___3923_27916 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3923_27916.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3923_27916.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3923_27916.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3923_27916.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3923_27916.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3923_27916.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3923_27916.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3923_27916.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3923_27916.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3923_27916.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3923_27916.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3923_27916.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3923_27916.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3923_27916.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3923_27916.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3923_27916.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3923_27916.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3923_27916.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3923_27916.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3923_27916.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3923_27916.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3923_27916.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3923_27916.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3923_27916.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3923_27916.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3923_27916.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3923_27916.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3923_27916.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3923_27916.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3923_27916.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3923_27916.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3923_27916.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3923_27916.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3923_27916.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3923_27916.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3923_27916.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3923_27916.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3923_27916.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3923_27916.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3923_27916.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3923_27916.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3923_27916.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3923_27916.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___3923_27916.FStar_TypeChecker_Env.enable_defer_to_tac)
                       } in
                     ((let uu____27918 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____27918
                       then
                         let uu____27919 =
                           let uu____27920 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____27920 in
                         let uu____27921 =
                           FStar_Syntax_Print.term_to_string hd2 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27919 uu____27921
                       else ());
                      (let uu____27923 = tc_term env2 hd2 in
                       match uu____27923 with
                       | (uu____27944,
                          { FStar_TypeChecker_Common.eff_name = uu____27945;
                            FStar_TypeChecker_Common.res_typ = t;
                            FStar_TypeChecker_Common.cflags = uu____27947;
                            FStar_TypeChecker_Common.comp_thunk = uu____27948;_},
                          g) ->
                           ((let uu____27966 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____27966
                               (fun uu____27967 -> ()));
                            (t, args1))))) in
          let uu____27978 = type_of_head true hd args in
          (match uu____27978 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____28016 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____28016 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____28042 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____28042)))
      | FStar_Syntax_Syntax.Tm_match (uu____28043, hd::uu____28045) ->
          let uu____28110 = FStar_Syntax_Subst.open_branch hd in
          (match uu____28110 with
           | (uu____28111, uu____28112, hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____28130, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      (let uu____28176 = FStar_TypeChecker_Env.debug env FStar_Options.High in
       if uu____28176
       then
         let uu____28177 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Calling universe_of_aux with %s\n" uu____28177
       else ());
      (let r = universe_of_aux env e in
       (let uu____28181 = FStar_TypeChecker_Env.debug env FStar_Options.High in
        if uu____28181
        then
          let uu____28182 = FStar_Syntax_Print.term_to_string r in
          FStar_Util.print1 "Got result from universe_of_aux = %s\n"
            uu____28182
        else ());
       level_of_type env e r)
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0 ->
    fun tps ->
      let uu____28206 = tc_binders env0 tps in
      match uu____28206 with
      | (tps1, env, g, us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env0 g; (tps1, env, us))
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          t.FStar_Syntax_Syntax.pos in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____28263 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____28280 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28285 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____28285
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28287 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28287
            (fun uu____28301 ->
               match uu____28301 with
               | (t2, uu____28309) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28311;
             FStar_Syntax_Syntax.vars = uu____28312;_},
           us)
          ->
          let uu____28318 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____28318
            (fun uu____28332 ->
               match uu____28332 with
               | (t2, uu____28340) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____28341) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____28343 = tc_constant env t1.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____28343
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____28345 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____28345
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____28350;_})
          ->
          let mk_comp =
            let uu____28394 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____28394
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____28422 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____28422
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____28489 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____28489
                 (fun u ->
                    let uu____28497 =
                      let uu____28500 =
                        let uu____28501 =
                          let uu____28516 =
                            f tbody (FStar_Pervasives_Native.Some u) in
                          (bs, uu____28516) in
                        FStar_Syntax_Syntax.Tm_arrow uu____28501 in
                      FStar_Syntax_Syntax.mk uu____28500
                        t1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____28497))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____28553 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____28553 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____28612 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____28612
                       (fun uc ->
                          let uu____28620 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____28620)
                 | (x, imp)::bs3 ->
                     let uu____28646 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____28646
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____28655 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____28675) ->
          let uu____28680 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____28680
            (fun u_x ->
               let uu____28688 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____28688)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____28693;
             FStar_Syntax_Syntax.vars = uu____28694;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28773 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28773 with
           | (unary_op, uu____28793) ->
               let head =
                 let uu____28821 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) uu____28821 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____28869;
             FStar_Syntax_Syntax.vars = uu____28870;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____28966 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____28966 with
           | (unary_op, uu____28986) ->
               let head =
                 let uu____29014 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   uu____29014 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____29070;
             FStar_Syntax_Syntax.vars = uu____29071;_},
           uu____29072::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____29111;
             FStar_Syntax_Syntax.vars = uu____29112;_},
           (t2, uu____29114)::uu____29115::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd, args) ->
          let t_hd = type_of_well_typed_term env hd in
          let rec aux t_hd1 =
            let uu____29211 =
              let uu____29212 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____29212.FStar_Syntax_Syntax.n in
            match uu____29211 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____29284 = FStar_Util.first_N n_args bs in
                    match uu____29284 with
                    | (bs1, rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____29372 =
                          let uu____29377 = FStar_Syntax_Syntax.mk_Total t2 in
                          FStar_Syntax_Subst.open_comp bs1 uu____29377 in
                        (match uu____29372 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____29429 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____29429 with
                       | (bs1, c1) ->
                           let uu____29450 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____29450
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____29528 ->
                     match uu____29528 with
                     | (bs1, t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____29604 = FStar_Syntax_Subst.subst subst t2 in
                         FStar_Pervasives_Native.Some uu____29604)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____29606) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____29612, uu____29613)
                -> aux t2
            | uu____29654 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29655, (FStar_Util.Inl t2, uu____29657), uu____29658) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29705, (FStar_Util.Inr c, uu____29707), uu____29708) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____29773 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____29773
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____29781) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____29786 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____29809 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29822 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____29833 = type_of_well_typed_term env t in
      match uu____29833 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29839;
            FStar_Syntax_Syntax.vars = uu____29840;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29843 -> FStar_Pervasives_Native.None
let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___4207_29868 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4207_29868.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4207_29868.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4207_29868.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4207_29868.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4207_29868.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4207_29868.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4207_29868.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4207_29868.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4207_29868.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4207_29868.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4207_29868.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4207_29868.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4207_29868.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4207_29868.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4207_29868.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4207_29868.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4207_29868.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4207_29868.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4207_29868.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4207_29868.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4207_29868.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4207_29868.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4207_29868.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4207_29868.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4207_29868.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4207_29868.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4207_29868.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4207_29868.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4207_29868.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4207_29868.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4207_29868.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4207_29868.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4207_29868.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4207_29868.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4207_29868.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4207_29868.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4207_29868.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4207_29868.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4207_29868.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4207_29868.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4207_29868.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4207_29868.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4207_29868.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4207_29868.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4207_29868.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4207_29868.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29874 =
            if must_total
            then
              let uu____29875 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29875 with | (uu____29882, uu____29883, g) -> g
            else
              (let uu____29886 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29886 with | (uu____29893, uu____29894, g) -> g) in
          let uu____29896 = type_of_well_typed_term env2 t in
          match uu____29896 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29901 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____29901
                then
                  let uu____29902 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____29903 = FStar_Syntax_Print.term_to_string t in
                  let uu____29904 = FStar_Syntax_Print.term_to_string k' in
                  let uu____29905 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29902 uu____29903 uu____29904 uu____29905
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____29911 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____29911
                 then
                   let uu____29912 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____29913 = FStar_Syntax_Print.term_to_string t in
                   let uu____29914 = FStar_Syntax_Print.term_to_string k' in
                   let uu____29915 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29912
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29913 uu____29914 uu____29915
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___4238_29941 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4238_29941.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4238_29941.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4238_29941.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4238_29941.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4238_29941.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4238_29941.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4238_29941.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4238_29941.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4238_29941.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4238_29941.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4238_29941.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4238_29941.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4238_29941.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4238_29941.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4238_29941.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4238_29941.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4238_29941.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4238_29941.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4238_29941.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4238_29941.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4238_29941.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4238_29941.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4238_29941.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4238_29941.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4238_29941.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4238_29941.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4238_29941.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4238_29941.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4238_29941.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4238_29941.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4238_29941.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4238_29941.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4238_29941.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4238_29941.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4238_29941.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4238_29941.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4238_29941.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4238_29941.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4238_29941.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4238_29941.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4238_29941.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4238_29941.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4238_29941.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4238_29941.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4238_29941.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___4238_29941.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let slow_check uu____29947 =
            if must_total
            then
              let uu____29948 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____29948 with | (uu____29955, uu____29956, g) -> g
            else
              (let uu____29959 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____29959 with | (uu____29966, uu____29967, g) -> g) in
          let uu____29969 =
            let uu____29970 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____29970 in
          if uu____29969
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k