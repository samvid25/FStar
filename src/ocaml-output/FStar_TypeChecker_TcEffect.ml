open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env -> fun ed -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env ->
    fun eff_name ->
      fun comb ->
        fun n ->
          fun uu____54 ->
            match uu____54 with
            | (us, t) ->
                let uu____73 = FStar_Syntax_Subst.open_univ_vars us t in
                (match uu____73 with
                 | (us1, t1) ->
                     let uu____86 =
                       let uu____91 =
                         let uu____98 =
                           FStar_TypeChecker_Env.push_univ_vars env us1 in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____98 t1 in
                       match uu____91 with
                       | (t2, lc, g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ))) in
                     (match uu____86 with
                      | (t2, ty) ->
                          let uu____115 =
                            FStar_TypeChecker_Generalize.generalize_universes
                              env t2 in
                          (match uu____115 with
                           | (g_us, t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty in
                               (if (FStar_List.length g_us) <> n
                                then
                                  (let error =
                                     let uu____135 =
                                       FStar_Util.string_of_int n in
                                     let uu____136 =
                                       let uu____137 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length in
                                       FStar_All.pipe_right uu____137
                                         FStar_Util.string_of_int in
                                     let uu____140 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3) in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____135 uu____136
                                       uu____140 in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____146 ->
                                        let uu____147 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1 ->
                                                  fun u2 ->
                                                    let uu____153 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2 in
                                                    uu____153 =
                                                      Prims.int_zero) us1
                                               g_us) in
                                        if uu____147
                                        then ()
                                        else
                                          (let uu____155 =
                                             let uu____160 =
                                               let uu____161 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1 in
                                               let uu____162 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____161
                                                 uu____162 in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____160) in
                                           FStar_Errors.raise_error uu____155
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun t ->
      fun reason ->
        fun r ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____194 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid in
              FStar_All.pipe_right uu____194 FStar_Util.must in
            let uu____199 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts in
            match uu____199 with
            | (uu____204, pure_wp_t) ->
                let uu____206 =
                  let uu____207 =
                    FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                  [uu____207] in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____206 r in
          let uu____240 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t in
          match uu____240 with
          | (pure_wp_uvar, uu____258, guard_wp) -> (pure_wp_uvar, guard_wp)
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env ->
    fun t ->
      fun k ->
        (let uu____292 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____292
         then
           let uu____293 = FStar_Syntax_Print.term_to_string t in
           let uu____294 =
             match k with
             | FStar_Pervasives_Native.None -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1 in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____293 uu____294
         else ());
        (let env1 =
           let uu___54_298 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_298.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_298.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_298.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_298.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_298.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_298.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_298.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_298.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_298.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_298.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_298.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_298.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_298.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_298.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_298.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_298.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_298.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_298.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_298.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_298.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_298.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_298.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_298.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_298.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_298.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_298.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_298.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_298.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_298.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_298.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_298.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_298.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_298.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_298.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_298.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_298.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_298.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_298.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_298.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_298.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_298.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_298.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_298.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_298.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_298.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___54_298.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         match k with
         | FStar_Pervasives_Native.None ->
             let uu____299 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____305 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k1 in
             ())
let (validate_layered_effect_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term Prims.list ->
        Prims.bool -> FStar_Range.range -> unit)
  =
  fun env ->
    fun bs ->
      fun repr_terms ->
        fun check_non_informatve_binders ->
          fun r ->
            let repr_args repr =
              let uu____351 =
                let uu____352 = FStar_Syntax_Subst.compress repr in
                uu____352.FStar_Syntax_Syntax.n in
              match uu____351 with
              | FStar_Syntax_Syntax.Tm_app (uu____365, args) -> args
              | FStar_Syntax_Syntax.Tm_arrow (uu____391::[], c) ->
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_args
              | uu____433 ->
                  let uu____434 =
                    let uu____439 =
                      let uu____440 = FStar_Syntax_Print.term_to_string repr in
                      FStar_Util.format1
                        "Unexpected repr term %s when validating layered effect combinator binders"
                        uu____440 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____439) in
                  FStar_Errors.raise_error uu____434 r in
            let rec head_names_in_term arg =
              let uu____461 =
                let uu____462 = FStar_Syntax_Subst.compress arg in
                uu____462.FStar_Syntax_Syntax.n in
              match uu____461 with
              | FStar_Syntax_Syntax.Tm_name uu____469 -> [arg]
              | FStar_Syntax_Syntax.Tm_app (head, uu____475) ->
                  let uu____500 =
                    let uu____501 = FStar_Syntax_Subst.compress head in
                    uu____501.FStar_Syntax_Syntax.n in
                  (match uu____500 with
                   | FStar_Syntax_Syntax.Tm_name uu____508 -> [head]
                   | uu____513 -> [])
              | FStar_Syntax_Syntax.Tm_abs (uu____516, body, uu____518) ->
                  head_names_in_term body
              | uu____543 -> [] in
            let head_names_in_args args =
              let uu____572 =
                FStar_All.pipe_right args
                  (FStar_List.map FStar_Pervasives_Native.fst) in
              FStar_All.pipe_right uu____572
                (FStar_List.collect head_names_in_term) in
            let repr_names_args =
              FStar_List.collect
                (fun repr ->
                   let uu____611 = FStar_All.pipe_right repr repr_args in
                   FStar_All.pipe_right uu____611 head_names_in_args)
                repr_terms in
            (let uu____641 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____641
             then
               let uu____642 =
                 FStar_List.fold_left
                   (fun s ->
                      fun t ->
                        let uu____648 =
                          let uu____649 = FStar_Syntax_Print.term_to_string t in
                          Prims.op_Hat "; " uu____649 in
                        Prims.op_Hat s uu____648) "" repr_names_args in
               let uu____650 = FStar_Syntax_Print.binders_to_string "; " bs in
               FStar_Util.print2
                 "Checking layered effect combinator binders validity, names: %s, binders: %s\n\n"
                 uu____642 uu____650
             else ());
            (let valid_binder b =
               (FStar_List.existsb
                  (fun t ->
                     let uu____673 =
                       let uu____674 =
                         let uu____675 =
                           FStar_All.pipe_right b FStar_Pervasives_Native.fst in
                         FStar_All.pipe_right uu____675
                           FStar_Syntax_Syntax.bv_to_name in
                       FStar_Syntax_Util.eq_tm uu____674 t in
                     uu____673 = FStar_Syntax_Util.Equal) repr_names_args)
                 ||
                 (match FStar_Pervasives_Native.snd b with
                  | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                      (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                      uu____687)) -> true
                  | uu____690 -> false) in
             let invalid_binders =
               FStar_List.filter
                 (fun b -> Prims.op_Negation (valid_binder b)) bs in
             if (FStar_List.length invalid_binders) <> Prims.int_zero
             then
               (let uu____723 =
                  let uu____728 =
                    let uu____729 =
                      FStar_Syntax_Print.binders_to_string "; "
                        invalid_binders in
                    FStar_Util.format1
                      "Binders %s neither appear as repr indices nor have an associated tactic"
                      uu____729 in
                  (FStar_Errors.Fatal_UnexpectedEffect, uu____728) in
                FStar_Errors.raise_error uu____723 r)
             else ();
             if check_non_informatve_binders
             then
               (let uu____731 =
                  FStar_List.fold_left
                    (fun uu____768 ->
                       fun b ->
                         match uu____768 with
                         | (env1, bs1) ->
                             let env2 =
                               FStar_TypeChecker_Env.push_binders env1 [b] in
                             let uu____831 =
                               FStar_TypeChecker_Normalize.non_info_norm env2
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             if uu____831
                             then (env2, bs1)
                             else (env2, (b :: bs1))) (env, []) bs in
                match uu____731 with
                | (uu____883, informative_binders) ->
                    if
                      (FStar_List.length informative_binders) <>
                        Prims.int_zero
                    then
                      let uu____907 =
                        let uu____912 =
                          let uu____913 =
                            FStar_Syntax_Print.binders_to_string "; "
                              informative_binders in
                          FStar_Util.format1
                            "Binders %s are informative while the effect is reifiable"
                            uu____913 in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____912) in
                      FStar_Errors.raise_error uu____907 r
                    else ())
             else ())
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu____944 =
            let uu____945 =
              FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
            FStar_Util.format1
              "While checking layered effect definition `%s`" uu____945 in
          FStar_Errors.with_ctx uu____944
            (fun uu____974 ->
               (let uu____976 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                    (FStar_Options.Other "LayeredEffectsTc") in
                if uu____976
                then
                  let uu____977 =
                    FStar_Syntax_Print.eff_decl_to_string false ed in
                  FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
                    uu____977
                else ());
               if
                 ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <>
                    Prims.int_zero)
                   ||
                   ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
                      Prims.int_zero)
               then
                 (let uu____986 =
                    let uu____991 =
                      let uu____992 =
                        let uu____993 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        Prims.op_Hat uu____993 ")" in
                      Prims.op_Hat
                        "Binders are not supported for layered effects ("
                        uu____992 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____991) in
                  let uu____994 =
                    FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
                  FStar_Errors.raise_error uu____986 uu____994)
               else ();
               (let log_combinator s uu____1018 =
                  match uu____1018 with
                  | (us, t, ty) ->
                      let uu____1046 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env0)
                          (FStar_Options.Other "LayeredEffectsTc") in
                      if uu____1046
                      then
                        let uu____1047 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____1048 =
                          FStar_Syntax_Print.tscheme_to_string (us, t) in
                        let uu____1053 =
                          FStar_Syntax_Print.tscheme_to_string (us, ty) in
                        FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                          uu____1047 s uu____1048 uu____1053
                      else () in
                let fresh_a_and_u_a a =
                  let uu____1073 = FStar_Syntax_Util.type_u () in
                  FStar_All.pipe_right uu____1073
                    (fun uu____1090 ->
                       match uu____1090 with
                       | (t, u) ->
                           let uu____1101 =
                             let uu____1102 =
                               FStar_Syntax_Syntax.gen_bv a
                                 FStar_Pervasives_Native.None t in
                             FStar_All.pipe_right uu____1102
                               FStar_Syntax_Syntax.mk_binder in
                           (uu____1101, u)) in
                let fresh_x_a x a =
                  let uu____1114 =
                    let uu____1115 =
                      let uu____1116 =
                        FStar_All.pipe_right a FStar_Pervasives_Native.fst in
                      FStar_All.pipe_right uu____1116
                        FStar_Syntax_Syntax.bv_to_name in
                    FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
                      uu____1115 in
                  FStar_All.pipe_right uu____1114
                    FStar_Syntax_Syntax.mk_binder in
                let check_and_gen1 =
                  let uu____1148 =
                    FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                  check_and_gen env0 uu____1148 in
                let signature =
                  let r =
                    (FStar_Pervasives_Native.snd
                       ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                  let uu____1167 =
                    check_and_gen1 "signature" Prims.int_one
                      ed.FStar_Syntax_Syntax.signature in
                  match uu____1167 with
                  | (sig_us, sig_t, sig_ty) ->
                      let uu____1189 =
                        FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
                      (match uu____1189 with
                       | (us, t) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           let uu____1209 = fresh_a_and_u_a "a" in
                           (match uu____1209 with
                            | (a, u) ->
                                let rest_bs =
                                  let uu____1229 =
                                    let uu____1230 =
                                      FStar_All.pipe_right a
                                        FStar_Pervasives_Native.fst in
                                    FStar_All.pipe_right uu____1230
                                      FStar_Syntax_Syntax.bv_to_name in
                                  FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                    env r ed.FStar_Syntax_Syntax.mname
                                    (sig_us, sig_t) u uu____1229 in
                                let bs = a :: rest_bs in
                                let k =
                                  let uu____1261 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Syntax.teff in
                                  FStar_Syntax_Util.arrow bs uu____1261 in
                                let g_eq = FStar_TypeChecker_Rel.teq env t k in
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env g_eq;
                                 (let uu____1266 =
                                    let uu____1269 =
                                      FStar_All.pipe_right k
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env) in
                                    FStar_Syntax_Subst.close_univ_vars us
                                      uu____1269 in
                                  (sig_us, uu____1266, sig_ty))))) in
                log_combinator "signature" signature;
                (let repr =
                   let repr_ts =
                     let uu____1295 =
                       FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                     FStar_All.pipe_right uu____1295 FStar_Util.must in
                   let r =
                     (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
                   let uu____1323 =
                     check_and_gen1 "repr" Prims.int_one repr_ts in
                   match uu____1323 with
                   | (repr_us, repr_t, repr_ty) ->
                       let uu____1345 =
                         FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                       (match uu____1345 with
                        | (us, ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us in
                            let uu____1365 = fresh_a_and_u_a "a" in
                            (match uu____1365 with
                             | (a, u) ->
                                 let rest_bs =
                                   let signature_ts =
                                     let uu____1386 = signature in
                                     match uu____1386 with
                                     | (us1, t, uu____1401) -> (us1, t) in
                                   let uu____1418 =
                                     let uu____1419 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____1419
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                     env r ed.FStar_Syntax_Syntax.mname
                                     signature_ts u uu____1418 in
                                 let bs = a :: rest_bs in
                                 let k =
                                   let uu____1446 =
                                     let uu____1449 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____1449
                                       (fun uu____1462 ->
                                          match uu____1462 with
                                          | (t, u1) ->
                                              let uu____1469 =
                                                let uu____1472 =
                                                  FStar_TypeChecker_Env.new_u_univ
                                                    () in
                                                FStar_Pervasives_Native.Some
                                                  uu____1472 in
                                              FStar_Syntax_Syntax.mk_Total' t
                                                uu____1469) in
                                   FStar_Syntax_Util.arrow bs uu____1446 in
                                 let g = FStar_TypeChecker_Rel.teq env ty k in
                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                    env g;
                                  (let uu____1475 =
                                     let uu____1478 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     FStar_Syntax_Subst.close_univ_vars us
                                       uu____1478 in
                                   (repr_us, repr_t, uu____1475))))) in
                 log_combinator "repr" repr;
                 (let fresh_repr r env u a_tm =
                    let signature_ts =
                      let uu____1512 = signature in
                      match uu____1512 with | (us, t, uu____1527) -> (us, t) in
                    let repr_ts =
                      let uu____1545 = repr in
                      match uu____1545 with | (us, t, uu____1560) -> (us, t) in
                    FStar_TypeChecker_Util.fresh_effect_repr env r
                      ed.FStar_Syntax_Syntax.mname signature_ts
                      (FStar_Pervasives_Native.Some repr_ts) u a_tm in
                  let not_an_arrow_error comb n t r =
                    let uu____1606 =
                      let uu____1611 =
                        let uu____1612 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____1613 = FStar_Util.string_of_int n in
                        let uu____1614 = FStar_Syntax_Print.tag_of_term t in
                        let uu____1615 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.format5
                          "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                          uu____1612 comb uu____1613 uu____1614 uu____1615 in
                      (FStar_Errors.Fatal_UnexpectedEffect, uu____1611) in
                    FStar_Errors.raise_error uu____1606 r in
                  let check_non_informative_binders =
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)
                      &&
                      (let uu____1626 =
                         FStar_Syntax_Util.has_attribute attrs
                           FStar_Parser_Const.allow_informative_binders_attr in
                       Prims.op_Negation uu____1626) in
                  let return_repr =
                    let return_repr_ts =
                      let uu____1645 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_return_repr in
                      FStar_All.pipe_right uu____1645 FStar_Util.must in
                    let r =
                      (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
                    let uu____1657 =
                      check_and_gen1 "return_repr" Prims.int_one
                        return_repr_ts in
                    match uu____1657 with
                    | (ret_us, ret_t, ret_ty) ->
                        let uu____1679 =
                          FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                        (match uu____1679 with
                         | (us, ty) ->
                             let env =
                               FStar_TypeChecker_Env.push_univ_vars env0 us in
                             (check_no_subtyping_for_layered_combinator env
                                ty FStar_Pervasives_Native.None;
                              (let uu____1700 = fresh_a_and_u_a "a" in
                               match uu____1700 with
                               | (a, u_a) ->
                                   let x_a = fresh_x_a "x" a in
                                   let rest_bs =
                                     let uu____1729 =
                                       let uu____1730 =
                                         FStar_Syntax_Subst.compress ty in
                                       uu____1730.FStar_Syntax_Syntax.n in
                                     match uu____1729 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs, uu____1742) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____1769 =
                                           FStar_Syntax_Subst.open_binders bs in
                                         (match uu____1769 with
                                          | (a', uu____1779)::(x',
                                                               uu____1781)::bs1
                                              ->
                                              let uu____1811 =
                                                let uu____1812 =
                                                  let uu____1817 =
                                                    let uu____1820 =
                                                      let uu____1821 =
                                                        let uu____1828 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            (FStar_Pervasives_Native.fst
                                                               a) in
                                                        (a', uu____1828) in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____1821 in
                                                    [uu____1820] in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____1817 in
                                                FStar_All.pipe_right bs1
                                                  uu____1812 in
                                              let uu____1835 =
                                                let uu____1848 =
                                                  let uu____1851 =
                                                    let uu____1852 =
                                                      let uu____1859 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             x_a) in
                                                      (x', uu____1859) in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1852 in
                                                  [uu____1851] in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1848 in
                                              FStar_All.pipe_right uu____1811
                                                uu____1835)
                                     | uu____1874 ->
                                         not_an_arrow_error "return"
                                           (Prims.of_int (2)) ty r in
                                   let bs = a :: x_a :: rest_bs in
                                   let uu____1896 =
                                     let uu____1901 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____1902 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name in
                                     fresh_repr r uu____1901 u_a uu____1902 in
                                   (match uu____1896 with
                                    | (repr1, g) ->
                                        let k =
                                          let uu____1922 =
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr1
                                              (FStar_Pervasives_Native.Some
                                                 u_a) in
                                          FStar_Syntax_Util.arrow bs
                                            uu____1922 in
                                        let g_eq =
                                          FStar_TypeChecker_Rel.teq env ty k in
                                        ((let uu____1927 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g g_eq in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env uu____1927);
                                         (let k1 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env) in
                                          (let uu____1930 =
                                             let uu____1931 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____1931.FStar_Syntax_Syntax.n in
                                           match uu____1930 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs1, c) ->
                                               let uu____1956 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs1 c in
                                               (match uu____1956 with
                                                | (a1::x::bs2, c1) ->
                                                    let res_t =
                                                      FStar_Syntax_Util.comp_result
                                                        c1 in
                                                    let env1 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env [a1; x] in
                                                    validate_layered_effect_binders
                                                      env1 bs2 [res_t]
                                                      check_non_informative_binders
                                                      r));
                                          (let uu____2019 =
                                             FStar_All.pipe_right k1
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us) in
                                           (ret_us, ret_t, uu____2019)))))))) in
                  log_combinator "return_repr" return_repr;
                  (let bind_repr =
                     let bind_repr_ts =
                       let uu____2049 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_bind_repr in
                       FStar_All.pipe_right uu____2049 FStar_Util.must in
                     let r =
                       (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
                     let uu____2061 =
                       check_and_gen1 "bind_repr" (Prims.of_int (2))
                         bind_repr_ts in
                     match uu____2061 with
                     | (bind_us, bind_t, bind_ty) ->
                         let uu____2083 =
                           FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                         (match uu____2083 with
                          | (us, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2104 = fresh_a_and_u_a "a" in
                                match uu____2104 with
                                | (a, u_a) ->
                                    let uu____2123 = fresh_a_and_u_a "b" in
                                    (match uu____2123 with
                                     | (b, u_b) ->
                                         let rest_bs =
                                           let uu____2151 =
                                             let uu____2152 =
                                               FStar_Syntax_Subst.compress ty in
                                             uu____2152.FStar_Syntax_Syntax.n in
                                           match uu____2151 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, uu____2164) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____2191 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs in
                                               (match uu____2191 with
                                                | (a', uu____2201)::(b',
                                                                    uu____2203)::bs1
                                                    ->
                                                    let uu____2233 =
                                                      let uu____2234 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (2)))) in
                                                      FStar_All.pipe_right
                                                        uu____2234
                                                        FStar_Pervasives_Native.fst in
                                                    let uu____2331 =
                                                      let uu____2344 =
                                                        let uu____2347 =
                                                          let uu____2348 =
                                                            let uu____2355 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   a) in
                                                            (a', uu____2355) in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____2348 in
                                                        let uu____2362 =
                                                          let uu____2365 =
                                                            let uu____2366 =
                                                              let uu____2373
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  (FStar_Pervasives_Native.fst
                                                                    b) in
                                                              (b',
                                                                uu____2373) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____2366 in
                                                          [uu____2365] in
                                                        uu____2347 ::
                                                          uu____2362 in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____2344 in
                                                    FStar_All.pipe_right
                                                      uu____2233 uu____2331)
                                           | uu____2388 ->
                                               not_an_arrow_error "bind"
                                                 (Prims.of_int (4)) ty r in
                                         let bs = a :: b :: rest_bs in
                                         let uu____2410 =
                                           let uu____2421 =
                                             let uu____2426 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____2427 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____2426 u_a
                                               uu____2427 in
                                           match uu____2421 with
                                           | (repr1, g) ->
                                               let uu____2442 =
                                                 let uu____2449 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____2449
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____2442, g) in
                                         (match uu____2410 with
                                          | (f, guard_f) ->
                                              let uu____2488 =
                                                let x_a = fresh_x_a "x" a in
                                                let uu____2500 =
                                                  let uu____2505 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [x_a]) in
                                                  let uu____2524 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____2505 u_b
                                                    uu____2524 in
                                                match uu____2500 with
                                                | (repr1, g) ->
                                                    let uu____2539 =
                                                      let uu____2546 =
                                                        let uu____2547 =
                                                          let uu____2548 =
                                                            let uu____2551 =
                                                              let uu____2554
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              FStar_Pervasives_Native.Some
                                                                uu____2554 in
                                                            FStar_Syntax_Syntax.mk_Total'
                                                              repr1
                                                              uu____2551 in
                                                          FStar_Syntax_Util.arrow
                                                            [x_a] uu____2548 in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          uu____2547 in
                                                      FStar_All.pipe_right
                                                        uu____2546
                                                        FStar_Syntax_Syntax.mk_binder in
                                                    (uu____2539, g) in
                                              (match uu____2488 with
                                               | (g, guard_g) ->
                                                   let uu____2605 =
                                                     let uu____2610 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env bs in
                                                     let uu____2611 =
                                                       FStar_All.pipe_right
                                                         (FStar_Pervasives_Native.fst
                                                            b)
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     fresh_repr r uu____2610
                                                       u_b uu____2611 in
                                                   (match uu____2605 with
                                                    | (repr1, guard_repr) ->
                                                        let uu____2628 =
                                                          let uu____2633 =
                                                            FStar_TypeChecker_Env.push_binders
                                                              env bs in
                                                          let uu____2634 =
                                                            let uu____2635 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            FStar_Util.format1
                                                              "implicit for pure_wp in checking bind for %s"
                                                              uu____2635 in
                                                          pure_wp_uvar
                                                            uu____2633 repr1
                                                            uu____2634 r in
                                                        (match uu____2628
                                                         with
                                                         | (pure_wp_uvar1,
                                                            g_pure_wp_uvar)
                                                             ->
                                                             let k =
                                                               let uu____2653
                                                                 =
                                                                 let uu____2656
                                                                   =
                                                                   let uu____2657
                                                                    =
                                                                    let uu____2658
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    [uu____2658] in
                                                                   let uu____2659
                                                                    =
                                                                    let uu____2670
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____2670] in
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2657;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2659;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                   } in
                                                                 FStar_Syntax_Syntax.mk_Comp
                                                                   uu____2656 in
                                                               FStar_Syntax_Util.arrow
                                                                 (FStar_List.append
                                                                    bs 
                                                                    [f; g])
                                                                 uu____2653 in
                                                             let guard_eq =
                                                               FStar_TypeChecker_Rel.teq
                                                                 env ty k in
                                                             (FStar_List.iter
                                                                (FStar_TypeChecker_Rel.force_trivial_guard
                                                                   env)
                                                                [guard_f;
                                                                guard_g;
                                                                guard_repr;
                                                                g_pure_wp_uvar;
                                                                guard_eq];
                                                              (let k1 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env) in
                                                               (let uu____2731
                                                                  =
                                                                  let uu____2732
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    k1 in
                                                                  uu____2732.FStar_Syntax_Syntax.n in
                                                                match uu____2731
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____2757
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____2757
                                                                    with
                                                                    | 
                                                                    (a1::b1::bs2,
                                                                    c1) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                    let uu____2801
                                                                    =
                                                                    let uu____2828
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2828
                                                                    (fun
                                                                    uu____2912
                                                                    ->
                                                                    match uu____2912
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____2993
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____3020
                                                                    =
                                                                    let uu____3027
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____3027
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____2993,
                                                                    uu____3020)) in
                                                                    (match uu____2801
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3142
                                                                    =
                                                                    let uu____3143
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3143.FStar_Syntax_Syntax.n in
                                                                    match uu____3142
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3148,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a1; b1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                               (let uu____3191
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    k1
                                                                    (
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us) in
                                                                (bind_us,
                                                                  bind_t,
                                                                  uu____3191)))))))))))) in
                   log_combinator "bind_repr" bind_repr;
                   (let stronger_repr =
                      let stronger_repr =
                        let ts =
                          let uu____3222 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_stronger_repr in
                          FStar_All.pipe_right uu____3222 FStar_Util.must in
                        let uu____3249 =
                          let uu____3250 =
                            let uu____3253 =
                              FStar_All.pipe_right ts
                                FStar_Pervasives_Native.snd in
                            FStar_All.pipe_right uu____3253
                              FStar_Syntax_Subst.compress in
                          uu____3250.FStar_Syntax_Syntax.n in
                        match uu____3249 with
                        | FStar_Syntax_Syntax.Tm_unknown ->
                            let signature_ts =
                              let uu____3265 = signature in
                              match uu____3265 with
                              | (us, t, uu____3280) -> (us, t) in
                            let uu____3297 =
                              FStar_TypeChecker_Env.inst_tscheme_with
                                signature_ts [FStar_Syntax_Syntax.U_unknown] in
                            (match uu____3297 with
                             | (uu____3306, signature_t) ->
                                 let uu____3308 =
                                   let uu____3309 =
                                     FStar_Syntax_Subst.compress signature_t in
                                   uu____3309.FStar_Syntax_Syntax.n in
                                 (match uu____3308 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____3317) ->
                                      let bs1 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      let repr_t =
                                        let repr_ts =
                                          let uu____3343 = repr in
                                          match uu____3343 with
                                          | (us, t, uu____3358) -> (us, t) in
                                        let uu____3375 =
                                          FStar_TypeChecker_Env.inst_tscheme_with
                                            repr_ts
                                            [FStar_Syntax_Syntax.U_unknown] in
                                        FStar_All.pipe_right uu____3375
                                          FStar_Pervasives_Native.snd in
                                      let repr_t_applied =
                                        let uu____3389 =
                                          let uu____3390 =
                                            let uu____3407 =
                                              let uu____3418 =
                                                let uu____3421 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst) in
                                                FStar_All.pipe_right
                                                  uu____3421
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name) in
                                              FStar_All.pipe_right uu____3418
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg) in
                                            (repr_t, uu____3407) in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____3390 in
                                        FStar_Syntax_Syntax.mk uu____3389
                                          FStar_Range.dummyRange in
                                      let f_b =
                                        FStar_Syntax_Syntax.null_binder
                                          repr_t_applied in
                                      let uu____3471 =
                                        let uu____3472 =
                                          let uu____3475 =
                                            FStar_All.pipe_right f_b
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____3475
                                            FStar_Syntax_Syntax.bv_to_name in
                                        FStar_Syntax_Util.abs
                                          (FStar_List.append bs1 [f_b])
                                          uu____3472
                                          FStar_Pervasives_Native.None in
                                      ([], uu____3471)
                                  | uu____3504 -> failwith "Impossible!"))
                        | uu____3509 -> ts in
                      let r =
                        (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                      let uu____3511 =
                        check_and_gen1 "stronger_repr" Prims.int_one
                          stronger_repr in
                      match uu____3511 with
                      | (stronger_us, stronger_t, stronger_ty) ->
                          ((let uu____3530 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____3530
                            then
                              let uu____3531 =
                                FStar_Syntax_Print.tscheme_to_string
                                  (stronger_us, stronger_t) in
                              let uu____3536 =
                                FStar_Syntax_Print.tscheme_to_string
                                  (stronger_us, stronger_ty) in
                              FStar_Util.print2
                                "stronger combinator typechecked with term: %s and type: %s\n"
                                uu____3531 uu____3536
                            else ());
                           (let uu____3542 =
                              FStar_Syntax_Subst.open_univ_vars stronger_us
                                stronger_ty in
                            match uu____3542 with
                            | (us, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env ty FStar_Pervasives_Native.None;
                                 (let uu____3559 = fresh_a_and_u_a "a" in
                                  match uu____3559 with
                                  | (a, u) ->
                                      let rest_bs =
                                        let uu____3583 =
                                          let uu____3584 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____3584.FStar_Syntax_Syntax.n in
                                        match uu____3583 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____3596) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (2))
                                            ->
                                            let uu____3623 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____3623 with
                                             | (a', uu____3633)::bs1 ->
                                                 let uu____3653 =
                                                   let uu____3654 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             - Prims.int_one)) in
                                                   FStar_All.pipe_right
                                                     uu____3654
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____3751 =
                                                   let uu____3764 =
                                                     let uu____3767 =
                                                       let uu____3768 =
                                                         let uu____3775 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a) in
                                                         (a', uu____3775) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____3768 in
                                                     [uu____3767] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____3764 in
                                                 FStar_All.pipe_right
                                                   uu____3653 uu____3751)
                                        | uu____3790 ->
                                            not_an_arrow_error "stronger"
                                              (Prims.of_int (2)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____3806 =
                                        let uu____3817 =
                                          let uu____3822 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____3823 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____3822 u
                                            uu____3823 in
                                        match uu____3817 with
                                        | (repr1, g) ->
                                            let uu____3838 =
                                              let uu____3845 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____3845
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____3838, g) in
                                      (match uu____3806 with
                                       | (f, guard_f) ->
                                           let uu____3880 =
                                             let uu____3885 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3886 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3885 u
                                               uu____3886 in
                                           (match uu____3880 with
                                            | (ret_t, guard_ret_t) ->
                                                let uu____3899 =
                                                  let uu____3904 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs in
                                                  let uu____3905 =
                                                    let uu____3906 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname in
                                                    FStar_Util.format1
                                                      "implicit for pure_wp in checking stronger for %s"
                                                      uu____3906 in
                                                  pure_wp_uvar uu____3904
                                                    ret_t uu____3905 r in
                                                (match uu____3899 with
                                                 | (pure_wp_uvar1, guard_wp)
                                                     ->
                                                     let c =
                                                       let uu____3918 =
                                                         let uu____3919 =
                                                           let uu____3920 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               () in
                                                           [uu____3920] in
                                                         let uu____3921 =
                                                           let uu____3932 =
                                                             FStar_All.pipe_right
                                                               pure_wp_uvar1
                                                               FStar_Syntax_Syntax.as_arg in
                                                           [uu____3932] in
                                                         {
                                                           FStar_Syntax_Syntax.comp_univs
                                                             = uu____3919;
                                                           FStar_Syntax_Syntax.effect_name
                                                             =
                                                             FStar_Parser_Const.effect_PURE_lid;
                                                           FStar_Syntax_Syntax.result_typ
                                                             = ret_t;
                                                           FStar_Syntax_Syntax.effect_args
                                                             = uu____3921;
                                                           FStar_Syntax_Syntax.flags
                                                             = []
                                                         } in
                                                       FStar_Syntax_Syntax.mk_Comp
                                                         uu____3918 in
                                                     let k =
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f]) c in
                                                     ((let uu____3987 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffectsTc") in
                                                       if uu____3987
                                                       then
                                                         let uu____3988 =
                                                           FStar_Syntax_Print.term_to_string
                                                             k in
                                                         FStar_Util.print1
                                                           "Expected type of subcomp before unification: %s\n"
                                                           uu____3988
                                                       else ());
                                                      (let guard_eq =
                                                         FStar_TypeChecker_Rel.teq
                                                           env ty k in
                                                       FStar_List.iter
                                                         (FStar_TypeChecker_Rel.force_trivial_guard
                                                            env)
                                                         [guard_f;
                                                         guard_ret_t;
                                                         guard_wp;
                                                         guard_eq];
                                                       (let k1 =
                                                          let uu____3993 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          FStar_All.pipe_right
                                                            uu____3993
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env) in
                                                        (let uu____3995 =
                                                           let uu____3996 =
                                                             FStar_Syntax_Subst.compress
                                                               k1 in
                                                           uu____3996.FStar_Syntax_Syntax.n in
                                                         match uu____3995
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (bs1, c1) ->
                                                             let uu____4021 =
                                                               FStar_Syntax_Subst.open_comp
                                                                 bs1 c1 in
                                                             (match uu____4021
                                                              with
                                                              | (a1::bs2, c2)
                                                                  ->
                                                                  let res_t =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                  let uu____4052
                                                                    =
                                                                    let uu____4071
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____4071
                                                                    (fun
                                                                    uu____4146
                                                                    ->
                                                                    match uu____4146
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4219
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4219)) in
                                                                  (match uu____4052
                                                                   with
                                                                   | 
                                                                   (bs3, f_b)
                                                                    ->
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                        (let uu____4291 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                stronger_us) in
                                                         (stronger_us,
                                                           stronger_t,
                                                           uu____4291)))))))))))) in
                    log_combinator "stronger_repr" stronger_repr;
                    (let if_then_else =
                       let if_then_else_ts =
                         let ts =
                           let uu____4314 =
                             FStar_All.pipe_right ed
                               FStar_Syntax_Util.get_layered_if_then_else_combinator in
                           FStar_All.pipe_right uu____4314 FStar_Util.must in
                         let uu____4325 =
                           let uu____4326 =
                             let uu____4329 =
                               FStar_All.pipe_right ts
                                 FStar_Pervasives_Native.snd in
                             FStar_All.pipe_right uu____4329
                               FStar_Syntax_Subst.compress in
                           uu____4326.FStar_Syntax_Syntax.n in
                         match uu____4325 with
                         | FStar_Syntax_Syntax.Tm_unknown ->
                             let signature_ts =
                               let uu____4341 = signature in
                               match uu____4341 with
                               | (us, t, uu____4356) -> (us, t) in
                             let uu____4373 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 signature_ts [FStar_Syntax_Syntax.U_unknown] in
                             (match uu____4373 with
                              | (uu____4382, signature_t) ->
                                  let uu____4384 =
                                    let uu____4385 =
                                      FStar_Syntax_Subst.compress signature_t in
                                    uu____4385.FStar_Syntax_Syntax.n in
                                  (match uu____4384 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____4393) ->
                                       let bs1 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       let repr_t =
                                         let repr_ts =
                                           let uu____4419 = repr in
                                           match uu____4419 with
                                           | (us, t, uu____4434) -> (us, t) in
                                         let uu____4451 =
                                           FStar_TypeChecker_Env.inst_tscheme_with
                                             repr_ts
                                             [FStar_Syntax_Syntax.U_unknown] in
                                         FStar_All.pipe_right uu____4451
                                           FStar_Pervasives_Native.snd in
                                       let repr_t_applied =
                                         let uu____4465 =
                                           let uu____4466 =
                                             let uu____4483 =
                                               let uu____4494 =
                                                 let uu____4497 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst) in
                                                 FStar_All.pipe_right
                                                   uu____4497
                                                   (FStar_List.map
                                                      FStar_Syntax_Syntax.bv_to_name) in
                                               FStar_All.pipe_right
                                                 uu____4494
                                                 (FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg) in
                                             (repr_t, uu____4483) in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____4466 in
                                         FStar_Syntax_Syntax.mk uu____4465
                                           FStar_Range.dummyRange in
                                       let f_b =
                                         FStar_Syntax_Syntax.null_binder
                                           repr_t_applied in
                                       let g_b =
                                         FStar_Syntax_Syntax.null_binder
                                           repr_t_applied in
                                       let b_b =
                                         FStar_Syntax_Syntax.null_binder
                                           FStar_Syntax_Util.t_bool in
                                       let uu____4549 =
                                         FStar_Syntax_Util.abs
                                           (FStar_List.append bs1
                                              [f_b; g_b; b_b]) repr_t_applied
                                           FStar_Pervasives_Native.None in
                                       ([], uu____4549)
                                   | uu____4580 -> failwith "Impossible!"))
                         | uu____4585 -> ts in
                       let r =
                         (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                       let uu____4589 =
                         check_and_gen1 "if_then_else" Prims.int_one
                           if_then_else_ts in
                       match uu____4589 with
                       | (if_then_else_us, if_then_else_t, if_then_else_ty)
                           ->
                           let uu____4607 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_t in
                           (match uu____4607 with
                            | (us, t) ->
                                let uu____4622 =
                                  FStar_Syntax_Subst.open_univ_vars
                                    if_then_else_us if_then_else_ty in
                                (match uu____4622 with
                                 | (uu____4635, ty) ->
                                     let env =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     (check_no_subtyping_for_layered_combinator
                                        env t
                                        (FStar_Pervasives_Native.Some ty);
                                      (let uu____4639 = fresh_a_and_u_a "a" in
                                       match uu____4639 with
                                       | (a, u_a) ->
                                           let rest_bs =
                                             let uu____4663 =
                                               let uu____4664 =
                                                 FStar_Syntax_Subst.compress
                                                   ty in
                                               uu____4664.FStar_Syntax_Syntax.n in
                                             match uu____4663 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, uu____4676) when
                                                 (FStar_List.length bs) >=
                                                   (Prims.of_int (4))
                                                 ->
                                                 let uu____4703 =
                                                   FStar_Syntax_Subst.open_binders
                                                     bs in
                                                 (match uu____4703 with
                                                  | (a', uu____4713)::bs1 ->
                                                      let uu____4733 =
                                                        let uu____4734 =
                                                          FStar_All.pipe_right
                                                            bs1
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs1)
                                                                  -
                                                                  (Prims.of_int (3)))) in
                                                        FStar_All.pipe_right
                                                          uu____4734
                                                          FStar_Pervasives_Native.fst in
                                                      let uu____4831 =
                                                        let uu____4844 =
                                                          let uu____4847 =
                                                            let uu____4848 =
                                                              let uu____4855
                                                                =
                                                                let uu____4858
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    a
                                                                    FStar_Pervasives_Native.fst in
                                                                FStar_All.pipe_right
                                                                  uu____4858
                                                                  FStar_Syntax_Syntax.bv_to_name in
                                                              (a',
                                                                uu____4855) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____4848 in
                                                          [uu____4847] in
                                                        FStar_Syntax_Subst.subst_binders
                                                          uu____4844 in
                                                      FStar_All.pipe_right
                                                        uu____4733 uu____4831)
                                             | uu____4879 ->
                                                 not_an_arrow_error
                                                   "if_then_else"
                                                   (Prims.of_int (4)) ty r in
                                           let bs = a :: rest_bs in
                                           let uu____4895 =
                                             let uu____4906 =
                                               let uu____4911 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____4912 =
                                                 let uu____4913 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____4913
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____4911 u_a
                                                 uu____4912 in
                                             match uu____4906 with
                                             | (repr1, g) ->
                                                 let uu____4934 =
                                                   let uu____4941 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "f"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____4941
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____4934, g) in
                                           (match uu____4895 with
                                            | (f_bs, guard_f) ->
                                                let uu____4976 =
                                                  let uu____4987 =
                                                    let uu____4992 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env bs in
                                                    let uu____4993 =
                                                      let uu____4994 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_All.pipe_right
                                                        uu____4994
                                                        FStar_Syntax_Syntax.bv_to_name in
                                                    fresh_repr r uu____4992
                                                      u_a uu____4993 in
                                                  match uu____4987 with
                                                  | (repr1, g) ->
                                                      let uu____5015 =
                                                        let uu____5022 =
                                                          FStar_Syntax_Syntax.gen_bv
                                                            "g"
                                                            FStar_Pervasives_Native.None
                                                            repr1 in
                                                        FStar_All.pipe_right
                                                          uu____5022
                                                          FStar_Syntax_Syntax.mk_binder in
                                                      (uu____5015, g) in
                                                (match uu____4976 with
                                                 | (g_bs, guard_g) ->
                                                     let p_b =
                                                       let uu____5064 =
                                                         FStar_Syntax_Syntax.gen_bv
                                                           "p"
                                                           FStar_Pervasives_Native.None
                                                           FStar_Syntax_Util.t_bool in
                                                       FStar_All.pipe_right
                                                         uu____5064
                                                         FStar_Syntax_Syntax.mk_binder in
                                                     let uu____5071 =
                                                       let uu____5076 =
                                                         FStar_TypeChecker_Env.push_binders
                                                           env
                                                           (FStar_List.append
                                                              bs [p_b]) in
                                                       let uu____5095 =
                                                         let uu____5096 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____5096
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       fresh_repr r
                                                         uu____5076 u_a
                                                         uu____5095 in
                                                     (match uu____5071 with
                                                      | (t_body, guard_body)
                                                          ->
                                                          let k =
                                                            FStar_Syntax_Util.abs
                                                              (FStar_List.append
                                                                 bs
                                                                 [f_bs;
                                                                 g_bs;
                                                                 p_b]) t_body
                                                              FStar_Pervasives_Native.None in
                                                          let guard_eq =
                                                            FStar_TypeChecker_Rel.teq
                                                              env t k in
                                                          (FStar_All.pipe_right
                                                             [guard_f;
                                                             guard_g;
                                                             guard_body;
                                                             guard_eq]
                                                             (FStar_List.iter
                                                                (FStar_TypeChecker_Rel.force_trivial_guard
                                                                   env));
                                                           (let k1 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env) in
                                                            (let uu____5154 =
                                                               let uu____5155
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   k1 in
                                                               uu____5155.FStar_Syntax_Syntax.n in
                                                             match uu____5154
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_abs
                                                                 (bs1, body,
                                                                  uu____5160)
                                                                 ->
                                                                 let uu____5185
                                                                   =
                                                                   FStar_Syntax_Subst.open_term
                                                                    bs1 body in
                                                                 (match uu____5185
                                                                  with
                                                                  | (a1::bs2,
                                                                    body1) ->
                                                                    let uu____5213
                                                                    =
                                                                    let uu____5240
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____5240
                                                                    (fun
                                                                    uu____5324
                                                                    ->
                                                                    match uu____5324
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5405
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5432
                                                                    =
                                                                    let uu____5439
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5439
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5405,
                                                                    uu____5432)) in
                                                                    (match uu____5213
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort;
                                                                    body1]
                                                                    check_non_informative_binders
                                                                    r)));
                                                            (let uu____5570 =
                                                               FStar_All.pipe_right
                                                                 k1
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    if_then_else_us) in
                                                             (if_then_else_us,
                                                               uu____5570,
                                                               if_then_else_ty))))))))))) in
                     log_combinator "if_then_else" if_then_else;
                     FStar_Errors.with_ctx
                       "While checking if-then-else soundness"
                       (fun uu____5600 ->
                          let r =
                            let uu____5602 =
                              let uu____5605 =
                                let uu____5614 =
                                  FStar_All.pipe_right ed
                                    FStar_Syntax_Util.get_layered_if_then_else_combinator in
                                FStar_All.pipe_right uu____5614
                                  FStar_Util.must in
                              FStar_All.pipe_right uu____5605
                                FStar_Pervasives_Native.snd in
                            uu____5602.FStar_Syntax_Syntax.pos in
                          let binder_aq_to_arg_aq aq =
                            match aq with
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Implicit uu____5657) ->
                                aq
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Meta uu____5658) ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit false)
                            | uu____5659 -> FStar_Pervasives_Native.None in
                          let uu____5662 = if_then_else in
                          match uu____5662 with
                          | (ite_us, ite_t, uu____5673) ->
                              let uu____5678 =
                                FStar_Syntax_Subst.open_univ_vars ite_us
                                  ite_t in
                              (match uu____5678 with
                               | (us, ite_t1) ->
                                   let uu____5685 =
                                     let uu____5702 =
                                       let uu____5703 =
                                         FStar_Syntax_Subst.compress ite_t1 in
                                       uu____5703.FStar_Syntax_Syntax.n in
                                     match uu____5702 with
                                     | FStar_Syntax_Syntax.Tm_abs
                                         (bs, uu____5723, uu____5724) ->
                                         let bs1 =
                                           FStar_Syntax_Subst.open_binders bs in
                                         let uu____5750 =
                                           let uu____5763 =
                                             let uu____5768 =
                                               let uu____5771 =
                                                 let uu____5780 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____5780
                                                   FStar_Pervasives_Native.snd in
                                               FStar_All.pipe_right
                                                 uu____5771
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____5768
                                               (FStar_List.map
                                                  FStar_Syntax_Syntax.bv_to_name) in
                                           FStar_All.pipe_right uu____5763
                                             (fun l ->
                                                let uu____5935 = l in
                                                match uu____5935 with
                                                | f::g::p::[] -> (f, g, p)) in
                                         (match uu____5750 with
                                          | (f, g, p) ->
                                              let uu____6006 =
                                                let uu____6007 =
                                                  FStar_TypeChecker_Env.push_univ_vars
                                                    env0 us in
                                                FStar_TypeChecker_Env.push_binders
                                                  uu____6007 bs1 in
                                              let uu____6008 =
                                                let uu____6009 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       (fun uu____6034 ->
                                                          match uu____6034
                                                          with
                                                          | (b, qual) ->
                                                              let uu____6053
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b in
                                                              (uu____6053,
                                                                (binder_aq_to_arg_aq
                                                                   qual)))) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  ite_t1 uu____6009 r in
                                              (uu____6006, uu____6008, f, g,
                                                p))
                                     | uu____6062 ->
                                         failwith
                                           "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                                   (match uu____5685 with
                                    | (env, ite_t_applied, f_t, g_t, p_t) ->
                                        let uu____6096 =
                                          let uu____6105 = stronger_repr in
                                          match uu____6105 with
                                          | (uu____6122, subcomp_t,
                                             subcomp_ty) ->
                                              let uu____6129 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  us subcomp_t in
                                              (match uu____6129 with
                                               | (uu____6142, subcomp_t1) ->
                                                   let uu____6144 =
                                                     let uu____6155 =
                                                       FStar_Syntax_Subst.open_univ_vars
                                                         us subcomp_ty in
                                                     match uu____6155 with
                                                     | (uu____6170,
                                                        subcomp_ty1) ->
                                                         let uu____6172 =
                                                           let uu____6173 =
                                                             FStar_Syntax_Subst.compress
                                                               subcomp_ty1 in
                                                           uu____6173.FStar_Syntax_Syntax.n in
                                                         (match uu____6172
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,
                                                               uu____6187)
                                                              ->
                                                              let uu____6208
                                                                =
                                                                FStar_All.pipe_right
                                                                  bs
                                                                  (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    Prims.int_one)) in
                                                              (match uu____6208
                                                               with
                                                               | (bs_except_last,
                                                                  last_b) ->
                                                                   let uu____6313
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    bs_except_last
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.snd) in
                                                                   let uu____6340
                                                                    =
                                                                    let uu____6343
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    last_b
                                                                    FStar_List.hd in
                                                                    FStar_All.pipe_right
                                                                    uu____6343
                                                                    FStar_Pervasives_Native.snd in
                                                                   (uu____6313,
                                                                    uu____6340))
                                                          | uu____6386 ->
                                                              failwith
                                                                "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                                   (match uu____6144 with
                                                    | (aqs_except_last,
                                                       last_aq) ->
                                                        let uu____6419 =
                                                          let uu____6430 =
                                                            FStar_All.pipe_right
                                                              aqs_except_last
                                                              (FStar_List.map
                                                                 binder_aq_to_arg_aq) in
                                                          let uu____6447 =
                                                            FStar_All.pipe_right
                                                              last_aq
                                                              binder_aq_to_arg_aq in
                                                          (uu____6430,
                                                            uu____6447) in
                                                        (match uu____6419
                                                         with
                                                         | (aqs_except_last1,
                                                            last_aq1) ->
                                                             let aux t =
                                                               let tun_args =
                                                                 FStar_All.pipe_right
                                                                   aqs_except_last1
                                                                   (FStar_List.map
                                                                    (fun aq
                                                                    ->
                                                                    (FStar_Syntax_Syntax.tun,
                                                                    aq))) in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 subcomp_t1
                                                                 (FStar_List.append
                                                                    tun_args
                                                                    [
                                                                    (t,
                                                                    last_aq1)])
                                                                 r in
                                                             let uu____6559 =
                                                               aux f_t in
                                                             let uu____6562 =
                                                               aux g_t in
                                                             (uu____6559,
                                                               uu____6562)))) in
                                        (match uu____6096 with
                                         | (subcomp_f, subcomp_g) ->
                                             let uu____6579 =
                                               let aux t =
                                                 let uu____6596 =
                                                   let uu____6597 =
                                                     let uu____6624 =
                                                       let uu____6641 =
                                                         let uu____6650 =
                                                           FStar_Syntax_Syntax.mk_Total
                                                             ite_t_applied in
                                                         FStar_Util.Inr
                                                           uu____6650 in
                                                       (uu____6641,
                                                         FStar_Pervasives_Native.None) in
                                                     (t, uu____6624,
                                                       FStar_Pervasives_Native.None) in
                                                   FStar_Syntax_Syntax.Tm_ascribed
                                                     uu____6597 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6596 r in
                                               let uu____6691 = aux subcomp_f in
                                               let uu____6692 = aux subcomp_g in
                                               (uu____6691, uu____6692) in
                                             (match uu____6579 with
                                              | (tm_subcomp_ascribed_f,
                                                 tm_subcomp_ascribed_g) ->
                                                  ((let uu____6696 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffectsTc") in
                                                    if uu____6696
                                                    then
                                                      let uu____6697 =
                                                        FStar_Syntax_Print.term_to_string
                                                          tm_subcomp_ascribed_f in
                                                      let uu____6698 =
                                                        FStar_Syntax_Print.term_to_string
                                                          tm_subcomp_ascribed_g in
                                                      FStar_Util.print2
                                                        "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                        uu____6697 uu____6698
                                                    else ());
                                                   (let env1 =
                                                      let uu____6702 =
                                                        let uu____6703 =
                                                          let uu____6704 =
                                                            FStar_All.pipe_right
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            uu____6704 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          uu____6703 in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu____6702 in
                                                    let uu____6707 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env1
                                                        tm_subcomp_ascribed_f in
                                                    match uu____6707 with
                                                    | (uu____6714,
                                                       uu____6715, g_f) ->
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1 g_f);
                                                   (let not_p =
                                                      let uu____6719 =
                                                        let uu____6720 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            FStar_Parser_Const.not_lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None in
                                                        FStar_All.pipe_right
                                                          uu____6720
                                                          FStar_Syntax_Syntax.fv_to_tm in
                                                      let uu____6721 =
                                                        let uu____6722 =
                                                          let uu____6731 =
                                                            FStar_All.pipe_right
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_All.pipe_right
                                                            uu____6731
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____6722] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____6719 uu____6721
                                                        r in
                                                    let env1 =
                                                      let uu____6759 =
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          not_p in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu____6759 in
                                                    let uu____6760 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env1
                                                        tm_subcomp_ascribed_g in
                                                    match uu____6760 with
                                                    | (uu____6767,
                                                       uu____6768, g_g) ->
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1 g_g)))))));
                     (let tc_action env act =
                        let env01 = env in
                        let r =
                          (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                        if
                          (FStar_List.length
                             act.FStar_Syntax_Syntax.action_params)
                            <> Prims.int_zero
                        then
                          (let uu____6790 =
                             let uu____6795 =
                               let uu____6796 =
                                 FStar_Ident.string_of_lid
                                   ed.FStar_Syntax_Syntax.mname in
                               let uu____6797 =
                                 FStar_Ident.string_of_lid
                                   act.FStar_Syntax_Syntax.action_name in
                               let uu____6798 =
                                 FStar_Syntax_Print.binders_to_string "; "
                                   act.FStar_Syntax_Syntax.action_params in
                               FStar_Util.format3
                                 "Action %s:%s has non-empty action params (%s)"
                                 uu____6796 uu____6797 uu____6798 in
                             (FStar_Errors.Fatal_MalformedActionDeclaration,
                               uu____6795) in
                           FStar_Errors.raise_error uu____6790 r)
                        else ();
                        (let uu____6800 =
                           let uu____6805 =
                             FStar_Syntax_Subst.univ_var_opening
                               act.FStar_Syntax_Syntax.action_univs in
                           match uu____6805 with
                           | (usubst, us) ->
                               let uu____6828 =
                                 FStar_TypeChecker_Env.push_univ_vars env us in
                               let uu____6829 =
                                 let uu___653_6830 = act in
                                 let uu____6831 =
                                   FStar_Syntax_Subst.subst usubst
                                     act.FStar_Syntax_Syntax.action_defn in
                                 let uu____6832 =
                                   FStar_Syntax_Subst.subst usubst
                                     act.FStar_Syntax_Syntax.action_typ in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___653_6830.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___653_6830.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs = us;
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___653_6830.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____6831;
                                   FStar_Syntax_Syntax.action_typ =
                                     uu____6832
                                 } in
                               (uu____6828, uu____6829) in
                         match uu____6800 with
                         | (env1, act1) ->
                             let act_typ =
                               let uu____6836 =
                                 let uu____6837 =
                                   FStar_Syntax_Subst.compress
                                     act1.FStar_Syntax_Syntax.action_typ in
                                 uu____6837.FStar_Syntax_Syntax.n in
                               match uu____6836 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                                   let ct =
                                     FStar_Syntax_Util.comp_to_comp_typ c in
                                   let uu____6863 =
                                     FStar_Ident.lid_equals
                                       ct.FStar_Syntax_Syntax.effect_name
                                       ed.FStar_Syntax_Syntax.mname in
                                   if uu____6863
                                   then
                                     let repr_ts =
                                       let uu____6865 = repr in
                                       match uu____6865 with
                                       | (us, t, uu____6880) -> (us, t) in
                                     let repr1 =
                                       let uu____6898 =
                                         FStar_TypeChecker_Env.inst_tscheme_with
                                           repr_ts
                                           ct.FStar_Syntax_Syntax.comp_univs in
                                       FStar_All.pipe_right uu____6898
                                         FStar_Pervasives_Native.snd in
                                     let repr2 =
                                       let uu____6908 =
                                         let uu____6909 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ in
                                         uu____6909 ::
                                           (ct.FStar_Syntax_Syntax.effect_args) in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____6908 r in
                                     let c1 =
                                       let uu____6927 =
                                         let uu____6930 =
                                           FStar_TypeChecker_Env.new_u_univ
                                             () in
                                         FStar_Pervasives_Native.Some
                                           uu____6930 in
                                       FStar_Syntax_Syntax.mk_Total' repr2
                                         uu____6927 in
                                     FStar_Syntax_Util.arrow bs c1
                                   else act1.FStar_Syntax_Syntax.action_typ
                               | uu____6932 ->
                                   act1.FStar_Syntax_Syntax.action_typ in
                             let uu____6933 =
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 env1 act_typ in
                             (match uu____6933 with
                              | (act_typ1, uu____6941, g_t) ->
                                  let uu____6943 =
                                    let uu____6950 =
                                      let uu___678_6951 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env1 act_typ1 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___678_6951.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___678_6951.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___678_6951.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___678_6951.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___678_6951.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___678_6951.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___678_6951.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___678_6951.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___678_6951.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___678_6951.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          = false;
                                        FStar_TypeChecker_Env.effects =
                                          (uu___678_6951.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___678_6951.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___678_6951.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___678_6951.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___678_6951.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___678_6951.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___678_6951.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___678_6951.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___678_6951.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___678_6951.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___678_6951.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___678_6951.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___678_6951.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___678_6951.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___678_6951.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___678_6951.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___678_6951.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___678_6951.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___678_6951.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___678_6951.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___678_6951.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___678_6951.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___678_6951.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___678_6951.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___678_6951.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___678_6951.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___678_6951.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___678_6951.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                      uu____6950
                                      act1.FStar_Syntax_Syntax.action_defn in
                                  (match uu____6943 with
                                   | (act_defn, uu____6953, g_d) ->
                                       ((let uu____6956 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____6956
                                         then
                                           let uu____6957 =
                                             FStar_Syntax_Print.term_to_string
                                               act_defn in
                                           let uu____6958 =
                                             FStar_Syntax_Print.term_to_string
                                               act_typ1 in
                                           FStar_Util.print2
                                             "Typechecked action definition: %s and action type: %s\n"
                                             uu____6957 uu____6958
                                         else ());
                                        (let uu____6960 =
                                           let act_typ2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 act_typ1 in
                                           let uu____6968 =
                                             let uu____6969 =
                                               FStar_Syntax_Subst.compress
                                                 act_typ2 in
                                             uu____6969.FStar_Syntax_Syntax.n in
                                           match uu____6968 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, uu____6979) ->
                                               let bs1 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs in
                                               let env2 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env1 bs1 in
                                               let uu____7002 =
                                                 FStar_Syntax_Util.type_u () in
                                               (match uu____7002 with
                                                | (t, u) ->
                                                    let reason =
                                                      let uu____7016 =
                                                        FStar_Ident.string_of_lid
                                                          ed.FStar_Syntax_Syntax.mname in
                                                      let uu____7017 =
                                                        FStar_Ident.string_of_lid
                                                          act1.FStar_Syntax_Syntax.action_name in
                                                      FStar_Util.format2
                                                        "implicit for return type of action %s:%s"
                                                        uu____7016 uu____7017 in
                                                    let uu____7018 =
                                                      FStar_TypeChecker_Util.new_implicit_var
                                                        reason r env2 t in
                                                    (match uu____7018 with
                                                     | (a_tm, uu____7038,
                                                        g_tm) ->
                                                         let uu____7052 =
                                                           fresh_repr r env2
                                                             u a_tm in
                                                         (match uu____7052
                                                          with
                                                          | (repr1, g) ->
                                                              let uu____7065
                                                                =
                                                                let uu____7068
                                                                  =
                                                                  let uu____7071
                                                                    =
                                                                    let uu____7074
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    FStar_All.pipe_right
                                                                    uu____7074
                                                                    (fun
                                                                    uu____7077
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7077) in
                                                                  FStar_Syntax_Syntax.mk_Total'
                                                                    repr1
                                                                    uu____7071 in
                                                                FStar_Syntax_Util.arrow
                                                                  bs1
                                                                  uu____7068 in
                                                              let uu____7078
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g g_tm in
                                                              (uu____7065,
                                                                uu____7078))))
                                           | uu____7081 ->
                                               let uu____7082 =
                                                 let uu____7087 =
                                                   let uu____7088 =
                                                     FStar_Ident.string_of_lid
                                                       ed.FStar_Syntax_Syntax.mname in
                                                   let uu____7089 =
                                                     FStar_Ident.string_of_lid
                                                       act1.FStar_Syntax_Syntax.action_name in
                                                   let uu____7090 =
                                                     FStar_Syntax_Print.term_to_string
                                                       act_typ2 in
                                                   FStar_Util.format3
                                                     "Unexpected non-function type for action %s:%s (%s)"
                                                     uu____7088 uu____7089
                                                     uu____7090 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____7087) in
                                               FStar_Errors.raise_error
                                                 uu____7082 r in
                                         match uu____6960 with
                                         | (k, g_k) ->
                                             ((let uu____7104 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffectsTc") in
                                               if uu____7104
                                               then
                                                 let uu____7105 =
                                                   FStar_Syntax_Print.term_to_string
                                                     k in
                                                 FStar_Util.print1
                                                   "Expected action type: %s\n"
                                                   uu____7105
                                               else ());
                                              (let g =
                                                 FStar_TypeChecker_Rel.teq
                                                   env1 act_typ1 k in
                                               FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1) [g_t; g_d; g_k; g];
                                               (let uu____7110 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env1)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____7110
                                                then
                                                  let uu____7111 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected action type after unification: %s\n"
                                                    uu____7111
                                                else ());
                                               (let act_typ2 =
                                                  let err_msg t =
                                                    let uu____7120 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname in
                                                    let uu____7121 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name in
                                                    let uu____7122 =
                                                      FStar_Syntax_Print.term_to_string
                                                        t in
                                                    FStar_Util.format3
                                                      "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                      uu____7120 uu____7121
                                                      uu____7122 in
                                                  let repr_args t =
                                                    let uu____7141 =
                                                      let uu____7142 =
                                                        FStar_Syntax_Subst.compress
                                                          t in
                                                      uu____7142.FStar_Syntax_Syntax.n in
                                                    match uu____7141 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (head, a::is) ->
                                                        let uu____7194 =
                                                          let uu____7195 =
                                                            FStar_Syntax_Subst.compress
                                                              head in
                                                          uu____7195.FStar_Syntax_Syntax.n in
                                                        (match uu____7194
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uinst
                                                             (uu____7204, us)
                                                             ->
                                                             (us,
                                                               (FStar_Pervasives_Native.fst
                                                                  a), is)
                                                         | uu____7214 ->
                                                             let uu____7215 =
                                                               let uu____7220
                                                                 = err_msg t in
                                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                 uu____7220) in
                                                             FStar_Errors.raise_error
                                                               uu____7215 r)
                                                    | uu____7227 ->
                                                        let uu____7228 =
                                                          let uu____7233 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7233) in
                                                        FStar_Errors.raise_error
                                                          uu____7228 r in
                                                  let k1 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env1 k in
                                                  let uu____7241 =
                                                    let uu____7242 =
                                                      FStar_Syntax_Subst.compress
                                                        k1 in
                                                    uu____7242.FStar_Syntax_Syntax.n in
                                                  match uu____7241 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs, c) ->
                                                      let uu____7267 =
                                                        FStar_Syntax_Subst.open_comp
                                                          bs c in
                                                      (match uu____7267 with
                                                       | (bs1, c1) ->
                                                           let uu____7274 =
                                                             repr_args
                                                               (FStar_Syntax_Util.comp_result
                                                                  c1) in
                                                           (match uu____7274
                                                            with
                                                            | (us, a, is) ->
                                                                let ct =
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                  } in
                                                                let uu____7285
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Comp
                                                                    ct in
                                                                FStar_Syntax_Util.arrow
                                                                  bs1
                                                                  uu____7285))
                                                  | uu____7288 ->
                                                      let uu____7289 =
                                                        let uu____7294 =
                                                          err_msg k1 in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____7294) in
                                                      FStar_Errors.raise_error
                                                        uu____7289 r in
                                                (let uu____7296 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "LayeredEffectsTc") in
                                                 if uu____7296
                                                 then
                                                   let uu____7297 =
                                                     FStar_Syntax_Print.term_to_string
                                                       act_typ2 in
                                                   FStar_Util.print1
                                                     "Action type after injecting it into the monad: %s\n"
                                                     uu____7297
                                                 else ());
                                                (let act2 =
                                                   let uu____7300 =
                                                     FStar_TypeChecker_Generalize.generalize_universes
                                                       env1 act_defn in
                                                   match uu____7300 with
                                                   | (us, act_defn1) ->
                                                       if
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                           = []
                                                       then
                                                         let uu___751_7313 =
                                                           act1 in
                                                         let uu____7314 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us act_typ2 in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___751_7313.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___751_7313.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = us;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___751_7313.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = act_defn1;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____7314
                                                         }
                                                       else
                                                         (let uu____7316 =
                                                            ((FStar_List.length
                                                                us)
                                                               =
                                                               (FStar_List.length
                                                                  act1.FStar_Syntax_Syntax.action_univs))
                                                              &&
                                                              (FStar_List.forall2
                                                                 (fun u1 ->
                                                                    fun u2 ->
                                                                    let uu____7322
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                    uu____7322
                                                                    =
                                                                    Prims.int_zero)
                                                                 us
                                                                 act1.FStar_Syntax_Syntax.action_univs) in
                                                          if uu____7316
                                                          then
                                                            let uu___756_7323
                                                              = act1 in
                                                            let uu____7324 =
                                                              FStar_Syntax_Subst.close_univ_vars
                                                                act1.FStar_Syntax_Syntax.action_univs
                                                                act_typ2 in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___756_7323.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___756_7323.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                =
                                                                (uu___756_7323.FStar_Syntax_Syntax.action_univs);
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___756_7323.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = act_defn1;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____7324
                                                            }
                                                          else
                                                            (let uu____7326 =
                                                               let uu____7331
                                                                 =
                                                                 let uu____7332
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname in
                                                                 let uu____7333
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                 let uu____7334
                                                                   =
                                                                   FStar_Syntax_Print.univ_names_to_string
                                                                    us in
                                                                 let uu____7335
                                                                   =
                                                                   FStar_Syntax_Print.univ_names_to_string
                                                                    act1.FStar_Syntax_Syntax.action_univs in
                                                                 FStar_Util.format4
                                                                   "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                   uu____7332
                                                                   uu____7333
                                                                   uu____7334
                                                                   uu____7335 in
                                                               (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                                 uu____7331) in
                                                             FStar_Errors.raise_error
                                                               uu____7326 r)) in
                                                 act2))))))))) in
                      let tschemes_of uu____7357 =
                        match uu____7357 with
                        | (us, t, ty) -> ((us, t), (us, ty)) in
                      let combinators =
                        let uu____7402 =
                          let uu____7403 = tschemes_of repr in
                          let uu____7408 = tschemes_of return_repr in
                          let uu____7413 = tschemes_of bind_repr in
                          let uu____7418 = tschemes_of stronger_repr in
                          let uu____7423 = tschemes_of if_then_else in
                          {
                            FStar_Syntax_Syntax.l_repr = uu____7403;
                            FStar_Syntax_Syntax.l_return = uu____7408;
                            FStar_Syntax_Syntax.l_bind = uu____7413;
                            FStar_Syntax_Syntax.l_subcomp = uu____7418;
                            FStar_Syntax_Syntax.l_if_then_else = uu____7423
                          } in
                        FStar_Syntax_Syntax.Layered_eff uu____7402 in
                      let uu___765_7428 = ed in
                      let uu____7429 =
                        FStar_List.map (tc_action env0)
                          ed.FStar_Syntax_Syntax.actions in
                      {
                        FStar_Syntax_Syntax.mname =
                          (uu___765_7428.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___765_7428.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.univs =
                          (uu___765_7428.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___765_7428.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (let uu____7436 = signature in
                           match uu____7436 with
                           | (us, t, uu____7451) -> (us, t));
                        FStar_Syntax_Syntax.combinators = combinators;
                        FStar_Syntax_Syntax.actions = uu____7429;
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___765_7428.FStar_Syntax_Syntax.eff_attrs)
                      }))))))))
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun _quals ->
        fun _attrs ->
          let uu____7496 =
            let uu____7497 =
              FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
            FStar_Util.format1 "While checking effect definition `%s`"
              uu____7497 in
          FStar_Errors.with_ctx uu____7496
            (fun uu____7542 ->
               (let uu____7544 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                    (FStar_Options.Other "ED") in
                if uu____7544
                then
                  let uu____7545 =
                    FStar_Syntax_Print.eff_decl_to_string false ed in
                  FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n"
                    uu____7545
                else ());
               (let uu____7547 =
                  let uu____7552 =
                    FStar_Syntax_Subst.univ_var_opening
                      ed.FStar_Syntax_Syntax.univs in
                  match uu____7552 with
                  | (ed_univs_subst, ed_univs) ->
                      let bs =
                        let uu____7576 =
                          FStar_Syntax_Subst.subst_binders ed_univs_subst
                            ed.FStar_Syntax_Syntax.binders in
                        FStar_Syntax_Subst.open_binders uu____7576 in
                      let uu____7577 =
                        let uu____7584 =
                          FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                        FStar_TypeChecker_TcTerm.tc_tparams uu____7584 bs in
                      (match uu____7577 with
                       | (bs1, uu____7590, uu____7591) ->
                           let uu____7592 =
                             let tmp_t =
                               let uu____7602 =
                                 let uu____7605 =
                                   FStar_All.pipe_right
                                     FStar_Syntax_Syntax.U_zero
                                     (fun uu____7610 ->
                                        FStar_Pervasives_Native.Some
                                          uu____7610) in
                                 FStar_Syntax_Syntax.mk_Total'
                                   FStar_Syntax_Syntax.t_unit uu____7605 in
                               FStar_Syntax_Util.arrow bs1 uu____7602 in
                             let uu____7611 =
                               FStar_TypeChecker_Generalize.generalize_universes
                                 env0 tmp_t in
                             match uu____7611 with
                             | (us, tmp_t1) ->
                                 let uu____7628 =
                                   let uu____7629 =
                                     let uu____7630 =
                                       FStar_All.pipe_right tmp_t1
                                         FStar_Syntax_Util.arrow_formals in
                                     FStar_All.pipe_right uu____7630
                                       FStar_Pervasives_Native.fst in
                                   FStar_All.pipe_right uu____7629
                                     FStar_Syntax_Subst.close_binders in
                                 (us, uu____7628) in
                           (match uu____7592 with
                            | (us, bs2) ->
                                (match ed_univs with
                                 | [] -> (us, bs2)
                                 | uu____7667 ->
                                     let uu____7670 =
                                       ((FStar_List.length ed_univs) =
                                          (FStar_List.length us))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1 ->
                                               fun u2 ->
                                                 let uu____7676 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2 in
                                                 uu____7676 = Prims.int_zero)
                                            ed_univs us) in
                                     if uu____7670
                                     then (us, bs2)
                                     else
                                       (let uu____7682 =
                                          let uu____7687 =
                                            let uu____7688 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____7689 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length ed_univs) in
                                            let uu____7690 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length us) in
                                            FStar_Util.format3
                                              "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                              uu____7688 uu____7689
                                              uu____7690 in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____7687) in
                                        let uu____7691 =
                                          FStar_Ident.range_of_lid
                                            ed.FStar_Syntax_Syntax.mname in
                                        FStar_Errors.raise_error uu____7682
                                          uu____7691)))) in
                match uu____7547 with
                | (us, bs) ->
                    let ed1 =
                      let uu___801_7699 = ed in
                      {
                        FStar_Syntax_Syntax.mname =
                          (uu___801_7699.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___801_7699.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.univs = us;
                        FStar_Syntax_Syntax.binders = bs;
                        FStar_Syntax_Syntax.signature =
                          (uu___801_7699.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.combinators =
                          (uu___801_7699.FStar_Syntax_Syntax.combinators);
                        FStar_Syntax_Syntax.actions =
                          (uu___801_7699.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___801_7699.FStar_Syntax_Syntax.eff_attrs)
                      } in
                    let uu____7700 = FStar_Syntax_Subst.univ_var_opening us in
                    (match uu____7700 with
                     | (ed_univs_subst, ed_univs) ->
                         let uu____7719 =
                           let uu____7724 =
                             FStar_Syntax_Subst.subst_binders ed_univs_subst
                               bs in
                           FStar_Syntax_Subst.open_binders' uu____7724 in
                         (match uu____7719 with
                          | (ed_bs, ed_bs_subst) ->
                              let ed2 =
                                let op uu____7745 =
                                  match uu____7745 with
                                  | (us1, t) ->
                                      let t1 =
                                        let uu____7765 =
                                          FStar_Syntax_Subst.shift_subst
                                            ((FStar_List.length ed_bs) +
                                               (FStar_List.length us1))
                                            ed_univs_subst in
                                        FStar_Syntax_Subst.subst uu____7765 t in
                                      let uu____7774 =
                                        let uu____7775 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length us1)
                                            ed_bs_subst in
                                        FStar_Syntax_Subst.subst uu____7775
                                          t1 in
                                      (us1, uu____7774) in
                                let uu___815_7780 = ed1 in
                                let uu____7781 =
                                  op ed1.FStar_Syntax_Syntax.signature in
                                let uu____7782 =
                                  FStar_Syntax_Util.apply_eff_combinators op
                                    ed1.FStar_Syntax_Syntax.combinators in
                                let uu____7783 =
                                  FStar_List.map
                                    (fun a ->
                                       let uu___818_7791 = a in
                                       let uu____7792 =
                                         let uu____7793 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_defn)) in
                                         FStar_Pervasives_Native.snd
                                           uu____7793 in
                                       let uu____7804 =
                                         let uu____7805 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_typ)) in
                                         FStar_Pervasives_Native.snd
                                           uu____7805 in
                                       {
                                         FStar_Syntax_Syntax.action_name =
                                           (uu___818_7791.FStar_Syntax_Syntax.action_name);
                                         FStar_Syntax_Syntax.action_unqualified_name
                                           =
                                           (uu___818_7791.FStar_Syntax_Syntax.action_unqualified_name);
                                         FStar_Syntax_Syntax.action_univs =
                                           (uu___818_7791.FStar_Syntax_Syntax.action_univs);
                                         FStar_Syntax_Syntax.action_params =
                                           (uu___818_7791.FStar_Syntax_Syntax.action_params);
                                         FStar_Syntax_Syntax.action_defn =
                                           uu____7792;
                                         FStar_Syntax_Syntax.action_typ =
                                           uu____7804
                                       }) ed1.FStar_Syntax_Syntax.actions in
                                {
                                  FStar_Syntax_Syntax.mname =
                                    (uu___815_7780.FStar_Syntax_Syntax.mname);
                                  FStar_Syntax_Syntax.cattributes =
                                    (uu___815_7780.FStar_Syntax_Syntax.cattributes);
                                  FStar_Syntax_Syntax.univs =
                                    (uu___815_7780.FStar_Syntax_Syntax.univs);
                                  FStar_Syntax_Syntax.binders =
                                    (uu___815_7780.FStar_Syntax_Syntax.binders);
                                  FStar_Syntax_Syntax.signature = uu____7781;
                                  FStar_Syntax_Syntax.combinators =
                                    uu____7782;
                                  FStar_Syntax_Syntax.actions = uu____7783;
                                  FStar_Syntax_Syntax.eff_attrs =
                                    (uu___815_7780.FStar_Syntax_Syntax.eff_attrs)
                                } in
                              ((let uu____7817 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____7817
                                then
                                  let uu____7818 =
                                    FStar_Syntax_Print.eff_decl_to_string
                                      false ed2 in
                                  FStar_Util.print1
                                    "After typechecking binders eff_decl: \n\t%s\n"
                                    uu____7818
                                else ());
                               (let env =
                                  let uu____7821 =
                                    FStar_TypeChecker_Env.push_univ_vars env0
                                      ed_univs in
                                  FStar_TypeChecker_Env.push_binders
                                    uu____7821 ed_bs in
                                let check_and_gen' comb n env_opt uu____7854
                                  k =
                                  match uu____7854 with
                                  | (us1, t) ->
                                      let env1 =
                                        if FStar_Util.is_some env_opt
                                        then
                                          FStar_All.pipe_right env_opt
                                            FStar_Util.must
                                        else env in
                                      let uu____7870 =
                                        FStar_Syntax_Subst.open_univ_vars us1
                                          t in
                                      (match uu____7870 with
                                       | (us2, t1) ->
                                           let t2 =
                                             match k with
                                             | FStar_Pervasives_Native.Some
                                                 k1 ->
                                                 let uu____7879 =
                                                   FStar_TypeChecker_Env.push_univ_vars
                                                     env1 us2 in
                                                 FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                   uu____7879 t1 k1
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu____7880 =
                                                   let uu____7887 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env1 us2 in
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     uu____7887 t1 in
                                                 (match uu____7880 with
                                                  | (t2, uu____7889, g) ->
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env1 g;
                                                       t2)) in
                                           let uu____7892 =
                                             FStar_TypeChecker_Generalize.generalize_universes
                                               env1 t2 in
                                           (match uu____7892 with
                                            | (g_us, t3) ->
                                                (if
                                                   (FStar_List.length g_us)
                                                     <> n
                                                 then
                                                   (let error =
                                                      let uu____7905 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____7906 =
                                                        FStar_Util.string_of_int
                                                          n in
                                                      let uu____7907 =
                                                        let uu____7908 =
                                                          FStar_All.pipe_right
                                                            g_us
                                                            FStar_List.length in
                                                        FStar_All.pipe_right
                                                          uu____7908
                                                          FStar_Util.string_of_int in
                                                      FStar_Util.format4
                                                        "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                        uu____7905 comb
                                                        uu____7906 uu____7907 in
                                                    FStar_Errors.raise_error
                                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                        error)
                                                      t3.FStar_Syntax_Syntax.pos)
                                                 else ();
                                                 (match us2 with
                                                  | [] -> (g_us, t3)
                                                  | uu____7916 ->
                                                      let uu____7917 =
                                                        ((FStar_List.length
                                                            us2)
                                                           =
                                                           (FStar_List.length
                                                              g_us))
                                                          &&
                                                          (FStar_List.forall2
                                                             (fun u1 ->
                                                                fun u2 ->
                                                                  let uu____7923
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                  uu____7923
                                                                    =
                                                                    Prims.int_zero)
                                                             us2 g_us) in
                                                      if uu____7917
                                                      then (g_us, t3)
                                                      else
                                                        (let uu____7929 =
                                                           let uu____7934 =
                                                             let uu____7935 =
                                                               FStar_Ident.string_of_lid
                                                                 ed2.FStar_Syntax_Syntax.mname in
                                                             let uu____7936 =
                                                               FStar_Util.string_of_int
                                                                 (FStar_List.length
                                                                    us2) in
                                                             let uu____7937 =
                                                               FStar_Util.string_of_int
                                                                 (FStar_List.length
                                                                    g_us) in
                                                             FStar_Util.format4
                                                               "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                               uu____7935
                                                               comb
                                                               uu____7936
                                                               uu____7937 in
                                                           (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                             uu____7934) in
                                                         FStar_Errors.raise_error
                                                           uu____7929
                                                           t3.FStar_Syntax_Syntax.pos))))) in
                                let signature =
                                  check_and_gen' "signature" Prims.int_one
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                    FStar_Pervasives_Native.None in
                                (let uu____7940 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "ED") in
                                 if uu____7940
                                 then
                                   let uu____7941 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       signature in
                                   FStar_Util.print1
                                     "Typechecked signature: %s\n" uu____7941
                                 else ());
                                (let fresh_a_and_wp uu____7954 =
                                   let fail t =
                                     let uu____7967 =
                                       FStar_TypeChecker_Err.unexpected_signature_for_monad
                                         env ed2.FStar_Syntax_Syntax.mname t in
                                     FStar_Errors.raise_error uu____7967
                                       (FStar_Pervasives_Native.snd
                                          ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                                   let uu____7982 =
                                     FStar_TypeChecker_Env.inst_tscheme
                                       signature in
                                   match uu____7982 with
                                   | (uu____7993, signature1) ->
                                       let uu____7995 =
                                         let uu____7996 =
                                           FStar_Syntax_Subst.compress
                                             signature1 in
                                         uu____7996.FStar_Syntax_Syntax.n in
                                       (match uu____7995 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs1, uu____8006) ->
                                            let bs2 =
                                              FStar_Syntax_Subst.open_binders
                                                bs1 in
                                            (match bs2 with
                                             | (a, uu____8035)::(wp,
                                                                 uu____8037)::[]
                                                 ->
                                                 (a,
                                                   (wp.FStar_Syntax_Syntax.sort))
                                             | uu____8066 -> fail signature1)
                                        | uu____8067 -> fail signature1) in
                                 let log_combinator s ts =
                                   let uu____8079 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED") in
                                   if uu____8079
                                   then
                                     let uu____8080 =
                                       FStar_Ident.string_of_lid
                                         ed2.FStar_Syntax_Syntax.mname in
                                     let uu____8081 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         ts in
                                     FStar_Util.print3
                                       "Typechecked %s:%s = %s\n" uu____8080
                                       s uu____8081
                                   else () in
                                 let ret_wp =
                                   let uu____8084 = fresh_a_and_wp () in
                                   match uu____8084 with
                                   | (a, wp_sort) ->
                                       let k =
                                         let uu____8100 =
                                           let uu____8109 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8116 =
                                             let uu____8125 =
                                               let uu____8132 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a in
                                               FStar_Syntax_Syntax.null_binder
                                                 uu____8132 in
                                             [uu____8125] in
                                           uu____8109 :: uu____8116 in
                                         let uu____8151 =
                                           FStar_Syntax_Syntax.mk_GTotal
                                             wp_sort in
                                         FStar_Syntax_Util.arrow uu____8100
                                           uu____8151 in
                                       let uu____8154 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_return_vc_combinator in
                                       check_and_gen' "ret_wp" Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____8154
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "ret_wp" ret_wp;
                                 (let bind_wp =
                                    let uu____8165 = fresh_a_and_wp () in
                                    match uu____8165 with
                                    | (a, wp_sort_a) ->
                                        let uu____8178 = fresh_a_and_wp () in
                                        (match uu____8178 with
                                         | (b, wp_sort_b) ->
                                             let wp_sort_a_b =
                                               let uu____8194 =
                                                 let uu____8203 =
                                                   let uu____8210 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____8210 in
                                                 [uu____8203] in
                                               let uu____8223 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu____8194 uu____8223 in
                                             let k =
                                               let uu____8229 =
                                                 let uu____8238 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_range in
                                                 let uu____8245 =
                                                   let uu____8254 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a in
                                                   let uu____8261 =
                                                     let uu____8270 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         b in
                                                     let uu____8277 =
                                                       let uu____8286 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       let uu____8293 =
                                                         let uu____8302 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a_b in
                                                         [uu____8302] in
                                                       uu____8286 ::
                                                         uu____8293 in
                                                     uu____8270 :: uu____8277 in
                                                   uu____8254 :: uu____8261 in
                                                 uu____8238 :: uu____8245 in
                                               let uu____8345 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu____8229 uu____8345 in
                                             let uu____8348 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_vc_combinator in
                                             check_and_gen' "bind_wp"
                                               (Prims.of_int (2))
                                               FStar_Pervasives_Native.None
                                               uu____8348
                                               (FStar_Pervasives_Native.Some
                                                  k)) in
                                  log_combinator "bind_wp" bind_wp;
                                  (let stronger =
                                     let uu____8359 = fresh_a_and_wp () in
                                     match uu____8359 with
                                     | (a, wp_sort_a) ->
                                         let uu____8372 =
                                           FStar_Syntax_Util.type_u () in
                                         (match uu____8372 with
                                          | (t, uu____8378) ->
                                              let k =
                                                let uu____8382 =
                                                  let uu____8391 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____8398 =
                                                    let uu____8407 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    let uu____8414 =
                                                      let uu____8423 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_sort_a in
                                                      [uu____8423] in
                                                    uu____8407 :: uu____8414 in
                                                  uu____8391 :: uu____8398 in
                                                let uu____8454 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t in
                                                FStar_Syntax_Util.arrow
                                                  uu____8382 uu____8454 in
                                              let uu____8457 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_stronger_vc_combinator in
                                              check_and_gen' "stronger"
                                                Prims.int_one
                                                FStar_Pervasives_Native.None
                                                uu____8457
                                                (FStar_Pervasives_Native.Some
                                                   k)) in
                                   log_combinator "stronger" stronger;
                                   (let if_then_else =
                                      let uu____8468 = fresh_a_and_wp () in
                                      match uu____8468 with
                                      | (a, wp_sort_a) ->
                                          let p =
                                            let uu____8482 =
                                              let uu____8485 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname in
                                              FStar_Pervasives_Native.Some
                                                uu____8485 in
                                            let uu____8486 =
                                              let uu____8487 =
                                                FStar_Syntax_Util.type_u () in
                                              FStar_All.pipe_right uu____8487
                                                FStar_Pervasives_Native.fst in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____8482 uu____8486 in
                                          let k =
                                            let uu____8499 =
                                              let uu____8508 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8515 =
                                                let uu____8524 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    p in
                                                let uu____8531 =
                                                  let uu____8540 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8547 =
                                                    let uu____8556 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    [uu____8556] in
                                                  uu____8540 :: uu____8547 in
                                                uu____8524 :: uu____8531 in
                                              uu____8508 :: uu____8515 in
                                            let uu____8593 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a in
                                            FStar_Syntax_Util.arrow
                                              uu____8499 uu____8593 in
                                          let uu____8596 =
                                            let uu____8601 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                            FStar_All.pipe_right uu____8601
                                              FStar_Util.must in
                                          check_and_gen' "if_then_else"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____8596
                                            (FStar_Pervasives_Native.Some k) in
                                    log_combinator "if_then_else"
                                      if_then_else;
                                    (let ite_wp =
                                       let uu____8614 = fresh_a_and_wp () in
                                       match uu____8614 with
                                       | (a, wp_sort_a) ->
                                           let k =
                                             let uu____8630 =
                                               let uu____8639 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____8646 =
                                                 let uu____8655 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8655] in
                                               uu____8639 :: uu____8646 in
                                             let uu____8680 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a in
                                             FStar_Syntax_Util.arrow
                                               uu____8630 uu____8680 in
                                           let uu____8683 =
                                             let uu____8688 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_wp_ite_combinator in
                                             FStar_All.pipe_right uu____8688
                                               FStar_Util.must in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             uu____8683
                                             (FStar_Pervasives_Native.Some k) in
                                     log_combinator "ite_wp" ite_wp;
                                     (let close_wp =
                                        let uu____8701 = fresh_a_and_wp () in
                                        match uu____8701 with
                                        | (a, wp_sort_a) ->
                                            let b =
                                              let uu____8715 =
                                                let uu____8718 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname in
                                                FStar_Pervasives_Native.Some
                                                  uu____8718 in
                                              let uu____8719 =
                                                let uu____8720 =
                                                  FStar_Syntax_Util.type_u () in
                                                FStar_All.pipe_right
                                                  uu____8720
                                                  FStar_Pervasives_Native.fst in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____8715 uu____8719 in
                                            let wp_sort_b_a =
                                              let uu____8732 =
                                                let uu____8741 =
                                                  let uu____8748 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____8748 in
                                                [uu____8741] in
                                              let uu____8761 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow
                                                uu____8732 uu____8761 in
                                            let k =
                                              let uu____8767 =
                                                let uu____8776 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____8783 =
                                                  let uu____8792 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____8799 =
                                                    let uu____8808 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a in
                                                    [uu____8808] in
                                                  uu____8792 :: uu____8799 in
                                                uu____8776 :: uu____8783 in
                                              let uu____8839 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow
                                                uu____8767 uu____8839 in
                                            let uu____8842 =
                                              let uu____8847 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_wp_close_combinator in
                                              FStar_All.pipe_right uu____8847
                                                FStar_Util.must in
                                            check_and_gen' "close_wp"
                                              (Prims.of_int (2))
                                              FStar_Pervasives_Native.None
                                              uu____8842
                                              (FStar_Pervasives_Native.Some k) in
                                      log_combinator "close_wp" close_wp;
                                      (let trivial =
                                         let uu____8860 = fresh_a_and_wp () in
                                         match uu____8860 with
                                         | (a, wp_sort_a) ->
                                             let uu____8873 =
                                               FStar_Syntax_Util.type_u () in
                                             (match uu____8873 with
                                              | (t, uu____8879) ->
                                                  let k =
                                                    let uu____8883 =
                                                      let uu____8892 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
                                                      let uu____8899 =
                                                        let uu____8908 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            wp_sort_a in
                                                        [uu____8908] in
                                                      uu____8892 ::
                                                        uu____8899 in
                                                    let uu____8933 =
                                                      FStar_Syntax_Syntax.mk_GTotal
                                                        t in
                                                    FStar_Syntax_Util.arrow
                                                      uu____8883 uu____8933 in
                                                  let trivial =
                                                    let uu____8937 =
                                                      let uu____8942 =
                                                        FStar_All.pipe_right
                                                          ed2
                                                          FStar_Syntax_Util.get_wp_trivial_combinator in
                                                      FStar_All.pipe_right
                                                        uu____8942
                                                        FStar_Util.must in
                                                    check_and_gen' "trivial"
                                                      Prims.int_one
                                                      FStar_Pervasives_Native.None
                                                      uu____8937
                                                      (FStar_Pervasives_Native.Some
                                                         k) in
                                                  (log_combinator "trivial"
                                                     trivial;
                                                   trivial)) in
                                       let uu____8954 =
                                         let uu____8971 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_eff_repr in
                                         match uu____8971 with
                                         | FStar_Pervasives_Native.None ->
                                             (FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               (ed2.FStar_Syntax_Syntax.actions))
                                         | uu____9000 ->
                                             let repr =
                                               let uu____9004 =
                                                 fresh_a_and_wp () in
                                               match uu____9004 with
                                               | (a, wp_sort_a) ->
                                                   let uu____9017 =
                                                     FStar_Syntax_Util.type_u
                                                       () in
                                                   (match uu____9017 with
                                                    | (t, uu____9023) ->
                                                        let k =
                                                          let uu____9027 =
                                                            let uu____9036 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu____9043 =
                                                              let uu____9052
                                                                =
                                                                FStar_Syntax_Syntax.null_binder
                                                                  wp_sort_a in
                                                              [uu____9052] in
                                                            uu____9036 ::
                                                              uu____9043 in
                                                          let uu____9077 =
                                                            FStar_Syntax_Syntax.mk_GTotal
                                                              t in
                                                          FStar_Syntax_Util.arrow
                                                            uu____9027
                                                            uu____9077 in
                                                        let uu____9080 =
                                                          let uu____9085 =
                                                            FStar_All.pipe_right
                                                              ed2
                                                              FStar_Syntax_Util.get_eff_repr in
                                                          FStar_All.pipe_right
                                                            uu____9085
                                                            FStar_Util.must in
                                                        check_and_gen' "repr"
                                                          Prims.int_one
                                                          FStar_Pervasives_Native.None
                                                          uu____9080
                                                          (FStar_Pervasives_Native.Some
                                                             k)) in
                                             (log_combinator "repr" repr;
                                              (let mk_repr' t wp =
                                                 let uu____9110 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     repr in
                                                 match uu____9110 with
                                                 | (uu____9117, repr1) ->
                                                     let repr2 =
                                                       FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Env.EraseUniverses;
                                                         FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                         env repr1 in
                                                     let uu____9120 =
                                                       let uu____9121 =
                                                         let uu____9138 =
                                                           let uu____9149 =
                                                             FStar_All.pipe_right
                                                               t
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu____9166 =
                                                             let uu____9177 =
                                                               FStar_All.pipe_right
                                                                 wp
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu____9177] in
                                                           uu____9149 ::
                                                             uu____9166 in
                                                         (repr2, uu____9138) in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu____9121 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____9120
                                                       FStar_Range.dummyRange in
                                               let mk_repr a wp =
                                                 let uu____9243 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a in
                                                 mk_repr' uu____9243 wp in
                                               let destruct_repr t =
                                                 let uu____9258 =
                                                   let uu____9259 =
                                                     FStar_Syntax_Subst.compress
                                                       t in
                                                   uu____9259.FStar_Syntax_Syntax.n in
                                                 match uu____9258 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____9270,
                                                      (t1, uu____9272)::
                                                      (wp, uu____9274)::[])
                                                     -> (t1, wp)
                                                 | uu____9333 ->
                                                     failwith
                                                       "Unexpected repr type" in
                                               let return_repr =
                                                 let return_repr_ts =
                                                   let uu____9350 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_return_repr in
                                                   FStar_All.pipe_right
                                                     uu____9350
                                                     FStar_Util.must in
                                                 let uu____9387 =
                                                   fresh_a_and_wp () in
                                                 match uu____9387 with
                                                 | (a, uu____9395) ->
                                                     let x_a =
                                                       let uu____9401 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "x_a"
                                                         FStar_Pervasives_Native.None
                                                         uu____9401 in
                                                     let res =
                                                       let wp =
                                                         let uu____9406 =
                                                           let uu____9407 =
                                                             FStar_TypeChecker_Env.inst_tscheme
                                                               ret_wp in
                                                           FStar_All.pipe_right
                                                             uu____9407
                                                             FStar_Pervasives_Native.snd in
                                                         let uu____9416 =
                                                           let uu____9417 =
                                                             let uu____9426 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_All.pipe_right
                                                               uu____9426
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu____9435 =
                                                             let uu____9446 =
                                                               let uu____9455
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   x_a in
                                                               FStar_All.pipe_right
                                                                 uu____9455
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu____9446] in
                                                           uu____9417 ::
                                                             uu____9435 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____9406
                                                           uu____9416
                                                           FStar_Range.dummyRange in
                                                       mk_repr a wp in
                                                     let k =
                                                       let uu____9491 =
                                                         let uu____9500 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             a in
                                                         let uu____9507 =
                                                           let uu____9516 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____9516] in
                                                         uu____9500 ::
                                                           uu____9507 in
                                                       let uu____9541 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           res in
                                                       FStar_Syntax_Util.arrow
                                                         uu____9491
                                                         uu____9541 in
                                                     let uu____9544 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env k in
                                                     (match uu____9544 with
                                                      | (k1, uu____9552,
                                                         uu____9553) ->
                                                          let env1 =
                                                            let uu____9557 =
                                                              FStar_TypeChecker_Env.set_range
                                                                env
                                                                (FStar_Pervasives_Native.snd
                                                                   return_repr_ts).FStar_Syntax_Syntax.pos in
                                                            FStar_Pervasives_Native.Some
                                                              uu____9557 in
                                                          check_and_gen'
                                                            "return_repr"
                                                            Prims.int_one
                                                            env1
                                                            return_repr_ts
                                                            (FStar_Pervasives_Native.Some
                                                               k1)) in
                                               log_combinator "return_repr"
                                                 return_repr;
                                               (let bind_repr =
                                                  let bind_repr_ts =
                                                    let uu____9567 =
                                                      FStar_All.pipe_right
                                                        ed2
                                                        FStar_Syntax_Util.get_bind_repr in
                                                    FStar_All.pipe_right
                                                      uu____9567
                                                      FStar_Util.must in
                                                  let r =
                                                    let uu____9579 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        FStar_Parser_Const.range_0
                                                        FStar_Syntax_Syntax.delta_constant
                                                        FStar_Pervasives_Native.None in
                                                    FStar_All.pipe_right
                                                      uu____9579
                                                      FStar_Syntax_Syntax.fv_to_tm in
                                                  let uu____9580 =
                                                    fresh_a_and_wp () in
                                                  match uu____9580 with
                                                  | (a, wp_sort_a) ->
                                                      let uu____9593 =
                                                        fresh_a_and_wp () in
                                                      (match uu____9593 with
                                                       | (b, wp_sort_b) ->
                                                           let wp_sort_a_b =
                                                             let uu____9609 =
                                                               let uu____9618
                                                                 =
                                                                 let uu____9625
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____9625 in
                                                               [uu____9618] in
                                                             let uu____9638 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 wp_sort_b in
                                                             FStar_Syntax_Util.arrow
                                                               uu____9609
                                                               uu____9638 in
                                                           let wp_f =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp_f"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a in
                                                           let wp_g =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp_g"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a_b in
                                                           let x_a =
                                                             let uu____9644 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "x_a"
                                                               FStar_Pervasives_Native.None
                                                               uu____9644 in
                                                           let wp_g_x =
                                                             let uu____9646 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_g in
                                                             let uu____9647 =
                                                               let uu____9648
                                                                 =
                                                                 let uu____9657
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    x_a in
                                                                 FStar_All.pipe_right
                                                                   uu____9657
                                                                   FStar_Syntax_Syntax.as_arg in
                                                               [uu____9648] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____9646
                                                               uu____9647
                                                               FStar_Range.dummyRange in
                                                           let res =
                                                             let wp =
                                                               let uu____9686
                                                                 =
                                                                 let uu____9687
                                                                   =
                                                                   FStar_TypeChecker_Env.inst_tscheme
                                                                    bind_wp in
                                                                 FStar_All.pipe_right
                                                                   uu____9687
                                                                   FStar_Pervasives_Native.snd in
                                                               let uu____9696
                                                                 =
                                                                 let uu____9697
                                                                   =
                                                                   let uu____9700
                                                                    =
                                                                    let uu____9703
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                    let uu____9704
                                                                    =
                                                                    let uu____9707
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    let uu____9708
                                                                    =
                                                                    let uu____9711
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____9712
                                                                    =
                                                                    let uu____9715
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____9715] in
                                                                    uu____9711
                                                                    ::
                                                                    uu____9712 in
                                                                    uu____9707
                                                                    ::
                                                                    uu____9708 in
                                                                    uu____9703
                                                                    ::
                                                                    uu____9704 in
                                                                   r ::
                                                                    uu____9700 in
                                                                 FStar_List.map
                                                                   FStar_Syntax_Syntax.as_arg
                                                                   uu____9697 in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____9686
                                                                 uu____9696
                                                                 FStar_Range.dummyRange in
                                                             mk_repr b wp in
                                                           let maybe_range_arg
                                                             =
                                                             let uu____9733 =
                                                               FStar_Util.for_some
                                                                 (FStar_Syntax_Util.attr_eq
                                                                    FStar_Syntax_Util.dm4f_bind_range_attr)
                                                                 ed2.FStar_Syntax_Syntax.eff_attrs in
                                                             if uu____9733
                                                             then
                                                               let uu____9742
                                                                 =
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   FStar_Syntax_Syntax.t_range in
                                                               let uu____9749
                                                                 =
                                                                 let uu____9758
                                                                   =
                                                                   FStar_Syntax_Syntax.null_binder
                                                                    FStar_Syntax_Syntax.t_range in
                                                                 [uu____9758] in
                                                               uu____9742 ::
                                                                 uu____9749
                                                             else [] in
                                                           let k =
                                                             let uu____9793 =
                                                               let uu____9802
                                                                 =
                                                                 let uu____9811
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    a in
                                                                 let uu____9818
                                                                   =
                                                                   let uu____9827
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    b in
                                                                   [uu____9827] in
                                                                 uu____9811
                                                                   ::
                                                                   uu____9818 in
                                                               let uu____9852
                                                                 =
                                                                 let uu____9861
                                                                   =
                                                                   let uu____9870
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_f in
                                                                   let uu____9877
                                                                    =
                                                                    let uu____9886
                                                                    =
                                                                    let uu____9893
                                                                    =
                                                                    let uu____9894
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____9894 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9893 in
                                                                    let uu____9895
                                                                    =
                                                                    let uu____9904
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                    let uu____9911
                                                                    =
                                                                    let uu____9920
                                                                    =
                                                                    let uu____9927
                                                                    =
                                                                    let uu____9928
                                                                    =
                                                                    let uu____9937
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____9937] in
                                                                    let uu____9956
                                                                    =
                                                                    let uu____9959
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____9959 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9928
                                                                    uu____9956 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9927 in
                                                                    [uu____9920] in
                                                                    uu____9904
                                                                    ::
                                                                    uu____9911 in
                                                                    uu____9886
                                                                    ::
                                                                    uu____9895 in
                                                                   uu____9870
                                                                    ::
                                                                    uu____9877 in
                                                                 FStar_List.append
                                                                   maybe_range_arg
                                                                   uu____9861 in
                                                               FStar_List.append
                                                                 uu____9802
                                                                 uu____9852 in
                                                             let uu____10004
                                                               =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 res in
                                                             FStar_Syntax_Util.arrow
                                                               uu____9793
                                                               uu____10004 in
                                                           let uu____10007 =
                                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                               env k in
                                                           (match uu____10007
                                                            with
                                                            | (k1,
                                                               uu____10015,
                                                               uu____10016)
                                                                ->
                                                                let env1 =
                                                                  FStar_TypeChecker_Env.set_range
                                                                    env
                                                                    (FStar_Pervasives_Native.snd
                                                                    bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                                let env2 =
                                                                  FStar_All.pipe_right
                                                                    (
                                                                    let uu___1013_10024
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1013_10024.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    })
                                                                    (
                                                                    fun
                                                                    uu____10025
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10025) in
                                                                check_and_gen'
                                                                  "bind_repr"
                                                                  (Prims.of_int (2))
                                                                  env2
                                                                  bind_repr_ts
                                                                  (FStar_Pervasives_Native.Some
                                                                    k1))) in
                                                log_combinator "bind_repr"
                                                  bind_repr;
                                                (let actions =
                                                   let check_action act =
                                                     if
                                                       (FStar_List.length
                                                          act.FStar_Syntax_Syntax.action_params)
                                                         <> Prims.int_zero
                                                     then
                                                       failwith
                                                         "tc_eff_decl: expected action_params to be empty"
                                                     else ();
                                                     (let uu____10044 =
                                                        if
                                                          act.FStar_Syntax_Syntax.action_univs
                                                            = []
                                                        then (env, act)
                                                        else
                                                          (let uu____10056 =
                                                             FStar_Syntax_Subst.univ_var_opening
                                                               act.FStar_Syntax_Syntax.action_univs in
                                                           match uu____10056
                                                           with
                                                           | (usubst, uvs) ->
                                                               let uu____10079
                                                                 =
                                                                 FStar_TypeChecker_Env.push_univ_vars
                                                                   env uvs in
                                                               let uu____10080
                                                                 =
                                                                 let uu___1026_10081
                                                                   = act in
                                                                 let uu____10082
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_defn in
                                                                 let uu____10083
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_typ in
                                                                 {
                                                                   FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1026_10081.FStar_Syntax_Syntax.action_name);
                                                                   FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1026_10081.FStar_Syntax_Syntax.action_unqualified_name);
                                                                   FStar_Syntax_Syntax.action_univs
                                                                    = uvs;
                                                                   FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1026_10081.FStar_Syntax_Syntax.action_params);
                                                                   FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____10082;
                                                                   FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____10083
                                                                 } in
                                                               (uu____10079,
                                                                 uu____10080)) in
                                                      match uu____10044 with
                                                      | (env1, act1) ->
                                                          let act_typ =
                                                            let uu____10087 =
                                                              let uu____10088
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  act1.FStar_Syntax_Syntax.action_typ in
                                                              uu____10088.FStar_Syntax_Syntax.n in
                                                            match uu____10087
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_arrow
                                                                (bs1, c) ->
                                                                let c1 =
                                                                  FStar_Syntax_Util.comp_to_comp_typ
                                                                    c in
                                                                let uu____10114
                                                                  =
                                                                  FStar_Ident.lid_equals
                                                                    c1.FStar_Syntax_Syntax.effect_name
                                                                    ed2.FStar_Syntax_Syntax.mname in
                                                                if
                                                                  uu____10114
                                                                then
                                                                  let uu____10115
                                                                    =
                                                                    let uu____10118
                                                                    =
                                                                    let uu____10119
                                                                    =
                                                                    let uu____10120
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____10120 in
                                                                    mk_repr'
                                                                    c1.FStar_Syntax_Syntax.result_typ
                                                                    uu____10119 in
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10118 in
                                                                  FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____10115
                                                                else
                                                                  act1.FStar_Syntax_Syntax.action_typ
                                                            | uu____10142 ->
                                                                act1.FStar_Syntax_Syntax.action_typ in
                                                          let uu____10143 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 act_typ in
                                                          (match uu____10143
                                                           with
                                                           | (act_typ1,
                                                              uu____10151,
                                                              g_t) ->
                                                               let env' =
                                                                 let uu___1043_10154
                                                                   =
                                                                   FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    act_typ1 in
                                                                 {
                                                                   FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.solver);
                                                                   FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.range);
                                                                   FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.curmodule);
                                                                   FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.gamma);
                                                                   FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.gamma_sig);
                                                                   FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.gamma_cache);
                                                                   FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.modules);
                                                                   FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.expected_typ);
                                                                   FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.sigtab);
                                                                   FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.attrtab);
                                                                   FStar_TypeChecker_Env.instantiate_imp
                                                                    = false;
                                                                   FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.effects);
                                                                   FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.generalize);
                                                                   FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.letrecs);
                                                                   FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.top_level);
                                                                   FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.check_uvars);
                                                                   FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.use_eq);
                                                                   FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.use_eq_strict);
                                                                   FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.is_iface);
                                                                   FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.admit);
                                                                   FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.lax);
                                                                   FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.lax_universes);
                                                                   FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.phase1);
                                                                   FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.failhard);
                                                                   FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.nosynth);
                                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.uvar_subtyping);
                                                                   FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.tc_term);
                                                                   FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.type_of);
                                                                   FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.universe_of);
                                                                   FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.check_type_of);
                                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.use_bv_sorts);
                                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.normalized_eff_names);
                                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.fv_delta_depths);
                                                                   FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.proof_ns);
                                                                   FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.synth_hook);
                                                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                   FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.splice);
                                                                   FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.mpreprocess);
                                                                   FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.postprocess);
                                                                   FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.identifier_info);
                                                                   FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.tc_hooks);
                                                                   FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.dsenv);
                                                                   FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.nbe);
                                                                   FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.strict_args_tab);
                                                                   FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.erasable_types_tab);
                                                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1043_10154.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                 } in
                                                               ((let uu____10156
                                                                   =
                                                                   FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                 if
                                                                   uu____10156
                                                                 then
                                                                   let uu____10157
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                   let uu____10158
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                   let uu____10159
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ1 in
                                                                   FStar_Util.print3
                                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                    uu____10157
                                                                    uu____10158
                                                                    uu____10159
                                                                 else ());
                                                                (let uu____10161
                                                                   =
                                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env'
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                 match uu____10161
                                                                 with
                                                                 | (act_defn,
                                                                    uu____10169,
                                                                    g_a) ->
                                                                    let act_defn1
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                    env1
                                                                    act_defn in
                                                                    let act_typ2
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                    FStar_TypeChecker_Env.Eager_unfolding;
                                                                    FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ1 in
                                                                    let uu____10173
                                                                    =
                                                                    let act_typ3
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    act_typ2 in
                                                                    match 
                                                                    act_typ3.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10209
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10209
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10221)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10228
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10228 in
                                                                    let uu____10231
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10231
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10245,
                                                                    g) ->
                                                                    (k1, g)))
                                                                    | 
                                                                    uu____10249
                                                                    ->
                                                                    let uu____10250
                                                                    =
                                                                    let uu____10255
                                                                    =
                                                                    let uu____10256
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10257
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10256
                                                                    uu____10257 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10255) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10250
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                    (match uu____10173
                                                                    with
                                                                    | 
                                                                    (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu____10272
                                                                    =
                                                                    let uu____10273
                                                                    =
                                                                    let uu____10274
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10274 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10273 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10272);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10276
                                                                    =
                                                                    let uu____10277
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10277.FStar_Syntax_Syntax.n in
                                                                    match uu____10276
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10302
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10302
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10309
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10309
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10329
                                                                    =
                                                                    let uu____10330
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10330] in
                                                                    let uu____10331
                                                                    =
                                                                    let uu____10342
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10342] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10329;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10331;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10367
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10367))
                                                                    | 
                                                                    uu____10370
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10371
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10391
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10391)) in
                                                                    match uu____10371
                                                                    with
                                                                    | 
                                                                    (univs,
                                                                    act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs
                                                                    act_typ4 in
                                                                    let uu___1093_10410
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1093_10410.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1093_10410.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1093_10410.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))) in
                                                   FStar_All.pipe_right
                                                     ed2.FStar_Syntax_Syntax.actions
                                                     (FStar_List.map
                                                        check_action) in
                                                 ((FStar_Pervasives_Native.Some
                                                     repr),
                                                   (FStar_Pervasives_Native.Some
                                                      return_repr),
                                                   (FStar_Pervasives_Native.Some
                                                      bind_repr), actions))))) in
                                       match uu____8954 with
                                       | (repr, return_repr, bind_repr,
                                          actions) ->
                                           let cl ts =
                                             let ts1 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 ed_bs ts in
                                             let ed_univs_closing =
                                               FStar_Syntax_Subst.univ_var_closing
                                                 ed_univs in
                                             let uu____10453 =
                                               FStar_Syntax_Subst.shift_subst
                                                 (FStar_List.length ed_bs)
                                                 ed_univs_closing in
                                             FStar_Syntax_Subst.subst_tscheme
                                               uu____10453 ts1 in
                                           let combinators =
                                             {
                                               FStar_Syntax_Syntax.ret_wp =
                                                 ret_wp;
                                               FStar_Syntax_Syntax.bind_wp =
                                                 bind_wp;
                                               FStar_Syntax_Syntax.stronger =
                                                 stronger;
                                               FStar_Syntax_Syntax.if_then_else
                                                 = if_then_else;
                                               FStar_Syntax_Syntax.ite_wp =
                                                 ite_wp;
                                               FStar_Syntax_Syntax.close_wp =
                                                 close_wp;
                                               FStar_Syntax_Syntax.trivial =
                                                 trivial;
                                               FStar_Syntax_Syntax.repr =
                                                 repr;
                                               FStar_Syntax_Syntax.return_repr
                                                 = return_repr;
                                               FStar_Syntax_Syntax.bind_repr
                                                 = bind_repr
                                             } in
                                           let combinators1 =
                                             FStar_Syntax_Util.apply_wp_eff_combinators
                                               cl combinators in
                                           let combinators2 =
                                             match ed2.FStar_Syntax_Syntax.combinators
                                             with
                                             | FStar_Syntax_Syntax.Primitive_eff
                                                 uu____10465 ->
                                                 FStar_Syntax_Syntax.Primitive_eff
                                                   combinators1
                                             | FStar_Syntax_Syntax.DM4F_eff
                                                 uu____10466 ->
                                                 FStar_Syntax_Syntax.DM4F_eff
                                                   combinators1
                                             | uu____10467 ->
                                                 failwith
                                                   "Impossible! tc_eff_decl on a layered effect is not expected" in
                                           let ed3 =
                                             let uu___1113_10469 = ed2 in
                                             let uu____10470 = cl signature in
                                             let uu____10471 =
                                               FStar_List.map
                                                 (fun a ->
                                                    let uu___1116_10479 = a in
                                                    let uu____10480 =
                                                      let uu____10481 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_defn)) in
                                                      FStar_All.pipe_right
                                                        uu____10481
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____10506 =
                                                      let uu____10507 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_typ)) in
                                                      FStar_All.pipe_right
                                                        uu____10507
                                                        FStar_Pervasives_Native.snd in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___1116_10479.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___1116_10479.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        =
                                                        (uu___1116_10479.FStar_Syntax_Syntax.action_univs);
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___1116_10479.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = uu____10480;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____10506
                                                    }) actions in
                                             {
                                               FStar_Syntax_Syntax.mname =
                                                 (uu___1113_10469.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.cattributes
                                                 =
                                                 (uu___1113_10469.FStar_Syntax_Syntax.cattributes);
                                               FStar_Syntax_Syntax.univs =
                                                 (uu___1113_10469.FStar_Syntax_Syntax.univs);
                                               FStar_Syntax_Syntax.binders =
                                                 (uu___1113_10469.FStar_Syntax_Syntax.binders);
                                               FStar_Syntax_Syntax.signature
                                                 = uu____10470;
                                               FStar_Syntax_Syntax.combinators
                                                 = combinators2;
                                               FStar_Syntax_Syntax.actions =
                                                 uu____10471;
                                               FStar_Syntax_Syntax.eff_attrs
                                                 =
                                                 (uu___1113_10469.FStar_Syntax_Syntax.eff_attrs)
                                             } in
                                           ((let uu____10533 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other "ED") in
                                             if uu____10533
                                             then
                                               let uu____10534 =
                                                 FStar_Syntax_Print.eff_decl_to_string
                                                   false ed3 in
                                               FStar_Util.print1
                                                 "Typechecked effect declaration:\n\t%s\n"
                                                 uu____10534
                                             else ());
                                            ed3))))))))))))))
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu____10564 =
            let uu____10585 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____10585
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____10564 env ed quals attrs
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env ->
    fun m ->
      fun s ->
        let fail uu____10635 =
          let uu____10636 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____10641 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____10636 uu____10641 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____10685)::(wp, uu____10687)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____10716 -> fail ())
        | uu____10717 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____10729 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____10729
       then
         let uu____10730 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____10730
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____10744 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____10744.FStar_Syntax_Syntax.pos in
       let uu____10753 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____10753 with
       | (us, lift, lift_ty) ->
           ((let uu____10764 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____10764
             then
               let uu____10765 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____10770 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____10765 uu____10770
             else ());
            (let uu____10776 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____10776 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____10791 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____10792 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____10793 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____10791 uu____10792 s uu____10793 in
                   let uu____10794 =
                     let uu____10801 =
                       let uu____10806 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____10806
                         (fun uu____10823 ->
                            match uu____10823 with
                            | (t, u) ->
                                let uu____10834 =
                                  let uu____10835 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____10835
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____10834, u)) in
                     match uu____10801 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____10853 =
                             let uu____10854 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____10854.FStar_Syntax_Syntax.n in
                           match uu____10853 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____10866)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____10893 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____10893 with
                                | (a', uu____10903)::bs1 ->
                                    let uu____10923 =
                                      let uu____10924 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____10924
                                        FStar_Pervasives_Native.fst in
                                    let uu____10989 =
                                      let uu____11002 =
                                        let uu____11005 =
                                          let uu____11006 =
                                            let uu____11013 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11013) in
                                          FStar_Syntax_Syntax.NT uu____11006 in
                                        [uu____11005] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11002 in
                                    FStar_All.pipe_right uu____10923
                                      uu____10989)
                           | uu____11028 ->
                               let uu____11029 =
                                 let uu____11034 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11034) in
                               FStar_Errors.raise_error uu____11029 r in
                         let uu____11043 =
                           let uu____11054 =
                             let uu____11059 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11066 =
                               let uu____11067 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11067
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11059 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11066 in
                           match uu____11054 with
                           | (f_sort, g) ->
                               let uu____11088 =
                                 let uu____11095 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11095
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11088, g) in
                         (match uu____11043 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11161 =
                                let uu____11166 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11167 =
                                  let uu____11168 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11168
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11166 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11167 in
                              (match uu____11161 with
                               | (repr, g_repr) ->
                                   let uu____11185 =
                                     let uu____11190 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11191 =
                                       let uu____11192 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11193 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11192 uu____11193 in
                                     pure_wp_uvar uu____11190 repr
                                       uu____11191 r in
                                   (match uu____11185 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11203 =
                                            let uu____11204 =
                                              let uu____11205 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11205] in
                                            let uu____11206 =
                                              let uu____11217 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11217] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11204;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11206;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11203 in
                                        let uu____11250 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11253 =
                                          let uu____11254 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11254 guard_wp in
                                        (uu____11250, uu____11253)))) in
                   match uu____10794 with
                   | (k, g_k) ->
                       ((let uu____11264 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11264
                         then
                           let uu____11265 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11265
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11271 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11271
                          then
                            let uu____11272 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11272
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11277 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11277) in
                          (let uu____11279 =
                             let uu____11280 = FStar_Syntax_Subst.compress k1 in
                             uu____11280.FStar_Syntax_Syntax.n in
                           match uu____11279 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11305 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11305 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11336 =
                                      let uu____11355 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11355
                                        (fun uu____11430 ->
                                           match uu____11430 with
                                           | (l1, l2) ->
                                               let uu____11503 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____11503)) in
                                    (match uu____11336 with
                                     | (bs2, f_b) ->
                                         let env1 =
                                           FStar_TypeChecker_Env.push_binders
                                             env [a] in
                                         validate_layered_effect_binders env1
                                           bs2
                                           [(FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort;
                                           res_t]
                                           check_non_informative_binders r)));
                          (let sub1 =
                             let uu___1226_11576 = sub in
                             let uu____11577 =
                               let uu____11580 =
                                 let uu____11581 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11581) in
                               FStar_Pervasives_Native.Some uu____11580 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1226_11576.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1226_11576.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11577;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____11595 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____11595
                            then
                              let uu____11596 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____11596
                            else ());
                           sub1)))))))))
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env ->
    fun sub ->
      fun r ->
        let check_and_gen1 env1 t k =
          let uu____11629 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Generalize.generalize_universes env1 uu____11629 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____11632 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____11632
        then tc_layered_lift env sub
        else
          (let uu____11634 =
             let uu____11641 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____11641 in
           match uu____11634 with
           | (a, wp_a_src) ->
               let uu____11648 =
                 let uu____11655 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____11655 in
               (match uu____11648 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____11663 =
                        let uu____11666 =
                          let uu____11667 =
                            let uu____11674 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____11674) in
                          FStar_Syntax_Syntax.NT uu____11667 in
                        [uu____11666] in
                      FStar_Syntax_Subst.subst uu____11663 wp_b_tgt in
                    let expected_k =
                      let uu____11682 =
                        let uu____11691 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____11698 =
                          let uu____11707 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____11707] in
                        uu____11691 :: uu____11698 in
                      let uu____11732 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____11682 uu____11732 in
                    let repr_type eff_name a1 wp =
                      (let uu____11754 =
                         let uu____11755 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____11755 in
                       if uu____11754
                       then
                         let uu____11756 =
                           let uu____11761 =
                             let uu____11762 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____11762 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____11761) in
                         let uu____11763 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____11756 uu____11763
                       else ());
                      (let uu____11765 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____11765 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____11797 =
                               let uu____11798 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____11798
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____11797 in
                           let uu____11805 =
                             let uu____11806 =
                               let uu____11823 =
                                 let uu____11834 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____11843 =
                                   let uu____11854 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____11854] in
                                 uu____11834 :: uu____11843 in
                               (repr, uu____11823) in
                             FStar_Syntax_Syntax.Tm_app uu____11806 in
                           let uu____11899 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____11805 uu____11899) in
                    let uu____11900 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12072 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12081 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12081 with
                              | (usubst, uvs1) ->
                                  let uu____12104 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12105 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12104, uu____12105)
                            else (env, lift_wp) in
                          (match uu____12072 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12150 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12150)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12221 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12234 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12234 with
                              | (usubst, uvs) ->
                                  let uu____12259 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12259)
                            else ([], lift) in
                          (match uu____12221 with
                           | (uvs, lift1) ->
                               ((let uu____12294 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12294
                                 then
                                   let uu____12295 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12295
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12298 =
                                   let uu____12305 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12305 lift1 in
                                 match uu____12298 with
                                 | (lift2, comp, uu____12330) ->
                                     let uu____12331 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12331 with
                                      | (uu____12360, lift_wp, lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____12387 =
                                              let uu____12398 =
                                                FStar_TypeChecker_Generalize.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12398 in
                                            let uu____12415 =
                                              FStar_TypeChecker_Generalize.generalize_universes
                                                env lift_wp1 in
                                            (uu____12387, uu____12415)
                                          else
                                            (let uu____12443 =
                                               let uu____12454 =
                                                 let uu____12463 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12463) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12454 in
                                             let uu____12478 =
                                               let uu____12487 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12487) in
                                             (uu____12443, uu____12478)))))) in
                    (match uu____11900 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1310_12551 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1310_12551.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1310_12551.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1310_12551.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1310_12551.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1310_12551.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1310_12551.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1310_12551.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1310_12551.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1310_12551.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1310_12551.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1310_12551.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1310_12551.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1310_12551.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1310_12551.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1310_12551.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1310_12551.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1310_12551.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1310_12551.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1310_12551.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1310_12551.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1310_12551.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1310_12551.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1310_12551.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1310_12551.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1310_12551.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1310_12551.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1310_12551.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1310_12551.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1310_12551.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1310_12551.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1310_12551.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1310_12551.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1310_12551.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1310_12551.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1310_12551.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1310_12551.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1310_12551.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1310_12551.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1310_12551.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1310_12551.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1310_12551.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1310_12551.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1310_12551.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1310_12551.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1310_12551.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1310_12551.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____12583 =
                                 let uu____12588 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____12588 with
                                 | (usubst, uvs1) ->
                                     let uu____12611 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____12612 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____12611, uu____12612) in
                               (match uu____12583 with
                                | (env2, lift2) ->
                                    let uu____12617 =
                                      let uu____12624 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____12624 in
                                    (match uu____12617 with
                                     | (a1, wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1 in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1 in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a in
                                         let repr_f =
                                           repr_type
                                             sub.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp) in
                                           let lift_wp_a =
                                             let uu____12650 =
                                               let uu____12651 =
                                                 let uu____12668 =
                                                   let uu____12679 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____12688 =
                                                     let uu____12699 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____12699] in
                                                   uu____12679 :: uu____12688 in
                                                 (lift_wp1, uu____12668) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____12651 in
                                             let uu____12744 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____12650 uu____12744 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____12748 =
                                             let uu____12757 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____12764 =
                                               let uu____12773 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____12780 =
                                                 let uu____12789 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____12789] in
                                               uu____12773 :: uu____12780 in
                                             uu____12757 :: uu____12764 in
                                           let uu____12820 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____12748 uu____12820 in
                                         let uu____12823 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____12823 with
                                          | (expected_k2, uu____12833,
                                             uu____12834) ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2 in
                                                   let uu____12838 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____12838)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____12846 =
                             let uu____12847 =
                               let uu____12848 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12848
                                 FStar_List.length in
                             uu____12847 <> Prims.int_one in
                           if uu____12846
                           then
                             let uu____12867 =
                               let uu____12872 =
                                 let uu____12873 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12874 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12875 =
                                   let uu____12876 =
                                     let uu____12877 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12877
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12876
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12873 uu____12874 uu____12875 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12872) in
                             FStar_Errors.raise_error uu____12867 r
                           else ());
                          (let uu____12898 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____12900 =
                                  let uu____12901 =
                                    let uu____12904 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____12904
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____12901
                                    FStar_List.length in
                                uu____12900 <> Prims.int_one) in
                           if uu____12898
                           then
                             let uu____12939 =
                               let uu____12944 =
                                 let uu____12945 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12946 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12947 =
                                   let uu____12948 =
                                     let uu____12949 =
                                       let uu____12952 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____12952
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12949
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12948
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12945 uu____12946 uu____12947 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12944) in
                             FStar_Errors.raise_error uu____12939 r
                           else ());
                          (let uu___1347_12988 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1347_12988.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1347_12988.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           })))))
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun uu____13018 ->
      fun r ->
        match uu____13018 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13041 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13065 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13065 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13096 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13096 c in
                     let uu____13105 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13105, uvs1, tps1, c1)) in
            (match uu____13041 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13125 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13125 with
                  | (tps2, c2) ->
                      let uu____13140 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13140 with
                       | (tps3, env3, us) ->
                           let uu____13158 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13158 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13184)::uu____13185 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13204 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13210 =
                                    let uu____13211 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13211 in
                                  if uu____13210
                                  then
                                    let uu____13212 =
                                      let uu____13217 =
                                        let uu____13218 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13219 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13218 uu____13219 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13217) in
                                    FStar_Errors.raise_error uu____13212 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13223 =
                                    let uu____13224 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Generalize.generalize_universes
                                      env0 uu____13224 in
                                  match uu____13223 with
                                  | (uvs2, t) ->
                                      let uu____13253 =
                                        let uu____13258 =
                                          let uu____13271 =
                                            let uu____13272 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13272.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13271) in
                                        match uu____13258 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13287, c5)) -> ([], c5)
                                        | (uu____13329,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13368 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13253 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13396 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13396 with
                                               | (uu____13401, t1) ->
                                                   let uu____13403 =
                                                     let uu____13408 =
                                                       let uu____13409 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13410 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13411 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13409
                                                         uu____13410
                                                         uu____13411 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13408) in
                                                   FStar_Errors.raise_error
                                                     uu____13403 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun ts ->
            let eff_name =
              let uu____13447 =
                let uu____13448 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13448 FStar_Ident.string_of_id in
              let uu____13449 =
                let uu____13450 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13450 FStar_Ident.string_of_id in
              let uu____13451 =
                let uu____13452 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13452 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13447 uu____13449
                uu____13451 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13458 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13458 with
            | (us, t, ty) ->
                let uu____13472 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____13472 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____13485 =
                         let uu____13490 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____13490
                           (fun uu____13507 ->
                              match uu____13507 with
                              | (t1, u) ->
                                  let uu____13518 =
                                    let uu____13519 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____13519
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____13518, u)) in
                       match uu____13485 with
                       | (a, u_a) ->
                           let uu____13526 =
                             let uu____13531 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____13531
                               (fun uu____13548 ->
                                  match uu____13548 with
                                  | (t1, u) ->
                                      let uu____13559 =
                                        let uu____13560 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____13560
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13559, u)) in
                           (match uu____13526 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____13576 =
                                    let uu____13577 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____13577.FStar_Syntax_Syntax.n in
                                  match uu____13576 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____13589) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____13616 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____13616 with
                                       | (a', uu____13626)::(b', uu____13628)::bs1
                                           ->
                                           let uu____13658 =
                                             let uu____13659 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____13659
                                               FStar_Pervasives_Native.fst in
                                           let uu____13724 =
                                             let uu____13737 =
                                               let uu____13740 =
                                                 let uu____13741 =
                                                   let uu____13748 =
                                                     let uu____13751 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____13751
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____13748) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____13741 in
                                               let uu____13764 =
                                                 let uu____13767 =
                                                   let uu____13768 =
                                                     let uu____13775 =
                                                       let uu____13778 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____13778
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____13775) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____13768 in
                                                 [uu____13767] in
                                               uu____13740 :: uu____13764 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____13737 in
                                           FStar_All.pipe_right uu____13658
                                             uu____13724)
                                  | uu____13799 ->
                                      let uu____13800 =
                                        let uu____13805 =
                                          let uu____13806 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____13807 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____13806 uu____13807 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____13805) in
                                      FStar_Errors.raise_error uu____13800 r in
                                let bs = a :: b :: rest_bs in
                                let uu____13837 =
                                  let uu____13848 =
                                    let uu____13853 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____13854 =
                                      let uu____13855 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____13855
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____13853 r m u_a uu____13854 in
                                  match uu____13848 with
                                  | (repr, g) ->
                                      let uu____13876 =
                                        let uu____13883 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____13883
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13876, g) in
                                (match uu____13837 with
                                 | (f, guard_f) ->
                                     let uu____13914 =
                                       let x_a =
                                         let uu____13932 =
                                           let uu____13933 =
                                             let uu____13934 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____13934
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____13933 in
                                         FStar_All.pipe_right uu____13932
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____13949 =
                                         let uu____13954 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____13973 =
                                           let uu____13974 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____13974
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____13954 r n u_b uu____13973 in
                                       match uu____13949 with
                                       | (repr, g) ->
                                           let uu____13995 =
                                             let uu____14002 =
                                               let uu____14003 =
                                                 let uu____14004 =
                                                   let uu____14007 =
                                                     let uu____14010 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14010 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14007 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14004 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14003 in
                                             FStar_All.pipe_right uu____14002
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____13995, g) in
                                     (match uu____13914 with
                                      | (g, guard_g) ->
                                          let uu____14053 =
                                            let uu____14058 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14059 =
                                              let uu____14060 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14060
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14058 r p u_b uu____14059 in
                                          (match uu____14053 with
                                           | (repr, guard_repr) ->
                                               let uu____14075 =
                                                 let uu____14080 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14081 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14080
                                                   repr uu____14081 r in
                                               (match uu____14075 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14091 =
                                                        let uu____14094 =
                                                          let uu____14095 =
                                                            let uu____14096 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14096] in
                                                          let uu____14097 =
                                                            let uu____14108 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14108] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14095;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14097;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14094 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14091 in
                                                    let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 ty1 k in
                                                    (FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1)
                                                       [guard_f;
                                                       guard_g;
                                                       guard_repr;
                                                       g_pure_wp_uvar;
                                                       guard_eq];
                                                     (let uu____14168 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14168
                                                      then
                                                        let uu____14169 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14174 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14169
                                                          uu____14174
                                                      else ());
                                                     (let k1 =
                                                        FStar_All.pipe_right
                                                          k
                                                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                             env1) in
                                                      let check_non_informative_binders
                                                        =
                                                        (FStar_TypeChecker_Env.is_reifiable_effect
                                                           env1 p)
                                                          &&
                                                          (let uu____14183 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14183) in
                                                      (let uu____14185 =
                                                         let uu____14186 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14186.FStar_Syntax_Syntax.n in
                                                       match uu____14185 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14211 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14211
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14255
                                                                  =
                                                                  let uu____14282
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14282
                                                                    (
                                                                    fun
                                                                    uu____14366
                                                                    ->
                                                                    match uu____14366
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14447
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____14474
                                                                    =
                                                                    let uu____14481
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14481
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____14447,
                                                                    uu____14474)) in
                                                                (match uu____14255
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____14596
                                                                    =
                                                                    let uu____14597
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____14597.FStar_Syntax_Syntax.n in
                                                                    match uu____14596
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____14602,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    let env2
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1
                                                                    [a1; b1] in
                                                                    validate_layered_effect_binders
                                                                    env2 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                      (let uu____14646 =
                                                         let uu____14651 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____14651) in
                                                       FStar_Errors.log_issue
                                                         r uu____14646);
                                                      (let uu____14652 =
                                                         let uu____14653 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____14653) in
                                                       ((us1, t),
                                                         uu____14652))))))))))))
let (tc_polymonadic_subcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env0 ->
    fun m ->
      fun n ->
        fun ts ->
          let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
          let combinator_name =
            let uu____14700 =
              let uu____14701 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____14701 FStar_Ident.string_of_id in
            let uu____14702 =
              let uu____14703 =
                let uu____14704 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14704 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____14703 in
            Prims.op_Hat uu____14700 uu____14702 in
          let uu____14705 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____14705 with
          | (us, t, ty) ->
              let uu____14719 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____14719 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____14732 =
                       let uu____14737 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____14737
                         (fun uu____14754 ->
                            match uu____14754 with
                            | (t1, u) ->
                                let uu____14765 =
                                  let uu____14766 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____14766
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____14765, u)) in
                     match uu____14732 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____14782 =
                             let uu____14783 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____14783.FStar_Syntax_Syntax.n in
                           match uu____14782 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____14795)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____14822 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____14822 with
                                | (a', uu____14832)::bs1 ->
                                    let uu____14852 =
                                      let uu____14853 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____14853
                                        FStar_Pervasives_Native.fst in
                                    let uu____14950 =
                                      let uu____14963 =
                                        let uu____14966 =
                                          let uu____14967 =
                                            let uu____14974 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____14974) in
                                          FStar_Syntax_Syntax.NT uu____14967 in
                                        [uu____14966] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____14963 in
                                    FStar_All.pipe_right uu____14852
                                      uu____14950)
                           | uu____14989 ->
                               let uu____14990 =
                                 let uu____14995 =
                                   let uu____14996 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____14997 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____14996 uu____14997 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____14995) in
                               FStar_Errors.raise_error uu____14990 r in
                         let bs = a :: rest_bs in
                         let uu____15021 =
                           let uu____15032 =
                             let uu____15037 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15038 =
                               let uu____15039 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15039
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15037 r m u uu____15038 in
                           match uu____15032 with
                           | (repr, g) ->
                               let uu____15060 =
                                 let uu____15067 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15067
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15060, g) in
                         (match uu____15021 with
                          | (f, guard_f) ->
                              let uu____15098 =
                                let uu____15103 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15104 =
                                  let uu____15105 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15105
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15103 r n u uu____15104 in
                              (match uu____15098 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15120 =
                                     let uu____15125 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15126 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15125 ret_t
                                       uu____15126 r in
                                   (match uu____15120 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15134 =
                                            let uu____15135 =
                                              let uu____15136 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15136] in
                                            let uu____15137 =
                                              let uu____15148 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15148] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15135;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15137;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15134 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15203 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15203
                                          then
                                            let uu____15204 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15204
                                          else ());
                                         (let guard_eq =
                                            FStar_TypeChecker_Rel.teq env ty1
                                              k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env)
                                            [guard_f;
                                            guard_ret_t;
                                            guard_wp;
                                            guard_eq];
                                          (let k1 =
                                             let uu____15211 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15211
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15215 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15215
                                            then
                                              let uu____15216 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15216
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____15224 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____15224) in
                                            (let uu____15226 =
                                               let uu____15227 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____15227.FStar_Syntax_Syntax.n in
                                             match uu____15226 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____15252 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____15252 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____15283 =
                                                        let uu____15302 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____15302
                                                          (fun uu____15377 ->
                                                             match uu____15377
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____15450
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____15450)) in
                                                      (match uu____15283 with
                                                       | (bs3, f_b) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.push_binders
                                                               env [a1] in
                                                           validate_layered_effect_binders
                                                             env1 bs3
                                                             [(FStar_Pervasives_Native.fst
                                                                 f_b).FStar_Syntax_Syntax.sort;
                                                             res_t]
                                                             check_non_informative_binders
                                                             r)));
                                            (let uu____15523 =
                                               let uu____15528 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____15528) in
                                             FStar_Errors.log_issue r
                                               uu____15523);
                                            (let uu____15529 =
                                               let uu____15530 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____15530) in
                                             ((us1, t), uu____15529))))))))))))