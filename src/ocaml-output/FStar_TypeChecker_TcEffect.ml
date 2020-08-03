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
                     let uu____2077 =
                       check_and_gen1 "bind_repr" (Prims.of_int (2))
                         bind_repr_ts in
                     match uu____2077 with
                     | (bind_us, bind_t, bind_ty) ->
                         let uu____2099 =
                           FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                         (match uu____2099 with
                          | (us, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2120 = fresh_a_and_u_a "a" in
                                match uu____2120 with
                                | (a, u_a) ->
                                    let uu____2139 = fresh_a_and_u_a "b" in
                                    (match uu____2139 with
                                     | (b, u_b) ->
                                         let rest_bs =
                                           let uu____2167 =
                                             let uu____2168 =
                                               FStar_Syntax_Subst.compress ty in
                                             uu____2168.FStar_Syntax_Syntax.n in
                                           match uu____2167 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, uu____2180) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____2207 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs in
                                               (match uu____2207 with
                                                | (a', uu____2217)::(b',
                                                                    uu____2219)::bs1
                                                    ->
                                                    let uu____2249 =
                                                      let uu____2250 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (2)))) in
                                                      FStar_All.pipe_right
                                                        uu____2250
                                                        FStar_Pervasives_Native.fst in
                                                    let uu____2315 =
                                                      let uu____2328 =
                                                        let uu____2331 =
                                                          let uu____2332 =
                                                            let uu____2339 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   a) in
                                                            (a', uu____2339) in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____2332 in
                                                        let uu____2346 =
                                                          let uu____2349 =
                                                            let uu____2350 =
                                                              let uu____2357
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  (FStar_Pervasives_Native.fst
                                                                    b) in
                                                              (b',
                                                                uu____2357) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____2350 in
                                                          [uu____2349] in
                                                        uu____2331 ::
                                                          uu____2346 in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____2328 in
                                                    FStar_All.pipe_right
                                                      uu____2249 uu____2315)
                                           | uu____2372 ->
                                               not_an_arrow_error "bind"
                                                 (Prims.of_int (4)) ty r in
                                         let bs = a :: b :: rest_bs in
                                         let uu____2394 =
                                           let uu____2405 =
                                             let uu____2410 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____2411 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____2410 u_a
                                               uu____2411 in
                                           match uu____2405 with
                                           | (repr1, g) ->
                                               let uu____2426 =
                                                 let uu____2433 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____2433
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____2426, g) in
                                         (match uu____2394 with
                                          | (f, guard_f) ->
                                              let uu____2472 =
                                                let x_a = fresh_x_a "x" a in
                                                let uu____2484 =
                                                  let uu____2489 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [x_a]) in
                                                  let uu____2508 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____2489 u_b
                                                    uu____2508 in
                                                match uu____2484 with
                                                | (repr1, g) ->
                                                    let uu____2523 =
                                                      let uu____2530 =
                                                        let uu____2531 =
                                                          let uu____2532 =
                                                            let uu____2535 =
                                                              let uu____2538
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              FStar_Pervasives_Native.Some
                                                                uu____2538 in
                                                            FStar_Syntax_Syntax.mk_Total'
                                                              repr1
                                                              uu____2535 in
                                                          FStar_Syntax_Util.arrow
                                                            [x_a] uu____2532 in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          uu____2531 in
                                                      FStar_All.pipe_right
                                                        uu____2530
                                                        FStar_Syntax_Syntax.mk_binder in
                                                    (uu____2523, g) in
                                              (match uu____2472 with
                                               | (g, guard_g) ->
                                                   let uu____2589 =
                                                     let uu____2594 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env bs in
                                                     let uu____2595 =
                                                       FStar_All.pipe_right
                                                         (FStar_Pervasives_Native.fst
                                                            b)
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     fresh_repr r uu____2594
                                                       u_b uu____2595 in
                                                   (match uu____2589 with
                                                    | (repr1, guard_repr) ->
                                                        let uu____2612 =
                                                          let uu____2617 =
                                                            FStar_TypeChecker_Env.push_binders
                                                              env bs in
                                                          let uu____2618 =
                                                            let uu____2619 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            FStar_Util.format1
                                                              "implicit for pure_wp in checking bind for %s"
                                                              uu____2619 in
                                                          pure_wp_uvar
                                                            uu____2617 repr1
                                                            uu____2618 r in
                                                        (match uu____2612
                                                         with
                                                         | (pure_wp_uvar1,
                                                            g_pure_wp_uvar)
                                                             ->
                                                             let k =
                                                               let uu____2637
                                                                 =
                                                                 let uu____2640
                                                                   =
                                                                   let uu____2641
                                                                    =
                                                                    let uu____2642
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    [uu____2642] in
                                                                   let uu____2643
                                                                    =
                                                                    let uu____2654
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu____2654] in
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2641;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2643;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                   } in
                                                                 FStar_Syntax_Syntax.mk_Comp
                                                                   uu____2640 in
                                                               FStar_Syntax_Util.arrow
                                                                 (FStar_List.append
                                                                    bs 
                                                                    [f; g])
                                                                 uu____2637 in
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
                                                               (let uu____2715
                                                                  =
                                                                  let uu____2716
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    k1 in
                                                                  uu____2716.FStar_Syntax_Syntax.n in
                                                                match uu____2715
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____2741
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____2741
                                                                    with
                                                                    | 
                                                                    (a1::b1::bs2,
                                                                    c1) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                    let uu____2785
                                                                    =
                                                                    let uu____2812
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2812
                                                                    (fun
                                                                    uu____2896
                                                                    ->
                                                                    match uu____2896
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____2977
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____3004
                                                                    =
                                                                    let uu____3011
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____3011
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____2977,
                                                                    uu____3004)) in
                                                                    (match uu____2785
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3126
                                                                    =
                                                                    let uu____3127
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3127.FStar_Syntax_Syntax.n in
                                                                    match uu____3126
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3132,
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
                                                               (let uu____3175
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    k1
                                                                    (
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us) in
                                                                (bind_us,
                                                                  bind_t,
                                                                  uu____3175)))))))))))) in
                   log_combinator "bind_repr" bind_repr;
                   (let stronger_repr =
                      let stronger_repr =
                        let ts =
                          let uu____3210 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_stronger_repr in
                          FStar_All.pipe_right uu____3210 FStar_Util.must in
                        let uu____3225 =
                          let uu____3226 =
                            let uu____3229 =
                              FStar_All.pipe_right ts
                                FStar_Pervasives_Native.snd in
                            FStar_All.pipe_right uu____3229
                              FStar_Syntax_Subst.compress in
                          uu____3226.FStar_Syntax_Syntax.n in
                        match uu____3225 with
                        | FStar_Syntax_Syntax.Tm_unknown ->
                            let signature_ts =
                              let uu____3249 = signature in
                              match uu____3249 with
                              | (us, t, uu____3264) -> (us, t) in
                            let uu____3281 =
                              FStar_TypeChecker_Env.inst_tscheme_with
                                signature_ts [FStar_Syntax_Syntax.U_unknown] in
                            (match uu____3281 with
                             | (uu____3290, signature_t) ->
                                 let uu____3292 =
                                   let uu____3293 =
                                     FStar_Syntax_Subst.compress signature_t in
                                   uu____3293.FStar_Syntax_Syntax.n in
                                 (match uu____3292 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____3301) ->
                                      let bs1 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      let repr_t =
                                        let repr_ts =
                                          let uu____3327 = repr in
                                          match uu____3327 with
                                          | (us, t, uu____3342) -> (us, t) in
                                        let uu____3359 =
                                          FStar_TypeChecker_Env.inst_tscheme_with
                                            repr_ts
                                            [FStar_Syntax_Syntax.U_unknown] in
                                        FStar_All.pipe_right uu____3359
                                          FStar_Pervasives_Native.snd in
                                      let repr_t_applied =
                                        let uu____3373 =
                                          let uu____3374 =
                                            let uu____3391 =
                                              let uu____3402 =
                                                let uu____3405 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst) in
                                                FStar_All.pipe_right
                                                  uu____3405
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name) in
                                              FStar_All.pipe_right uu____3402
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg) in
                                            (repr_t, uu____3391) in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____3374 in
                                        FStar_Syntax_Syntax.mk uu____3373
                                          FStar_Range.dummyRange in
                                      let f_b =
                                        FStar_Syntax_Syntax.null_binder
                                          repr_t_applied in
                                      let uu____3455 =
                                        let uu____3456 =
                                          let uu____3459 =
                                            FStar_All.pipe_right f_b
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____3459
                                            FStar_Syntax_Syntax.bv_to_name in
                                        FStar_Syntax_Util.abs
                                          (FStar_List.append bs1 [f_b])
                                          uu____3456
                                          FStar_Pervasives_Native.None in
                                      ([], uu____3455)
                                  | uu____3488 -> failwith "Impossible!"))
                        | uu____3493 -> ts in
                      let r =
                        (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                      let uu____3495 =
                        check_and_gen1 "stronger_repr" Prims.int_one
                          stronger_repr in
                      match uu____3495 with
                      | (stronger_us, stronger_t, stronger_ty) ->
                          ((let uu____3514 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____3514
                            then
                              let uu____3515 =
                                FStar_Syntax_Print.tscheme_to_string
                                  (stronger_us, stronger_t) in
                              let uu____3520 =
                                FStar_Syntax_Print.tscheme_to_string
                                  (stronger_us, stronger_ty) in
                              FStar_Util.print2
                                "stronger combinator typechecked with term: %s and type: %s\n"
                                uu____3515 uu____3520
                            else ());
                           (let uu____3526 =
                              FStar_Syntax_Subst.open_univ_vars stronger_us
                                stronger_ty in
                            match uu____3526 with
                            | (us, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env ty FStar_Pervasives_Native.None;
                                 (let uu____3543 = fresh_a_and_u_a "a" in
                                  match uu____3543 with
                                  | (a, u) ->
                                      let rest_bs =
                                        let uu____3567 =
                                          let uu____3568 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____3568.FStar_Syntax_Syntax.n in
                                        match uu____3567 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____3580) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (2))
                                            ->
                                            let uu____3607 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____3607 with
                                             | (a', uu____3617)::bs1 ->
                                                 let uu____3637 =
                                                   let uu____3638 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             - Prims.int_one)) in
                                                   FStar_All.pipe_right
                                                     uu____3638
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____3735 =
                                                   let uu____3748 =
                                                     let uu____3751 =
                                                       let uu____3752 =
                                                         let uu____3759 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a) in
                                                         (a', uu____3759) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____3752 in
                                                     [uu____3751] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____3748 in
                                                 FStar_All.pipe_right
                                                   uu____3637 uu____3735)
                                        | uu____3774 ->
                                            not_an_arrow_error "stronger"
                                              (Prims.of_int (2)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____3790 =
                                        let uu____3801 =
                                          let uu____3806 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____3807 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____3806 u
                                            uu____3807 in
                                        match uu____3801 with
                                        | (repr1, g) ->
                                            let uu____3822 =
                                              let uu____3829 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____3829
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____3822, g) in
                                      (match uu____3790 with
                                       | (f, guard_f) ->
                                           let uu____3864 =
                                             let uu____3869 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3870 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3869 u
                                               uu____3870 in
                                           (match uu____3864 with
                                            | (ret_t, guard_ret_t) ->
                                                let uu____3883 =
                                                  let uu____3888 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs in
                                                  let uu____3889 =
                                                    let uu____3890 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname in
                                                    FStar_Util.format1
                                                      "implicit for pure_wp in checking stronger for %s"
                                                      uu____3890 in
                                                  pure_wp_uvar uu____3888
                                                    ret_t uu____3889 r in
                                                (match uu____3883 with
                                                 | (pure_wp_uvar1, guard_wp)
                                                     ->
                                                     let c =
                                                       let uu____3902 =
                                                         let uu____3903 =
                                                           let uu____3904 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               () in
                                                           [uu____3904] in
                                                         let uu____3905 =
                                                           let uu____3916 =
                                                             FStar_All.pipe_right
                                                               pure_wp_uvar1
                                                               FStar_Syntax_Syntax.as_arg in
                                                           [uu____3916] in
                                                         {
                                                           FStar_Syntax_Syntax.comp_univs
                                                             = uu____3903;
                                                           FStar_Syntax_Syntax.effect_name
                                                             =
                                                             FStar_Parser_Const.effect_PURE_lid;
                                                           FStar_Syntax_Syntax.result_typ
                                                             = ret_t;
                                                           FStar_Syntax_Syntax.effect_args
                                                             = uu____3905;
                                                           FStar_Syntax_Syntax.flags
                                                             = []
                                                         } in
                                                       FStar_Syntax_Syntax.mk_Comp
                                                         uu____3902 in
                                                     let k =
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f]) c in
                                                     ((let uu____3971 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffectsTc") in
                                                       if uu____3971
                                                       then
                                                         let uu____3972 =
                                                           FStar_Syntax_Print.term_to_string
                                                             k in
                                                         FStar_Util.print1
                                                           "Expected type of subcomp before unification: %s\n"
                                                           uu____3972
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
                                                          let uu____3977 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          FStar_All.pipe_right
                                                            uu____3977
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env) in
                                                        (let uu____3979 =
                                                           let uu____3980 =
                                                             FStar_Syntax_Subst.compress
                                                               k1 in
                                                           uu____3980.FStar_Syntax_Syntax.n in
                                                         match uu____3979
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (bs1, c1) ->
                                                             let uu____4005 =
                                                               FStar_Syntax_Subst.open_comp
                                                                 bs1 c1 in
                                                             (match uu____4005
                                                              with
                                                              | (a1::bs2, c2)
                                                                  ->
                                                                  let res_t =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                  let uu____4036
                                                                    =
                                                                    let uu____4055
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____4055
                                                                    (fun
                                                                    uu____4130
                                                                    ->
                                                                    match uu____4130
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4203
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4203)) in
                                                                  (match uu____4036
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
                                                        (let uu____4275 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                stronger_us) in
                                                         (stronger_us,
                                                           stronger_t,
                                                           uu____4275)))))))))))) in
                    log_combinator "stronger_repr" stronger_repr;
                    (let if_then_else =
                       let if_then_else_ts =
                         let ts =
                           let uu____4298 =
                             FStar_All.pipe_right ed
                               FStar_Syntax_Util.get_layered_if_then_else_combinator in
                           FStar_All.pipe_right uu____4298 FStar_Util.must in
                         let uu____4309 =
                           let uu____4310 =
                             let uu____4313 =
                               FStar_All.pipe_right ts
                                 FStar_Pervasives_Native.snd in
                             FStar_All.pipe_right uu____4313
                               FStar_Syntax_Subst.compress in
                           uu____4310.FStar_Syntax_Syntax.n in
                         match uu____4309 with
                         | FStar_Syntax_Syntax.Tm_unknown ->
                             let signature_ts =
                               let uu____4325 = signature in
                               match uu____4325 with
                               | (us, t, uu____4340) -> (us, t) in
                             let uu____4357 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 signature_ts [FStar_Syntax_Syntax.U_unknown] in
                             (match uu____4357 with
                              | (uu____4366, signature_t) ->
                                  let uu____4368 =
                                    let uu____4369 =
                                      FStar_Syntax_Subst.compress signature_t in
                                    uu____4369.FStar_Syntax_Syntax.n in
                                  (match uu____4368 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____4377) ->
                                       let bs1 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       let repr_t =
                                         let repr_ts =
                                           let uu____4403 = repr in
                                           match uu____4403 with
                                           | (us, t, uu____4418) -> (us, t) in
                                         let uu____4435 =
                                           FStar_TypeChecker_Env.inst_tscheme_with
                                             repr_ts
                                             [FStar_Syntax_Syntax.U_unknown] in
                                         FStar_All.pipe_right uu____4435
                                           FStar_Pervasives_Native.snd in
                                       let repr_t_applied =
                                         let uu____4449 =
                                           let uu____4450 =
                                             let uu____4467 =
                                               let uu____4478 =
                                                 let uu____4481 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst) in
                                                 FStar_All.pipe_right
                                                   uu____4481
                                                   (FStar_List.map
                                                      FStar_Syntax_Syntax.bv_to_name) in
                                               FStar_All.pipe_right
                                                 uu____4478
                                                 (FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg) in
                                             (repr_t, uu____4467) in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____4450 in
                                         FStar_Syntax_Syntax.mk uu____4449
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
                                       let uu____4533 =
                                         FStar_Syntax_Util.abs
                                           (FStar_List.append bs1
                                              [f_b; g_b; b_b]) repr_t_applied
                                           FStar_Pervasives_Native.None in
                                       ([], uu____4533)
                                   | uu____4564 -> failwith "Impossible!"))
                         | uu____4569 -> ts in
                       let r =
                         (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                       let uu____4573 =
                         check_and_gen1 "if_then_else" Prims.int_one
                           if_then_else_ts in
                       match uu____4573 with
                       | (if_then_else_us, if_then_else_t, if_then_else_ty)
                           ->
                           let uu____4591 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_t in
                           (match uu____4591 with
                            | (us, t) ->
                                let uu____4606 =
                                  FStar_Syntax_Subst.open_univ_vars
                                    if_then_else_us if_then_else_ty in
                                (match uu____4606 with
                                 | (uu____4619, ty) ->
                                     let env =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     (check_no_subtyping_for_layered_combinator
                                        env t
                                        (FStar_Pervasives_Native.Some ty);
                                      (let uu____4623 = fresh_a_and_u_a "a" in
                                       match uu____4623 with
                                       | (a, u_a) ->
                                           let rest_bs =
                                             let uu____4647 =
                                               let uu____4648 =
                                                 FStar_Syntax_Subst.compress
                                                   ty in
                                               uu____4648.FStar_Syntax_Syntax.n in
                                             match uu____4647 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, uu____4660) when
                                                 (FStar_List.length bs) >=
                                                   (Prims.of_int (4))
                                                 ->
                                                 let uu____4687 =
                                                   FStar_Syntax_Subst.open_binders
                                                     bs in
                                                 (match uu____4687 with
                                                  | (a', uu____4697)::bs1 ->
                                                      let uu____4717 =
                                                        let uu____4718 =
                                                          FStar_All.pipe_right
                                                            bs1
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs1)
                                                                  -
                                                                  (Prims.of_int (3)))) in
                                                        FStar_All.pipe_right
                                                          uu____4718
                                                          FStar_Pervasives_Native.fst in
                                                      let uu____4783 =
                                                        let uu____4796 =
                                                          let uu____4799 =
                                                            let uu____4800 =
                                                              let uu____4807
                                                                =
                                                                let uu____4810
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    a
                                                                    FStar_Pervasives_Native.fst in
                                                                FStar_All.pipe_right
                                                                  uu____4810
                                                                  FStar_Syntax_Syntax.bv_to_name in
                                                              (a',
                                                                uu____4807) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____4800 in
                                                          [uu____4799] in
                                                        FStar_Syntax_Subst.subst_binders
                                                          uu____4796 in
                                                      FStar_All.pipe_right
                                                        uu____4717 uu____4783)
                                             | uu____4831 ->
                                                 not_an_arrow_error
                                                   "if_then_else"
                                                   (Prims.of_int (4)) ty r in
                                           let bs = a :: rest_bs in
                                           let uu____4847 =
                                             let uu____4858 =
                                               let uu____4863 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____4864 =
                                                 let uu____4865 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____4865
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____4863 u_a
                                                 uu____4864 in
                                             match uu____4858 with
                                             | (repr1, g) ->
                                                 let uu____4886 =
                                                   let uu____4893 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "f"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____4893
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____4886, g) in
                                           (match uu____4847 with
                                            | (f_bs, guard_f) ->
                                                let uu____4928 =
                                                  let uu____4939 =
                                                    let uu____4944 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env bs in
                                                    let uu____4945 =
                                                      let uu____4946 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_All.pipe_right
                                                        uu____4946
                                                        FStar_Syntax_Syntax.bv_to_name in
                                                    fresh_repr r uu____4944
                                                      u_a uu____4945 in
                                                  match uu____4939 with
                                                  | (repr1, g) ->
                                                      let uu____4967 =
                                                        let uu____4974 =
                                                          FStar_Syntax_Syntax.gen_bv
                                                            "g"
                                                            FStar_Pervasives_Native.None
                                                            repr1 in
                                                        FStar_All.pipe_right
                                                          uu____4974
                                                          FStar_Syntax_Syntax.mk_binder in
                                                      (uu____4967, g) in
                                                (match uu____4928 with
                                                 | (g_bs, guard_g) ->
                                                     let p_b =
                                                       let uu____5016 =
                                                         FStar_Syntax_Syntax.gen_bv
                                                           "p"
                                                           FStar_Pervasives_Native.None
                                                           FStar_Syntax_Util.t_bool in
                                                       FStar_All.pipe_right
                                                         uu____5016
                                                         FStar_Syntax_Syntax.mk_binder in
                                                     let uu____5023 =
                                                       let uu____5028 =
                                                         FStar_TypeChecker_Env.push_binders
                                                           env
                                                           (FStar_List.append
                                                              bs [p_b]) in
                                                       let uu____5047 =
                                                         let uu____5048 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____5048
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       fresh_repr r
                                                         uu____5028 u_a
                                                         uu____5047 in
                                                     (match uu____5023 with
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
                                                            (let uu____5106 =
                                                               let uu____5107
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   k1 in
                                                               uu____5107.FStar_Syntax_Syntax.n in
                                                             match uu____5106
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_abs
                                                                 (bs1, body,
                                                                  uu____5112)
                                                                 ->
                                                                 let uu____5137
                                                                   =
                                                                   FStar_Syntax_Subst.open_term
                                                                    bs1 body in
                                                                 (match uu____5137
                                                                  with
                                                                  | (a1::bs2,
                                                                    body1) ->
                                                                    let uu____5165
                                                                    =
                                                                    let uu____5192
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____5192
                                                                    (fun
                                                                    uu____5276
                                                                    ->
                                                                    match uu____5276
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5357
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5384
                                                                    =
                                                                    let uu____5391
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5391
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5357,
                                                                    uu____5384)) in
                                                                    (match uu____5165
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
                                                            (let uu____5522 =
                                                               FStar_All.pipe_right
                                                                 k1
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    if_then_else_us) in
                                                             (if_then_else_us,
                                                               uu____5522,
                                                               if_then_else_ty))))))))))) in
                     log_combinator "if_then_else" if_then_else;
                     FStar_Errors.with_ctx
                       "While checking if-then-else soundness"
                       (fun uu____5552 ->
                          let r =
                            let uu____5554 =
                              let uu____5557 =
                                let uu____5566 =
                                  FStar_All.pipe_right ed
                                    FStar_Syntax_Util.get_layered_if_then_else_combinator in
                                FStar_All.pipe_right uu____5566
                                  FStar_Util.must in
                              FStar_All.pipe_right uu____5557
                                FStar_Pervasives_Native.snd in
                            uu____5554.FStar_Syntax_Syntax.pos in
                          let binder_aq_to_arg_aq aq =
                            match aq with
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Implicit uu____5609) ->
                                aq
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Meta uu____5610) ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit false)
                            | uu____5611 -> FStar_Pervasives_Native.None in
                          let uu____5614 = if_then_else in
                          match uu____5614 with
                          | (ite_us, ite_t, uu____5625) ->
                              let uu____5630 =
                                FStar_Syntax_Subst.open_univ_vars ite_us
                                  ite_t in
                              (match uu____5630 with
                               | (us, ite_t1) ->
                                   let uu____5637 =
                                     let uu____5654 =
                                       let uu____5655 =
                                         FStar_Syntax_Subst.compress ite_t1 in
                                       uu____5655.FStar_Syntax_Syntax.n in
                                     match uu____5654 with
                                     | FStar_Syntax_Syntax.Tm_abs
                                         (bs, uu____5675, uu____5676) ->
                                         let bs1 =
                                           FStar_Syntax_Subst.open_binders bs in
                                         let uu____5702 =
                                           let uu____5715 =
                                             let uu____5720 =
                                               let uu____5723 =
                                                 let uu____5732 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____5732
                                                   FStar_Pervasives_Native.snd in
                                               FStar_All.pipe_right
                                                 uu____5723
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____5720
                                               (FStar_List.map
                                                  FStar_Syntax_Syntax.bv_to_name) in
                                           FStar_All.pipe_right uu____5715
                                             (fun l ->
                                                let uu____5887 = l in
                                                match uu____5887 with
                                                | f::g::p::[] -> (f, g, p)) in
                                         (match uu____5702 with
                                          | (f, g, p) ->
                                              let uu____5958 =
                                                let uu____5959 =
                                                  FStar_TypeChecker_Env.push_univ_vars
                                                    env0 us in
                                                FStar_TypeChecker_Env.push_binders
                                                  uu____5959 bs1 in
                                              let uu____5960 =
                                                let uu____5961 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       (fun uu____5986 ->
                                                          match uu____5986
                                                          with
                                                          | (b, qual) ->
                                                              let uu____6005
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b in
                                                              (uu____6005,
                                                                (binder_aq_to_arg_aq
                                                                   qual)))) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  ite_t1 uu____5961 r in
                                              (uu____5958, uu____5960, f, g,
                                                p))
                                     | uu____6014 ->
                                         failwith
                                           "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                                   (match uu____5637 with
                                    | (env, ite_t_applied, f_t, g_t, p_t) ->
                                        let uu____6048 =
                                          let uu____6057 = stronger_repr in
                                          match uu____6057 with
                                          | (uu____6074, subcomp_t,
                                             subcomp_ty) ->
                                              let uu____6081 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  us subcomp_t in
                                              (match uu____6081 with
                                               | (uu____6094, subcomp_t1) ->
                                                   let uu____6096 =
                                                     let uu____6107 =
                                                       FStar_Syntax_Subst.open_univ_vars
                                                         us subcomp_ty in
                                                     match uu____6107 with
                                                     | (uu____6122,
                                                        subcomp_ty1) ->
                                                         let uu____6124 =
                                                           let uu____6125 =
                                                             FStar_Syntax_Subst.compress
                                                               subcomp_ty1 in
                                                           uu____6125.FStar_Syntax_Syntax.n in
                                                         (match uu____6124
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,
                                                               uu____6139)
                                                              ->
                                                              let uu____6160
                                                                =
                                                                FStar_All.pipe_right
                                                                  bs
                                                                  (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    Prims.int_one)) in
                                                              (match uu____6160
                                                               with
                                                               | (bs_except_last,
                                                                  last_b) ->
                                                                   let uu____6265
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    bs_except_last
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.snd) in
                                                                   let uu____6292
                                                                    =
                                                                    let uu____6295
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    last_b
                                                                    FStar_List.hd in
                                                                    FStar_All.pipe_right
                                                                    uu____6295
                                                                    FStar_Pervasives_Native.snd in
                                                                   (uu____6265,
                                                                    uu____6292))
                                                          | uu____6338 ->
                                                              failwith
                                                                "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                                   (match uu____6096 with
                                                    | (aqs_except_last,
                                                       last_aq) ->
                                                        let uu____6371 =
                                                          let uu____6382 =
                                                            FStar_All.pipe_right
                                                              aqs_except_last
                                                              (FStar_List.map
                                                                 binder_aq_to_arg_aq) in
                                                          let uu____6399 =
                                                            FStar_All.pipe_right
                                                              last_aq
                                                              binder_aq_to_arg_aq in
                                                          (uu____6382,
                                                            uu____6399) in
                                                        (match uu____6371
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
                                                             let uu____6511 =
                                                               aux f_t in
                                                             let uu____6514 =
                                                               aux g_t in
                                                             (uu____6511,
                                                               uu____6514)))) in
                                        (match uu____6048 with
                                         | (subcomp_f, subcomp_g) ->
                                             let uu____6531 =
                                               let aux t =
                                                 let uu____6548 =
                                                   let uu____6549 =
                                                     let uu____6576 =
                                                       let uu____6593 =
                                                         let uu____6602 =
                                                           FStar_Syntax_Syntax.mk_Total
                                                             ite_t_applied in
                                                         FStar_Util.Inr
                                                           uu____6602 in
                                                       (uu____6593,
                                                         FStar_Pervasives_Native.None) in
                                                     (t, uu____6576,
                                                       FStar_Pervasives_Native.None) in
                                                   FStar_Syntax_Syntax.Tm_ascribed
                                                     uu____6549 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6548 r in
                                               let uu____6643 = aux subcomp_f in
                                               let uu____6644 = aux subcomp_g in
                                               (uu____6643, uu____6644) in
                                             (match uu____6531 with
                                              | (tm_subcomp_ascribed_f,
                                                 tm_subcomp_ascribed_g) ->
                                                  ((let uu____6648 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffectsTc") in
                                                    if uu____6648
                                                    then
                                                      let uu____6649 =
                                                        FStar_Syntax_Print.term_to_string
                                                          tm_subcomp_ascribed_f in
                                                      let uu____6650 =
                                                        FStar_Syntax_Print.term_to_string
                                                          tm_subcomp_ascribed_g in
                                                      FStar_Util.print2
                                                        "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                        uu____6649 uu____6650
                                                    else ());
                                                   (let env1 =
                                                      let uu____6654 =
                                                        let uu____6655 =
                                                          let uu____6656 =
                                                            FStar_All.pipe_right
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            uu____6656 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          uu____6655 in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu____6654 in
                                                    let uu____6659 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env1
                                                        tm_subcomp_ascribed_f in
                                                    match uu____6659 with
                                                    | (uu____6666,
                                                       uu____6667, g_f) ->
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1 g_f);
                                                   (let not_p =
                                                      let uu____6671 =
                                                        let uu____6672 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            FStar_Parser_Const.not_lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None in
                                                        FStar_All.pipe_right
                                                          uu____6672
                                                          FStar_Syntax_Syntax.fv_to_tm in
                                                      let uu____6673 =
                                                        let uu____6674 =
                                                          let uu____6683 =
                                                            FStar_All.pipe_right
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_All.pipe_right
                                                            uu____6683
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____6674] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____6671 uu____6673
                                                        r in
                                                    let env1 =
                                                      let uu____6711 =
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          not_p in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu____6711 in
                                                    let uu____6712 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env1
                                                        tm_subcomp_ascribed_g in
                                                    match uu____6712 with
                                                    | (uu____6719,
                                                       uu____6720, g_g) ->
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
                          (let uu____6742 =
                             let uu____6747 =
                               let uu____6748 =
                                 FStar_Ident.string_of_lid
                                   ed.FStar_Syntax_Syntax.mname in
                               let uu____6749 =
                                 FStar_Ident.string_of_lid
                                   act.FStar_Syntax_Syntax.action_name in
                               let uu____6750 =
                                 FStar_Syntax_Print.binders_to_string "; "
                                   act.FStar_Syntax_Syntax.action_params in
                               FStar_Util.format3
                                 "Action %s:%s has non-empty action params (%s)"
                                 uu____6748 uu____6749 uu____6750 in
                             (FStar_Errors.Fatal_MalformedActionDeclaration,
                               uu____6747) in
                           FStar_Errors.raise_error uu____6742 r)
                        else ();
                        (let uu____6752 =
                           let uu____6757 =
                             FStar_Syntax_Subst.univ_var_opening
                               act.FStar_Syntax_Syntax.action_univs in
                           match uu____6757 with
                           | (usubst, us) ->
                               let uu____6780 =
                                 FStar_TypeChecker_Env.push_univ_vars env us in
                               let uu____6781 =
                                 let uu___653_6782 = act in
                                 let uu____6783 =
                                   FStar_Syntax_Subst.subst usubst
                                     act.FStar_Syntax_Syntax.action_defn in
                                 let uu____6784 =
                                   FStar_Syntax_Subst.subst usubst
                                     act.FStar_Syntax_Syntax.action_typ in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___653_6782.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___653_6782.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs = us;
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___653_6782.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____6783;
                                   FStar_Syntax_Syntax.action_typ =
                                     uu____6784
                                 } in
                               (uu____6780, uu____6781) in
                         match uu____6752 with
                         | (env1, act1) ->
                             let act_typ =
                               let uu____6788 =
                                 let uu____6789 =
                                   FStar_Syntax_Subst.compress
                                     act1.FStar_Syntax_Syntax.action_typ in
                                 uu____6789.FStar_Syntax_Syntax.n in
                               match uu____6788 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                                   let ct =
                                     FStar_Syntax_Util.comp_to_comp_typ c in
                                   let uu____6815 =
                                     FStar_Ident.lid_equals
                                       ct.FStar_Syntax_Syntax.effect_name
                                       ed.FStar_Syntax_Syntax.mname in
                                   if uu____6815
                                   then
                                     let repr_ts =
                                       let uu____6817 = repr in
                                       match uu____6817 with
                                       | (us, t, uu____6832) -> (us, t) in
                                     let repr1 =
                                       let uu____6850 =
                                         FStar_TypeChecker_Env.inst_tscheme_with
                                           repr_ts
                                           ct.FStar_Syntax_Syntax.comp_univs in
                                       FStar_All.pipe_right uu____6850
                                         FStar_Pervasives_Native.snd in
                                     let repr2 =
                                       let uu____6860 =
                                         let uu____6861 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ in
                                         uu____6861 ::
                                           (ct.FStar_Syntax_Syntax.effect_args) in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____6860 r in
                                     let c1 =
                                       let uu____6879 =
                                         let uu____6882 =
                                           FStar_TypeChecker_Env.new_u_univ
                                             () in
                                         FStar_Pervasives_Native.Some
                                           uu____6882 in
                                       FStar_Syntax_Syntax.mk_Total' repr2
                                         uu____6879 in
                                     FStar_Syntax_Util.arrow bs c1
                                   else act1.FStar_Syntax_Syntax.action_typ
                               | uu____6884 ->
                                   act1.FStar_Syntax_Syntax.action_typ in
                             let uu____6885 =
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 env1 act_typ in
                             (match uu____6885 with
                              | (act_typ1, uu____6893, g_t) ->
                                  let uu____6895 =
                                    let uu____6902 =
                                      let uu___678_6903 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env1 act_typ1 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___678_6903.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___678_6903.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___678_6903.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___678_6903.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___678_6903.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___678_6903.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___678_6903.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___678_6903.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___678_6903.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___678_6903.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          = false;
                                        FStar_TypeChecker_Env.effects =
                                          (uu___678_6903.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___678_6903.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___678_6903.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___678_6903.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___678_6903.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___678_6903.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___678_6903.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___678_6903.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___678_6903.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___678_6903.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___678_6903.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___678_6903.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___678_6903.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___678_6903.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___678_6903.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___678_6903.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___678_6903.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___678_6903.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___678_6903.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___678_6903.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___678_6903.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___678_6903.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___678_6903.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___678_6903.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___678_6903.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___678_6903.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___678_6903.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___678_6903.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                      uu____6902
                                      act1.FStar_Syntax_Syntax.action_defn in
                                  (match uu____6895 with
                                   | (act_defn, uu____6905, g_d) ->
                                       ((let uu____6908 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____6908
                                         then
                                           let uu____6909 =
                                             FStar_Syntax_Print.term_to_string
                                               act_defn in
                                           let uu____6910 =
                                             FStar_Syntax_Print.term_to_string
                                               act_typ1 in
                                           FStar_Util.print2
                                             "Typechecked action definition: %s and action type: %s\n"
                                             uu____6909 uu____6910
                                         else ());
                                        (let uu____6912 =
                                           let act_typ2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 act_typ1 in
                                           let uu____6920 =
                                             let uu____6921 =
                                               FStar_Syntax_Subst.compress
                                                 act_typ2 in
                                             uu____6921.FStar_Syntax_Syntax.n in
                                           match uu____6920 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, uu____6931) ->
                                               let bs1 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs in
                                               let env2 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env1 bs1 in
                                               let uu____6954 =
                                                 FStar_Syntax_Util.type_u () in
                                               (match uu____6954 with
                                                | (t, u) ->
                                                    let reason =
                                                      let uu____6968 =
                                                        FStar_Ident.string_of_lid
                                                          ed.FStar_Syntax_Syntax.mname in
                                                      let uu____6969 =
                                                        FStar_Ident.string_of_lid
                                                          act1.FStar_Syntax_Syntax.action_name in
                                                      FStar_Util.format2
                                                        "implicit for return type of action %s:%s"
                                                        uu____6968 uu____6969 in
                                                    let uu____6970 =
                                                      FStar_TypeChecker_Util.new_implicit_var
                                                        reason r env2 t in
                                                    (match uu____6970 with
                                                     | (a_tm, uu____6990,
                                                        g_tm) ->
                                                         let uu____7004 =
                                                           fresh_repr r env2
                                                             u a_tm in
                                                         (match uu____7004
                                                          with
                                                          | (repr1, g) ->
                                                              let uu____7017
                                                                =
                                                                let uu____7020
                                                                  =
                                                                  let uu____7023
                                                                    =
                                                                    let uu____7026
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    FStar_All.pipe_right
                                                                    uu____7026
                                                                    (fun
                                                                    uu____7029
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7029) in
                                                                  FStar_Syntax_Syntax.mk_Total'
                                                                    repr1
                                                                    uu____7023 in
                                                                FStar_Syntax_Util.arrow
                                                                  bs1
                                                                  uu____7020 in
                                                              let uu____7030
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g g_tm in
                                                              (uu____7017,
                                                                uu____7030))))
                                           | uu____7033 ->
                                               let uu____7034 =
                                                 let uu____7039 =
                                                   let uu____7040 =
                                                     FStar_Ident.string_of_lid
                                                       ed.FStar_Syntax_Syntax.mname in
                                                   let uu____7041 =
                                                     FStar_Ident.string_of_lid
                                                       act1.FStar_Syntax_Syntax.action_name in
                                                   let uu____7042 =
                                                     FStar_Syntax_Print.term_to_string
                                                       act_typ2 in
                                                   FStar_Util.format3
                                                     "Unexpected non-function type for action %s:%s (%s)"
                                                     uu____7040 uu____7041
                                                     uu____7042 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____7039) in
                                               FStar_Errors.raise_error
                                                 uu____7034 r in
                                         match uu____6912 with
                                         | (k, g_k) ->
                                             ((let uu____7056 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffectsTc") in
                                               if uu____7056
                                               then
                                                 let uu____7057 =
                                                   FStar_Syntax_Print.term_to_string
                                                     k in
                                                 FStar_Util.print1
                                                   "Expected action type: %s\n"
                                                   uu____7057
                                               else ());
                                              (let g =
                                                 FStar_TypeChecker_Rel.teq
                                                   env1 act_typ1 k in
                                               FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1) [g_t; g_d; g_k; g];
                                               (let uu____7062 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env1)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____7062
                                                then
                                                  let uu____7063 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected action type after unification: %s\n"
                                                    uu____7063
                                                else ());
                                               (let act_typ2 =
                                                  let err_msg t =
                                                    let uu____7072 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname in
                                                    let uu____7073 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name in
                                                    let uu____7074 =
                                                      FStar_Syntax_Print.term_to_string
                                                        t in
                                                    FStar_Util.format3
                                                      "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                      uu____7072 uu____7073
                                                      uu____7074 in
                                                  let repr_args t =
                                                    let uu____7093 =
                                                      let uu____7094 =
                                                        FStar_Syntax_Subst.compress
                                                          t in
                                                      uu____7094.FStar_Syntax_Syntax.n in
                                                    match uu____7093 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (head, a::is) ->
                                                        let uu____7146 =
                                                          let uu____7147 =
                                                            FStar_Syntax_Subst.compress
                                                              head in
                                                          uu____7147.FStar_Syntax_Syntax.n in
                                                        (match uu____7146
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uinst
                                                             (uu____7156, us)
                                                             ->
                                                             (us,
                                                               (FStar_Pervasives_Native.fst
                                                                  a), is)
                                                         | uu____7166 ->
                                                             let uu____7167 =
                                                               let uu____7172
                                                                 = err_msg t in
                                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                 uu____7172) in
                                                             FStar_Errors.raise_error
                                                               uu____7167 r)
                                                    | uu____7179 ->
                                                        let uu____7180 =
                                                          let uu____7185 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7185) in
                                                        FStar_Errors.raise_error
                                                          uu____7180 r in
                                                  let k1 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env1 k in
                                                  let uu____7193 =
                                                    let uu____7194 =
                                                      FStar_Syntax_Subst.compress
                                                        k1 in
                                                    uu____7194.FStar_Syntax_Syntax.n in
                                                  match uu____7193 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs, c) ->
                                                      let uu____7219 =
                                                        FStar_Syntax_Subst.open_comp
                                                          bs c in
                                                      (match uu____7219 with
                                                       | (bs1, c1) ->
                                                           let uu____7226 =
                                                             repr_args
                                                               (FStar_Syntax_Util.comp_result
                                                                  c1) in
                                                           (match uu____7226
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
                                                                let uu____7237
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Comp
                                                                    ct in
                                                                FStar_Syntax_Util.arrow
                                                                  bs1
                                                                  uu____7237))
                                                  | uu____7240 ->
                                                      let uu____7241 =
                                                        let uu____7246 =
                                                          err_msg k1 in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____7246) in
                                                      FStar_Errors.raise_error
                                                        uu____7241 r in
                                                (let uu____7248 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "LayeredEffectsTc") in
                                                 if uu____7248
                                                 then
                                                   let uu____7249 =
                                                     FStar_Syntax_Print.term_to_string
                                                       act_typ2 in
                                                   FStar_Util.print1
                                                     "Action type after injecting it into the monad: %s\n"
                                                     uu____7249
                                                 else ());
                                                (let act2 =
                                                   let uu____7252 =
                                                     FStar_TypeChecker_Generalize.generalize_universes
                                                       env1 act_defn in
                                                   match uu____7252 with
                                                   | (us, act_defn1) ->
                                                       if
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                           = []
                                                       then
                                                         let uu___751_7265 =
                                                           act1 in
                                                         let uu____7266 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us act_typ2 in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___751_7265.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___751_7265.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = us;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___751_7265.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = act_defn1;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____7266
                                                         }
                                                       else
                                                         (let uu____7268 =
                                                            ((FStar_List.length
                                                                us)
                                                               =
                                                               (FStar_List.length
                                                                  act1.FStar_Syntax_Syntax.action_univs))
                                                              &&
                                                              (FStar_List.forall2
                                                                 (fun u1 ->
                                                                    fun u2 ->
                                                                    let uu____7274
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                    uu____7274
                                                                    =
                                                                    Prims.int_zero)
                                                                 us
                                                                 act1.FStar_Syntax_Syntax.action_univs) in
                                                          if uu____7268
                                                          then
                                                            let uu___756_7275
                                                              = act1 in
                                                            let uu____7276 =
                                                              FStar_Syntax_Subst.close_univ_vars
                                                                act1.FStar_Syntax_Syntax.action_univs
                                                                act_typ2 in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___756_7275.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___756_7275.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                =
                                                                (uu___756_7275.FStar_Syntax_Syntax.action_univs);
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___756_7275.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = act_defn1;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____7276
                                                            }
                                                          else
                                                            (let uu____7278 =
                                                               let uu____7283
                                                                 =
                                                                 let uu____7284
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname in
                                                                 let uu____7285
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                 let uu____7286
                                                                   =
                                                                   FStar_Syntax_Print.univ_names_to_string
                                                                    us in
                                                                 let uu____7287
                                                                   =
                                                                   FStar_Syntax_Print.univ_names_to_string
                                                                    act1.FStar_Syntax_Syntax.action_univs in
                                                                 FStar_Util.format4
                                                                   "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                   uu____7284
                                                                   uu____7285
                                                                   uu____7286
                                                                   uu____7287 in
                                                               (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                                 uu____7283) in
                                                             FStar_Errors.raise_error
                                                               uu____7278 r)) in
                                                 act2))))))))) in
                      let tschemes_of uu____7309 =
                        match uu____7309 with
                        | (us, t, ty) -> ((us, t), (us, ty)) in
                      let combinators =
                        let uu____7354 =
                          let uu____7355 = tschemes_of repr in
                          let uu____7360 = tschemes_of return_repr in
                          let uu____7365 = tschemes_of bind_repr in
                          let uu____7370 = tschemes_of stronger_repr in
                          let uu____7375 = tschemes_of if_then_else in
                          {
                            FStar_Syntax_Syntax.l_repr = uu____7355;
                            FStar_Syntax_Syntax.l_return = uu____7360;
                            FStar_Syntax_Syntax.l_bind = uu____7365;
                            FStar_Syntax_Syntax.l_subcomp = uu____7370;
                            FStar_Syntax_Syntax.l_if_then_else = uu____7375
                          } in
                        FStar_Syntax_Syntax.Layered_eff uu____7354 in
                      let uu___765_7380 = ed in
                      let uu____7381 =
                        FStar_List.map (tc_action env0)
                          ed.FStar_Syntax_Syntax.actions in
                      {
                        FStar_Syntax_Syntax.mname =
                          (uu___765_7380.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___765_7380.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.univs =
                          (uu___765_7380.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___765_7380.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (let uu____7388 = signature in
                           match uu____7388 with
                           | (us, t, uu____7403) -> (us, t));
                        FStar_Syntax_Syntax.combinators = combinators;
                        FStar_Syntax_Syntax.actions = uu____7381;
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___765_7380.FStar_Syntax_Syntax.eff_attrs)
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
          let uu____7448 =
            let uu____7449 =
              FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
            FStar_Util.format1 "While checking effect definition `%s`"
              uu____7449 in
          FStar_Errors.with_ctx uu____7448
            (fun uu____7494 ->
               (let uu____7496 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                    (FStar_Options.Other "ED") in
                if uu____7496
                then
                  let uu____7497 =
                    FStar_Syntax_Print.eff_decl_to_string false ed in
                  FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n"
                    uu____7497
                else ());
               (let uu____7499 =
                  let uu____7504 =
                    FStar_Syntax_Subst.univ_var_opening
                      ed.FStar_Syntax_Syntax.univs in
                  match uu____7504 with
                  | (ed_univs_subst, ed_univs) ->
                      let bs =
                        let uu____7528 =
                          FStar_Syntax_Subst.subst_binders ed_univs_subst
                            ed.FStar_Syntax_Syntax.binders in
                        FStar_Syntax_Subst.open_binders uu____7528 in
                      let uu____7529 =
                        let uu____7536 =
                          FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                        FStar_TypeChecker_TcTerm.tc_tparams uu____7536 bs in
                      (match uu____7529 with
                       | (bs1, uu____7542, uu____7543) ->
                           let uu____7544 =
                             let tmp_t =
                               let uu____7554 =
                                 let uu____7557 =
                                   FStar_All.pipe_right
                                     FStar_Syntax_Syntax.U_zero
                                     (fun uu____7562 ->
                                        FStar_Pervasives_Native.Some
                                          uu____7562) in
                                 FStar_Syntax_Syntax.mk_Total'
                                   FStar_Syntax_Syntax.t_unit uu____7557 in
                               FStar_Syntax_Util.arrow bs1 uu____7554 in
                             let uu____7563 =
                               FStar_TypeChecker_Generalize.generalize_universes
                                 env0 tmp_t in
                             match uu____7563 with
                             | (us, tmp_t1) ->
                                 let uu____7580 =
                                   let uu____7581 =
                                     let uu____7582 =
                                       FStar_All.pipe_right tmp_t1
                                         FStar_Syntax_Util.arrow_formals in
                                     FStar_All.pipe_right uu____7582
                                       FStar_Pervasives_Native.fst in
                                   FStar_All.pipe_right uu____7581
                                     FStar_Syntax_Subst.close_binders in
                                 (us, uu____7580) in
                           (match uu____7544 with
                            | (us, bs2) ->
                                (match ed_univs with
                                 | [] -> (us, bs2)
                                 | uu____7619 ->
                                     let uu____7622 =
                                       ((FStar_List.length ed_univs) =
                                          (FStar_List.length us))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1 ->
                                               fun u2 ->
                                                 let uu____7628 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2 in
                                                 uu____7628 = Prims.int_zero)
                                            ed_univs us) in
                                     if uu____7622
                                     then (us, bs2)
                                     else
                                       (let uu____7634 =
                                          let uu____7639 =
                                            let uu____7640 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____7641 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length ed_univs) in
                                            let uu____7642 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length us) in
                                            FStar_Util.format3
                                              "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                              uu____7640 uu____7641
                                              uu____7642 in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____7639) in
                                        let uu____7643 =
                                          FStar_Ident.range_of_lid
                                            ed.FStar_Syntax_Syntax.mname in
                                        FStar_Errors.raise_error uu____7634
                                          uu____7643)))) in
                match uu____7499 with
                | (us, bs) ->
                    let ed1 =
                      let uu___801_7651 = ed in
                      {
                        FStar_Syntax_Syntax.mname =
                          (uu___801_7651.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___801_7651.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.univs = us;
                        FStar_Syntax_Syntax.binders = bs;
                        FStar_Syntax_Syntax.signature =
                          (uu___801_7651.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.combinators =
                          (uu___801_7651.FStar_Syntax_Syntax.combinators);
                        FStar_Syntax_Syntax.actions =
                          (uu___801_7651.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___801_7651.FStar_Syntax_Syntax.eff_attrs)
                      } in
                    let uu____7652 = FStar_Syntax_Subst.univ_var_opening us in
                    (match uu____7652 with
                     | (ed_univs_subst, ed_univs) ->
                         let uu____7671 =
                           let uu____7676 =
                             FStar_Syntax_Subst.subst_binders ed_univs_subst
                               bs in
                           FStar_Syntax_Subst.open_binders' uu____7676 in
                         (match uu____7671 with
                          | (ed_bs, ed_bs_subst) ->
                              let ed2 =
                                let op uu____7697 =
                                  match uu____7697 with
                                  | (us1, t) ->
                                      let t1 =
                                        let uu____7717 =
                                          FStar_Syntax_Subst.shift_subst
                                            ((FStar_List.length ed_bs) +
                                               (FStar_List.length us1))
                                            ed_univs_subst in
                                        FStar_Syntax_Subst.subst uu____7717 t in
                                      let uu____7726 =
                                        let uu____7727 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length us1)
                                            ed_bs_subst in
                                        FStar_Syntax_Subst.subst uu____7727
                                          t1 in
                                      (us1, uu____7726) in
                                let uu___815_7732 = ed1 in
                                let uu____7733 =
                                  op ed1.FStar_Syntax_Syntax.signature in
                                let uu____7734 =
                                  FStar_Syntax_Util.apply_eff_combinators op
                                    ed1.FStar_Syntax_Syntax.combinators in
                                let uu____7735 =
                                  FStar_List.map
                                    (fun a ->
                                       let uu___818_7743 = a in
                                       let uu____7744 =
                                         let uu____7745 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_defn)) in
                                         FStar_Pervasives_Native.snd
                                           uu____7745 in
                                       let uu____7756 =
                                         let uu____7757 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_typ)) in
                                         FStar_Pervasives_Native.snd
                                           uu____7757 in
                                       {
                                         FStar_Syntax_Syntax.action_name =
                                           (uu___818_7743.FStar_Syntax_Syntax.action_name);
                                         FStar_Syntax_Syntax.action_unqualified_name
                                           =
                                           (uu___818_7743.FStar_Syntax_Syntax.action_unqualified_name);
                                         FStar_Syntax_Syntax.action_univs =
                                           (uu___818_7743.FStar_Syntax_Syntax.action_univs);
                                         FStar_Syntax_Syntax.action_params =
                                           (uu___818_7743.FStar_Syntax_Syntax.action_params);
                                         FStar_Syntax_Syntax.action_defn =
                                           uu____7744;
                                         FStar_Syntax_Syntax.action_typ =
                                           uu____7756
                                       }) ed1.FStar_Syntax_Syntax.actions in
                                {
                                  FStar_Syntax_Syntax.mname =
                                    (uu___815_7732.FStar_Syntax_Syntax.mname);
                                  FStar_Syntax_Syntax.cattributes =
                                    (uu___815_7732.FStar_Syntax_Syntax.cattributes);
                                  FStar_Syntax_Syntax.univs =
                                    (uu___815_7732.FStar_Syntax_Syntax.univs);
                                  FStar_Syntax_Syntax.binders =
                                    (uu___815_7732.FStar_Syntax_Syntax.binders);
                                  FStar_Syntax_Syntax.signature = uu____7733;
                                  FStar_Syntax_Syntax.combinators =
                                    uu____7734;
                                  FStar_Syntax_Syntax.actions = uu____7735;
                                  FStar_Syntax_Syntax.eff_attrs =
                                    (uu___815_7732.FStar_Syntax_Syntax.eff_attrs)
                                } in
                              ((let uu____7769 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____7769
                                then
                                  let uu____7770 =
                                    FStar_Syntax_Print.eff_decl_to_string
                                      false ed2 in
                                  FStar_Util.print1
                                    "After typechecking binders eff_decl: \n\t%s\n"
                                    uu____7770
                                else ());
                               (let env =
                                  let uu____7773 =
                                    FStar_TypeChecker_Env.push_univ_vars env0
                                      ed_univs in
                                  FStar_TypeChecker_Env.push_binders
                                    uu____7773 ed_bs in
                                let check_and_gen' comb n env_opt uu____7806
                                  k =
                                  match uu____7806 with
                                  | (us1, t) ->
                                      let env1 =
                                        if FStar_Util.is_some env_opt
                                        then
                                          FStar_All.pipe_right env_opt
                                            FStar_Util.must
                                        else env in
                                      let uu____7822 =
                                        FStar_Syntax_Subst.open_univ_vars us1
                                          t in
                                      (match uu____7822 with
                                       | (us2, t1) ->
                                           let t2 =
                                             match k with
                                             | FStar_Pervasives_Native.Some
                                                 k1 ->
                                                 let uu____7831 =
                                                   FStar_TypeChecker_Env.push_univ_vars
                                                     env1 us2 in
                                                 FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                   uu____7831 t1 k1
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu____7832 =
                                                   let uu____7839 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env1 us2 in
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     uu____7839 t1 in
                                                 (match uu____7832 with
                                                  | (t2, uu____7841, g) ->
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env1 g;
                                                       t2)) in
                                           let uu____7844 =
                                             FStar_TypeChecker_Generalize.generalize_universes
                                               env1 t2 in
                                           (match uu____7844 with
                                            | (g_us, t3) ->
                                                (if
                                                   (FStar_List.length g_us)
                                                     <> n
                                                 then
                                                   (let error =
                                                      let uu____7857 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____7858 =
                                                        FStar_Util.string_of_int
                                                          n in
                                                      let uu____7859 =
                                                        let uu____7860 =
                                                          FStar_All.pipe_right
                                                            g_us
                                                            FStar_List.length in
                                                        FStar_All.pipe_right
                                                          uu____7860
                                                          FStar_Util.string_of_int in
                                                      FStar_Util.format4
                                                        "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                        uu____7857 comb
                                                        uu____7858 uu____7859 in
                                                    FStar_Errors.raise_error
                                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                        error)
                                                      t3.FStar_Syntax_Syntax.pos)
                                                 else ();
                                                 (match us2 with
                                                  | [] -> (g_us, t3)
                                                  | uu____7868 ->
                                                      let uu____7869 =
                                                        ((FStar_List.length
                                                            us2)
                                                           =
                                                           (FStar_List.length
                                                              g_us))
                                                          &&
                                                          (FStar_List.forall2
                                                             (fun u1 ->
                                                                fun u2 ->
                                                                  let uu____7875
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                  uu____7875
                                                                    =
                                                                    Prims.int_zero)
                                                             us2 g_us) in
                                                      if uu____7869
                                                      then (g_us, t3)
                                                      else
                                                        (let uu____7881 =
                                                           let uu____7886 =
                                                             let uu____7887 =
                                                               FStar_Ident.string_of_lid
                                                                 ed2.FStar_Syntax_Syntax.mname in
                                                             let uu____7888 =
                                                               FStar_Util.string_of_int
                                                                 (FStar_List.length
                                                                    us2) in
                                                             let uu____7889 =
                                                               FStar_Util.string_of_int
                                                                 (FStar_List.length
                                                                    g_us) in
                                                             FStar_Util.format4
                                                               "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                               uu____7887
                                                               comb
                                                               uu____7888
                                                               uu____7889 in
                                                           (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                             uu____7886) in
                                                         FStar_Errors.raise_error
                                                           uu____7881
                                                           t3.FStar_Syntax_Syntax.pos))))) in
                                let signature =
                                  check_and_gen' "signature" Prims.int_one
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                    FStar_Pervasives_Native.None in
                                (let uu____7892 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "ED") in
                                 if uu____7892
                                 then
                                   let uu____7893 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       signature in
                                   FStar_Util.print1
                                     "Typechecked signature: %s\n" uu____7893
                                 else ());
                                (let fresh_a_and_wp uu____7906 =
                                   let fail t =
                                     let uu____7919 =
                                       FStar_TypeChecker_Err.unexpected_signature_for_monad
                                         env ed2.FStar_Syntax_Syntax.mname t in
                                     FStar_Errors.raise_error uu____7919
                                       (FStar_Pervasives_Native.snd
                                          ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                                   let uu____7934 =
                                     FStar_TypeChecker_Env.inst_tscheme
                                       signature in
                                   match uu____7934 with
                                   | (uu____7945, signature1) ->
                                       let uu____7947 =
                                         let uu____7948 =
                                           FStar_Syntax_Subst.compress
                                             signature1 in
                                         uu____7948.FStar_Syntax_Syntax.n in
                                       (match uu____7947 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs1, uu____7958) ->
                                            let bs2 =
                                              FStar_Syntax_Subst.open_binders
                                                bs1 in
                                            (match bs2 with
                                             | (a, uu____7987)::(wp,
                                                                 uu____7989)::[]
                                                 ->
                                                 (a,
                                                   (wp.FStar_Syntax_Syntax.sort))
                                             | uu____8018 -> fail signature1)
                                        | uu____8019 -> fail signature1) in
                                 let log_combinator s ts =
                                   let uu____8031 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED") in
                                   if uu____8031
                                   then
                                     let uu____8032 =
                                       FStar_Ident.string_of_lid
                                         ed2.FStar_Syntax_Syntax.mname in
                                     let uu____8033 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         ts in
                                     FStar_Util.print3
                                       "Typechecked %s:%s = %s\n" uu____8032
                                       s uu____8033
                                   else () in
                                 let ret_wp =
                                   let uu____8036 = fresh_a_and_wp () in
                                   match uu____8036 with
                                   | (a, wp_sort) ->
                                       let k =
                                         let uu____8052 =
                                           let uu____8061 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8068 =
                                             let uu____8077 =
                                               let uu____8084 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a in
                                               FStar_Syntax_Syntax.null_binder
                                                 uu____8084 in
                                             [uu____8077] in
                                           uu____8061 :: uu____8068 in
                                         let uu____8103 =
                                           FStar_Syntax_Syntax.mk_GTotal
                                             wp_sort in
                                         FStar_Syntax_Util.arrow uu____8052
                                           uu____8103 in
                                       let uu____8106 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_return_vc_combinator in
                                       check_and_gen' "ret_wp" Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____8106
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "ret_wp" ret_wp;
                                 (let bind_wp =
                                    let uu____8117 = fresh_a_and_wp () in
                                    match uu____8117 with
                                    | (a, wp_sort_a) ->
                                        let uu____8130 = fresh_a_and_wp () in
                                        (match uu____8130 with
                                         | (b, wp_sort_b) ->
                                             let wp_sort_a_b =
                                               let uu____8146 =
                                                 let uu____8155 =
                                                   let uu____8162 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____8162 in
                                                 [uu____8155] in
                                               let uu____8175 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu____8146 uu____8175 in
                                             let k =
                                               let uu____8181 =
                                                 let uu____8190 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_range in
                                                 let uu____8197 =
                                                   let uu____8206 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a in
                                                   let uu____8213 =
                                                     let uu____8222 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         b in
                                                     let uu____8229 =
                                                       let uu____8238 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       let uu____8245 =
                                                         let uu____8254 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a_b in
                                                         [uu____8254] in
                                                       uu____8238 ::
                                                         uu____8245 in
                                                     uu____8222 :: uu____8229 in
                                                   uu____8206 :: uu____8213 in
                                                 uu____8190 :: uu____8197 in
                                               let uu____8297 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu____8181 uu____8297 in
                                             let uu____8300 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_vc_combinator in
                                             check_and_gen' "bind_wp"
                                               (Prims.of_int (2))
                                               FStar_Pervasives_Native.None
                                               uu____8300
                                               (FStar_Pervasives_Native.Some
                                                  k)) in
                                  log_combinator "bind_wp" bind_wp;
                                  (let stronger =
                                     let uu____8311 = fresh_a_and_wp () in
                                     match uu____8311 with
                                     | (a, wp_sort_a) ->
                                         let uu____8324 =
                                           FStar_Syntax_Util.type_u () in
                                         (match uu____8324 with
                                          | (t, uu____8330) ->
                                              let k =
                                                let uu____8334 =
                                                  let uu____8343 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____8350 =
                                                    let uu____8359 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    let uu____8366 =
                                                      let uu____8375 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_sort_a in
                                                      [uu____8375] in
                                                    uu____8359 :: uu____8366 in
                                                  uu____8343 :: uu____8350 in
                                                let uu____8406 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t in
                                                FStar_Syntax_Util.arrow
                                                  uu____8334 uu____8406 in
                                              let uu____8409 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_stronger_vc_combinator in
                                              check_and_gen' "stronger"
                                                Prims.int_one
                                                FStar_Pervasives_Native.None
                                                uu____8409
                                                (FStar_Pervasives_Native.Some
                                                   k)) in
                                   log_combinator "stronger" stronger;
                                   (let if_then_else =
                                      let uu____8420 = fresh_a_and_wp () in
                                      match uu____8420 with
                                      | (a, wp_sort_a) ->
                                          let p =
                                            let uu____8434 =
                                              let uu____8437 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname in
                                              FStar_Pervasives_Native.Some
                                                uu____8437 in
                                            let uu____8438 =
                                              let uu____8439 =
                                                FStar_Syntax_Util.type_u () in
                                              FStar_All.pipe_right uu____8439
                                                FStar_Pervasives_Native.fst in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____8434 uu____8438 in
                                          let k =
                                            let uu____8451 =
                                              let uu____8460 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8467 =
                                                let uu____8476 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    p in
                                                let uu____8483 =
                                                  let uu____8492 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8499 =
                                                    let uu____8508 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    [uu____8508] in
                                                  uu____8492 :: uu____8499 in
                                                uu____8476 :: uu____8483 in
                                              uu____8460 :: uu____8467 in
                                            let uu____8545 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a in
                                            FStar_Syntax_Util.arrow
                                              uu____8451 uu____8545 in
                                          let uu____8548 =
                                            let uu____8553 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                            FStar_All.pipe_right uu____8553
                                              FStar_Util.must in
                                          check_and_gen' "if_then_else"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____8548
                                            (FStar_Pervasives_Native.Some k) in
                                    log_combinator "if_then_else"
                                      if_then_else;
                                    (let ite_wp =
                                       let uu____8582 = fresh_a_and_wp () in
                                       match uu____8582 with
                                       | (a, wp_sort_a) ->
                                           let k =
                                             let uu____8598 =
                                               let uu____8607 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____8614 =
                                                 let uu____8623 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8623] in
                                               uu____8607 :: uu____8614 in
                                             let uu____8648 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a in
                                             FStar_Syntax_Util.arrow
                                               uu____8598 uu____8648 in
                                           let uu____8651 =
                                             let uu____8656 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_wp_ite_combinator in
                                             FStar_All.pipe_right uu____8656
                                               FStar_Util.must in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             uu____8651
                                             (FStar_Pervasives_Native.Some k) in
                                     log_combinator "ite_wp" ite_wp;
                                     (let close_wp =
                                        let uu____8685 = fresh_a_and_wp () in
                                        match uu____8685 with
                                        | (a, wp_sort_a) ->
                                            let b =
                                              let uu____8699 =
                                                let uu____8702 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname in
                                                FStar_Pervasives_Native.Some
                                                  uu____8702 in
                                              let uu____8703 =
                                                let uu____8704 =
                                                  FStar_Syntax_Util.type_u () in
                                                FStar_All.pipe_right
                                                  uu____8704
                                                  FStar_Pervasives_Native.fst in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____8699 uu____8703 in
                                            let wp_sort_b_a =
                                              let uu____8716 =
                                                let uu____8725 =
                                                  let uu____8732 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____8732 in
                                                [uu____8725] in
                                              let uu____8745 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow
                                                uu____8716 uu____8745 in
                                            let k =
                                              let uu____8751 =
                                                let uu____8760 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____8767 =
                                                  let uu____8776 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____8783 =
                                                    let uu____8792 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a in
                                                    [uu____8792] in
                                                  uu____8776 :: uu____8783 in
                                                uu____8760 :: uu____8767 in
                                              let uu____8823 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow
                                                uu____8751 uu____8823 in
                                            let uu____8826 =
                                              let uu____8831 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_wp_close_combinator in
                                              FStar_All.pipe_right uu____8831
                                                FStar_Util.must in
                                            check_and_gen' "close_wp"
                                              (Prims.of_int (2))
                                              FStar_Pervasives_Native.None
                                              uu____8826
                                              (FStar_Pervasives_Native.Some k) in
                                      log_combinator "close_wp" close_wp;
                                      (let trivial =
                                         let uu____8844 = fresh_a_and_wp () in
                                         match uu____8844 with
                                         | (a, wp_sort_a) ->
                                             let uu____8857 =
                                               FStar_Syntax_Util.type_u () in
                                             (match uu____8857 with
                                              | (t, uu____8863) ->
                                                  let k =
                                                    let uu____8867 =
                                                      let uu____8876 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
                                                      let uu____8883 =
                                                        let uu____8892 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            wp_sort_a in
                                                        [uu____8892] in
                                                      uu____8876 ::
                                                        uu____8883 in
                                                    let uu____8917 =
                                                      FStar_Syntax_Syntax.mk_GTotal
                                                        t in
                                                    FStar_Syntax_Util.arrow
                                                      uu____8867 uu____8917 in
                                                  let trivial =
                                                    let uu____8921 =
                                                      let uu____8926 =
                                                        FStar_All.pipe_right
                                                          ed2
                                                          FStar_Syntax_Util.get_wp_trivial_combinator in
                                                      FStar_All.pipe_right
                                                        uu____8926
                                                        FStar_Util.must in
                                                    check_and_gen' "trivial"
                                                      Prims.int_one
                                                      FStar_Pervasives_Native.None
                                                      uu____8921
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
                                                 let uu____9126 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     repr in
                                                 match uu____9126 with
                                                 | (uu____9133, repr1) ->
                                                     let repr2 =
                                                       FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Env.EraseUniverses;
                                                         FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                         env repr1 in
                                                     let uu____9136 =
                                                       let uu____9137 =
                                                         let uu____9154 =
                                                           let uu____9165 =
                                                             FStar_All.pipe_right
                                                               t
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu____9182 =
                                                             let uu____9193 =
                                                               FStar_All.pipe_right
                                                                 wp
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu____9193] in
                                                           uu____9165 ::
                                                             uu____9182 in
                                                         (repr2, uu____9154) in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu____9137 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____9136
                                                       FStar_Range.dummyRange in
                                               let mk_repr a wp =
                                                 let uu____9259 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a in
                                                 mk_repr' uu____9259 wp in
                                               let destruct_repr t =
                                                 let uu____9274 =
                                                   let uu____9275 =
                                                     FStar_Syntax_Subst.compress
                                                       t in
                                                   uu____9275.FStar_Syntax_Syntax.n in
                                                 match uu____9274 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____9286,
                                                      (t1, uu____9288)::
                                                      (wp, uu____9290)::[])
                                                     -> (t1, wp)
                                                 | uu____9349 ->
                                                     failwith
                                                       "Unexpected repr type" in
                                               let return_repr =
                                                 let return_repr_ts =
                                                   let uu____9364 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_return_repr in
                                                   FStar_All.pipe_right
                                                     uu____9364
                                                     FStar_Util.must in
                                                 let uu____9391 =
                                                   fresh_a_and_wp () in
                                                 match uu____9391 with
                                                 | (a, uu____9399) ->
                                                     let x_a =
                                                       let uu____9405 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "x_a"
                                                         FStar_Pervasives_Native.None
                                                         uu____9405 in
                                                     let res =
                                                       let wp =
                                                         let uu____9410 =
                                                           let uu____9411 =
                                                             FStar_TypeChecker_Env.inst_tscheme
                                                               ret_wp in
                                                           FStar_All.pipe_right
                                                             uu____9411
                                                             FStar_Pervasives_Native.snd in
                                                         let uu____9420 =
                                                           let uu____9421 =
                                                             let uu____9430 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_All.pipe_right
                                                               uu____9430
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu____9439 =
                                                             let uu____9450 =
                                                               let uu____9459
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   x_a in
                                                               FStar_All.pipe_right
                                                                 uu____9459
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu____9450] in
                                                           uu____9421 ::
                                                             uu____9439 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____9410
                                                           uu____9420
                                                           FStar_Range.dummyRange in
                                                       mk_repr a wp in
                                                     let k =
                                                       let uu____9495 =
                                                         let uu____9504 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             a in
                                                         let uu____9511 =
                                                           let uu____9520 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____9520] in
                                                         uu____9504 ::
                                                           uu____9511 in
                                                       let uu____9545 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           res in
                                                       FStar_Syntax_Util.arrow
                                                         uu____9495
                                                         uu____9545 in
                                                     let uu____9548 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env k in
                                                     (match uu____9548 with
                                                      | (k1, uu____9556,
                                                         uu____9557) ->
                                                          let env1 =
                                                            let uu____9561 =
                                                              FStar_TypeChecker_Env.set_range
                                                                env
                                                                (FStar_Pervasives_Native.snd
                                                                   return_repr_ts).FStar_Syntax_Syntax.pos in
                                                            FStar_Pervasives_Native.Some
                                                              uu____9561 in
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
                                                    let uu____9571 =
                                                      FStar_All.pipe_right
                                                        ed2
                                                        FStar_Syntax_Util.get_bind_repr in
                                                    FStar_All.pipe_right
                                                      uu____9571
                                                      FStar_Util.must in
                                                  let r =
                                                    let uu____9585 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        FStar_Parser_Const.range_0
                                                        FStar_Syntax_Syntax.delta_constant
                                                        FStar_Pervasives_Native.None in
                                                    FStar_All.pipe_right
                                                      uu____9585
                                                      FStar_Syntax_Syntax.fv_to_tm in
                                                  let uu____9586 =
                                                    fresh_a_and_wp () in
                                                  match uu____9586 with
                                                  | (a, wp_sort_a) ->
                                                      let uu____9599 =
                                                        fresh_a_and_wp () in
                                                      (match uu____9599 with
                                                       | (b, wp_sort_b) ->
                                                           let wp_sort_a_b =
                                                             let uu____9615 =
                                                               let uu____9624
                                                                 =
                                                                 let uu____9631
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____9631 in
                                                               [uu____9624] in
                                                             let uu____9644 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 wp_sort_b in
                                                             FStar_Syntax_Util.arrow
                                                               uu____9615
                                                               uu____9644 in
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
                                                             let uu____9650 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "x_a"
                                                               FStar_Pervasives_Native.None
                                                               uu____9650 in
                                                           let wp_g_x =
                                                             let uu____9652 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_g in
                                                             let uu____9653 =
                                                               let uu____9654
                                                                 =
                                                                 let uu____9663
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    x_a in
                                                                 FStar_All.pipe_right
                                                                   uu____9663
                                                                   FStar_Syntax_Syntax.as_arg in
                                                               [uu____9654] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____9652
                                                               uu____9653
                                                               FStar_Range.dummyRange in
                                                           let res =
                                                             let wp =
                                                               let uu____9692
                                                                 =
                                                                 let uu____9693
                                                                   =
                                                                   FStar_TypeChecker_Env.inst_tscheme
                                                                    bind_wp in
                                                                 FStar_All.pipe_right
                                                                   uu____9693
                                                                   FStar_Pervasives_Native.snd in
                                                               let uu____9702
                                                                 =
                                                                 let uu____9703
                                                                   =
                                                                   let uu____9706
                                                                    =
                                                                    let uu____9709
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                    let uu____9710
                                                                    =
                                                                    let uu____9713
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    let uu____9714
                                                                    =
                                                                    let uu____9717
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____9718
                                                                    =
                                                                    let uu____9721
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____9721] in
                                                                    uu____9717
                                                                    ::
                                                                    uu____9718 in
                                                                    uu____9713
                                                                    ::
                                                                    uu____9714 in
                                                                    uu____9709
                                                                    ::
                                                                    uu____9710 in
                                                                   r ::
                                                                    uu____9706 in
                                                                 FStar_List.map
                                                                   FStar_Syntax_Syntax.as_arg
                                                                   uu____9703 in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____9692
                                                                 uu____9702
                                                                 FStar_Range.dummyRange in
                                                             mk_repr b wp in
                                                           let maybe_range_arg
                                                             =
                                                             let uu____9739 =
                                                               FStar_Util.for_some
                                                                 (FStar_Syntax_Util.attr_eq
                                                                    FStar_Syntax_Util.dm4f_bind_range_attr)
                                                                 ed2.FStar_Syntax_Syntax.eff_attrs in
                                                             if uu____9739
                                                             then
                                                               let uu____9748
                                                                 =
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   FStar_Syntax_Syntax.t_range in
                                                               let uu____9755
                                                                 =
                                                                 let uu____9764
                                                                   =
                                                                   FStar_Syntax_Syntax.null_binder
                                                                    FStar_Syntax_Syntax.t_range in
                                                                 [uu____9764] in
                                                               uu____9748 ::
                                                                 uu____9755
                                                             else [] in
                                                           let k =
                                                             let uu____9799 =
                                                               let uu____9808
                                                                 =
                                                                 let uu____9817
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    a in
                                                                 let uu____9824
                                                                   =
                                                                   let uu____9833
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    b in
                                                                   [uu____9833] in
                                                                 uu____9817
                                                                   ::
                                                                   uu____9824 in
                                                               let uu____9858
                                                                 =
                                                                 let uu____9867
                                                                   =
                                                                   let uu____9876
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_f in
                                                                   let uu____9883
                                                                    =
                                                                    let uu____9892
                                                                    =
                                                                    let uu____9899
                                                                    =
                                                                    let uu____9900
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____9900 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9899 in
                                                                    let uu____9901
                                                                    =
                                                                    let uu____9910
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                    let uu____9917
                                                                    =
                                                                    let uu____9926
                                                                    =
                                                                    let uu____9933
                                                                    =
                                                                    let uu____9934
                                                                    =
                                                                    let uu____9943
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____9943] in
                                                                    let uu____9962
                                                                    =
                                                                    let uu____9965
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____9965 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9934
                                                                    uu____9962 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9933 in
                                                                    [uu____9926] in
                                                                    uu____9910
                                                                    ::
                                                                    uu____9917 in
                                                                    uu____9892
                                                                    ::
                                                                    uu____9901 in
                                                                   uu____9876
                                                                    ::
                                                                    uu____9883 in
                                                                 FStar_List.append
                                                                   maybe_range_arg
                                                                   uu____9867 in
                                                               FStar_List.append
                                                                 uu____9808
                                                                 uu____9858 in
                                                             let uu____10010
                                                               =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 res in
                                                             FStar_Syntax_Util.arrow
                                                               uu____9799
                                                               uu____10010 in
                                                           let uu____10013 =
                                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                               env k in
                                                           (match uu____10013
                                                            with
                                                            | (k1,
                                                               uu____10021,
                                                               uu____10022)
                                                                ->
                                                                let env1 =
                                                                  FStar_TypeChecker_Env.set_range
                                                                    env
                                                                    (FStar_Pervasives_Native.snd
                                                                    bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                                let env2 =
                                                                  FStar_All.pipe_right
                                                                    (
                                                                    let uu___1013_10032
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1013_10032.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    })
                                                                    (
                                                                    fun
                                                                    uu____10033
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10033) in
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
                                                     (let uu____10052 =
                                                        if
                                                          act.FStar_Syntax_Syntax.action_univs
                                                            = []
                                                        then (env, act)
                                                        else
                                                          (let uu____10064 =
                                                             FStar_Syntax_Subst.univ_var_opening
                                                               act.FStar_Syntax_Syntax.action_univs in
                                                           match uu____10064
                                                           with
                                                           | (usubst, uvs) ->
                                                               let uu____10087
                                                                 =
                                                                 FStar_TypeChecker_Env.push_univ_vars
                                                                   env uvs in
                                                               let uu____10088
                                                                 =
                                                                 let uu___1026_10089
                                                                   = act in
                                                                 let uu____10090
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_defn in
                                                                 let uu____10091
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_typ in
                                                                 {
                                                                   FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1026_10089.FStar_Syntax_Syntax.action_name);
                                                                   FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1026_10089.FStar_Syntax_Syntax.action_unqualified_name);
                                                                   FStar_Syntax_Syntax.action_univs
                                                                    = uvs;
                                                                   FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1026_10089.FStar_Syntax_Syntax.action_params);
                                                                   FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____10090;
                                                                   FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____10091
                                                                 } in
                                                               (uu____10087,
                                                                 uu____10088)) in
                                                      match uu____10052 with
                                                      | (env1, act1) ->
                                                          let act_typ =
                                                            let uu____10095 =
                                                              let uu____10096
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  act1.FStar_Syntax_Syntax.action_typ in
                                                              uu____10096.FStar_Syntax_Syntax.n in
                                                            match uu____10095
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_arrow
                                                                (bs1, c) ->
                                                                let c1 =
                                                                  FStar_Syntax_Util.comp_to_comp_typ
                                                                    c in
                                                                let uu____10122
                                                                  =
                                                                  FStar_Ident.lid_equals
                                                                    c1.FStar_Syntax_Syntax.effect_name
                                                                    ed2.FStar_Syntax_Syntax.mname in
                                                                if
                                                                  uu____10122
                                                                then
                                                                  let uu____10123
                                                                    =
                                                                    let uu____10126
                                                                    =
                                                                    let uu____10127
                                                                    =
                                                                    let uu____10128
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____10128 in
                                                                    mk_repr'
                                                                    c1.FStar_Syntax_Syntax.result_typ
                                                                    uu____10127 in
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10126 in
                                                                  FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____10123
                                                                else
                                                                  act1.FStar_Syntax_Syntax.action_typ
                                                            | uu____10150 ->
                                                                act1.FStar_Syntax_Syntax.action_typ in
                                                          let uu____10151 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 act_typ in
                                                          (match uu____10151
                                                           with
                                                           | (act_typ1,
                                                              uu____10159,
                                                              g_t) ->
                                                               let env' =
                                                                 let uu___1043_10162
                                                                   =
                                                                   FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    act_typ1 in
                                                                 {
                                                                   FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.solver);
                                                                   FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.range);
                                                                   FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.curmodule);
                                                                   FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.gamma);
                                                                   FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.gamma_sig);
                                                                   FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.gamma_cache);
                                                                   FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.modules);
                                                                   FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.expected_typ);
                                                                   FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.sigtab);
                                                                   FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.attrtab);
                                                                   FStar_TypeChecker_Env.instantiate_imp
                                                                    = false;
                                                                   FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.effects);
                                                                   FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.generalize);
                                                                   FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.letrecs);
                                                                   FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.top_level);
                                                                   FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.check_uvars);
                                                                   FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.use_eq);
                                                                   FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.use_eq_strict);
                                                                   FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.is_iface);
                                                                   FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.admit);
                                                                   FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.lax);
                                                                   FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.lax_universes);
                                                                   FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.phase1);
                                                                   FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.failhard);
                                                                   FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.nosynth);
                                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.uvar_subtyping);
                                                                   FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.tc_term);
                                                                   FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.type_of);
                                                                   FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.universe_of);
                                                                   FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.check_type_of);
                                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.use_bv_sorts);
                                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.normalized_eff_names);
                                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.fv_delta_depths);
                                                                   FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.proof_ns);
                                                                   FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.synth_hook);
                                                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                   FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.splice);
                                                                   FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.mpreprocess);
                                                                   FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.postprocess);
                                                                   FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.identifier_info);
                                                                   FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.tc_hooks);
                                                                   FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.dsenv);
                                                                   FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.nbe);
                                                                   FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.strict_args_tab);
                                                                   FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.erasable_types_tab);
                                                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1043_10162.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                 } in
                                                               ((let uu____10164
                                                                   =
                                                                   FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                 if
                                                                   uu____10164
                                                                 then
                                                                   let uu____10165
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                   let uu____10166
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                   let uu____10167
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ1 in
                                                                   FStar_Util.print3
                                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                    uu____10165
                                                                    uu____10166
                                                                    uu____10167
                                                                 else ());
                                                                (let uu____10169
                                                                   =
                                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env'
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                 match uu____10169
                                                                 with
                                                                 | (act_defn,
                                                                    uu____10177,
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
                                                                    let uu____10181
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
                                                                    let uu____10217
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10217
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10229)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10236
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10236 in
                                                                    let uu____10239
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10239
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10253,
                                                                    g) ->
                                                                    (k1, g)))
                                                                    | 
                                                                    uu____10257
                                                                    ->
                                                                    let uu____10258
                                                                    =
                                                                    let uu____10263
                                                                    =
                                                                    let uu____10264
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10265
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10264
                                                                    uu____10265 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10263) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10258
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                    (match uu____10181
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
                                                                    let uu____10280
                                                                    =
                                                                    let uu____10281
                                                                    =
                                                                    let uu____10282
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10282 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10281 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10280);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10284
                                                                    =
                                                                    let uu____10285
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10285.FStar_Syntax_Syntax.n in
                                                                    match uu____10284
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10310
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10310
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10317
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10317
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10337
                                                                    =
                                                                    let uu____10338
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10338] in
                                                                    let uu____10339
                                                                    =
                                                                    let uu____10350
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10350] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10337;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10339;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10375
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10375))
                                                                    | 
                                                                    uu____10378
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10379
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10399
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10399)) in
                                                                    match uu____10379
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
                                                                    let uu___1093_10418
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1093_10418.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1093_10418.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1093_10418.FStar_Syntax_Syntax.action_params);
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
                                             let uu____10461 =
                                               FStar_Syntax_Subst.shift_subst
                                                 (FStar_List.length ed_bs)
                                                 ed_univs_closing in
                                             FStar_Syntax_Subst.subst_tscheme
                                               uu____10461 ts1 in
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
                                                 uu____10473 ->
                                                 FStar_Syntax_Syntax.Primitive_eff
                                                   combinators1
                                             | FStar_Syntax_Syntax.DM4F_eff
                                                 uu____10474 ->
                                                 FStar_Syntax_Syntax.DM4F_eff
                                                   combinators1
                                             | uu____10475 ->
                                                 failwith
                                                   "Impossible! tc_eff_decl on a layered effect is not expected" in
                                           let ed3 =
                                             let uu___1113_10477 = ed2 in
                                             let uu____10478 = cl signature in
                                             let uu____10479 =
                                               FStar_List.map
                                                 (fun a ->
                                                    let uu___1116_10487 = a in
                                                    let uu____10488 =
                                                      let uu____10489 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_defn)) in
                                                      FStar_All.pipe_right
                                                        uu____10489
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____10514 =
                                                      let uu____10515 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_typ)) in
                                                      FStar_All.pipe_right
                                                        uu____10515
                                                        FStar_Pervasives_Native.snd in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___1116_10487.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___1116_10487.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        =
                                                        (uu___1116_10487.FStar_Syntax_Syntax.action_univs);
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___1116_10487.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = uu____10488;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____10514
                                                    }) actions in
                                             {
                                               FStar_Syntax_Syntax.mname =
                                                 (uu___1113_10477.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.cattributes
                                                 =
                                                 (uu___1113_10477.FStar_Syntax_Syntax.cattributes);
                                               FStar_Syntax_Syntax.univs =
                                                 (uu___1113_10477.FStar_Syntax_Syntax.univs);
                                               FStar_Syntax_Syntax.binders =
                                                 (uu___1113_10477.FStar_Syntax_Syntax.binders);
                                               FStar_Syntax_Syntax.signature
                                                 = uu____10478;
                                               FStar_Syntax_Syntax.combinators
                                                 = combinators2;
                                               FStar_Syntax_Syntax.actions =
                                                 uu____10479;
                                               FStar_Syntax_Syntax.eff_attrs
                                                 =
                                                 (uu___1113_10477.FStar_Syntax_Syntax.eff_attrs)
                                             } in
                                           ((let uu____10541 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other "ED") in
                                             if uu____10541
                                             then
                                               let uu____10542 =
                                                 FStar_Syntax_Print.eff_decl_to_string
                                                   false ed3 in
                                               FStar_Util.print1
                                                 "Typechecked effect declaration:\n\t%s\n"
                                                 uu____10542
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
          let uu____10572 =
            let uu____10593 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____10593
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____10572 env ed quals attrs
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
        let fail uu____10643 =
          let uu____10644 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____10649 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____10644 uu____10649 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____10693)::(wp, uu____10695)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____10724 -> fail ())
        | uu____10725 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____10737 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____10737
       then
         let uu____10738 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____10738
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____10752 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____10752.FStar_Syntax_Syntax.pos in
       let uu____10761 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____10761 with
       | (us, lift, lift_ty) ->
           ((let uu____10772 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____10772
             then
               let uu____10773 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____10778 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____10773 uu____10778
             else ());
            (let uu____10784 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____10784 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____10799 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____10800 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____10801 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____10799 uu____10800 s uu____10801 in
                   let uu____10802 =
                     let uu____10809 =
                       let uu____10814 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____10814
                         (fun uu____10831 ->
                            match uu____10831 with
                            | (t, u) ->
                                let uu____10842 =
                                  let uu____10843 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____10843
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____10842, u)) in
                     match uu____10809 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____10861 =
                             let uu____10862 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____10862.FStar_Syntax_Syntax.n in
                           match uu____10861 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____10874)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____10901 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____10901 with
                                | (a', uu____10911)::bs1 ->
                                    let uu____10931 =
                                      let uu____10932 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____10932
                                        FStar_Pervasives_Native.fst in
                                    let uu____10997 =
                                      let uu____11010 =
                                        let uu____11013 =
                                          let uu____11014 =
                                            let uu____11021 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11021) in
                                          FStar_Syntax_Syntax.NT uu____11014 in
                                        [uu____11013] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11010 in
                                    FStar_All.pipe_right uu____10931
                                      uu____10997)
                           | uu____11036 ->
                               let uu____11037 =
                                 let uu____11042 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11042) in
                               FStar_Errors.raise_error uu____11037 r in
                         let uu____11051 =
                           let uu____11062 =
                             let uu____11067 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11074 =
                               let uu____11075 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11075
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11067 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11074 in
                           match uu____11062 with
                           | (f_sort, g) ->
                               let uu____11096 =
                                 let uu____11103 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11103
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11096, g) in
                         (match uu____11051 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11169 =
                                let uu____11174 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11175 =
                                  let uu____11176 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11176
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11174 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11175 in
                              (match uu____11169 with
                               | (repr, g_repr) ->
                                   let uu____11193 =
                                     let uu____11198 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11199 =
                                       let uu____11200 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11201 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11200 uu____11201 in
                                     pure_wp_uvar uu____11198 repr
                                       uu____11199 r in
                                   (match uu____11193 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11211 =
                                            let uu____11212 =
                                              let uu____11213 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11213] in
                                            let uu____11214 =
                                              let uu____11225 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11225] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11212;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11214;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11211 in
                                        let uu____11258 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11261 =
                                          let uu____11262 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11262 guard_wp in
                                        (uu____11258, uu____11261)))) in
                   match uu____10802 with
                   | (k, g_k) ->
                       ((let uu____11272 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11272
                         then
                           let uu____11273 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11273
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11279 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11279
                          then
                            let uu____11280 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11280
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11285 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11285) in
                          (let uu____11287 =
                             let uu____11288 = FStar_Syntax_Subst.compress k1 in
                             uu____11288.FStar_Syntax_Syntax.n in
                           match uu____11287 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11313 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11313 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11344 =
                                      let uu____11363 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11363
                                        (fun uu____11438 ->
                                           match uu____11438 with
                                           | (l1, l2) ->
                                               let uu____11511 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____11511)) in
                                    (match uu____11344 with
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
                             let uu___1226_11584 = sub in
                             let uu____11585 =
                               let uu____11588 =
                                 let uu____11589 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11589) in
                               FStar_Pervasives_Native.Some uu____11588 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1226_11584.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1226_11584.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11585;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____11603 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____11603
                            then
                              let uu____11604 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____11604
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
          let uu____11637 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Generalize.generalize_universes env1 uu____11637 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____11640 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____11640
        then tc_layered_lift env sub
        else
          (let uu____11642 =
             let uu____11649 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____11649 in
           match uu____11642 with
           | (a, wp_a_src) ->
               let uu____11656 =
                 let uu____11663 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____11663 in
               (match uu____11656 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____11671 =
                        let uu____11674 =
                          let uu____11675 =
                            let uu____11682 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____11682) in
                          FStar_Syntax_Syntax.NT uu____11675 in
                        [uu____11674] in
                      FStar_Syntax_Subst.subst uu____11671 wp_b_tgt in
                    let expected_k =
                      let uu____11690 =
                        let uu____11699 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____11706 =
                          let uu____11715 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____11715] in
                        uu____11699 :: uu____11706 in
                      let uu____11740 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____11690 uu____11740 in
                    let repr_type eff_name a1 wp =
                      (let uu____11762 =
                         let uu____11763 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____11763 in
                       if uu____11762
                       then
                         let uu____11764 =
                           let uu____11769 =
                             let uu____11770 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____11770 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____11769) in
                         let uu____11771 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____11764 uu____11771
                       else ());
                      (let uu____11773 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____11773 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____11805 =
                               let uu____11806 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____11806
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____11805 in
                           let uu____11813 =
                             let uu____11814 =
                               let uu____11831 =
                                 let uu____11842 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____11851 =
                                   let uu____11862 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____11862] in
                                 uu____11842 :: uu____11851 in
                               (repr, uu____11831) in
                             FStar_Syntax_Syntax.Tm_app uu____11814 in
                           let uu____11907 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____11813 uu____11907) in
                    let uu____11908 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12080 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12089 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12089 with
                              | (usubst, uvs1) ->
                                  let uu____12112 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12113 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12112, uu____12113)
                            else (env, lift_wp) in
                          (match uu____12080 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12158 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12158)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12229 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12242 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12242 with
                              | (usubst, uvs) ->
                                  let uu____12267 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12267)
                            else ([], lift) in
                          (match uu____12229 with
                           | (uvs, lift1) ->
                               ((let uu____12302 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12302
                                 then
                                   let uu____12303 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12303
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12306 =
                                   let uu____12313 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12313 lift1 in
                                 match uu____12306 with
                                 | (lift2, comp, uu____12338) ->
                                     let uu____12339 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12339 with
                                      | (uu____12368, lift_wp, lift_elab) ->
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
                                            let uu____12395 =
                                              let uu____12406 =
                                                FStar_TypeChecker_Generalize.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12406 in
                                            let uu____12423 =
                                              FStar_TypeChecker_Generalize.generalize_universes
                                                env lift_wp1 in
                                            (uu____12395, uu____12423)
                                          else
                                            (let uu____12451 =
                                               let uu____12462 =
                                                 let uu____12471 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12471) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12462 in
                                             let uu____12486 =
                                               let uu____12495 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12495) in
                                             (uu____12451, uu____12486)))))) in
                    (match uu____11908 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1310_12559 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1310_12559.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1310_12559.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1310_12559.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1310_12559.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1310_12559.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1310_12559.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1310_12559.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1310_12559.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1310_12559.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1310_12559.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1310_12559.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1310_12559.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1310_12559.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1310_12559.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1310_12559.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1310_12559.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1310_12559.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1310_12559.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1310_12559.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1310_12559.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1310_12559.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1310_12559.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1310_12559.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1310_12559.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1310_12559.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1310_12559.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1310_12559.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1310_12559.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1310_12559.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1310_12559.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1310_12559.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1310_12559.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1310_12559.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1310_12559.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1310_12559.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1310_12559.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1310_12559.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1310_12559.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1310_12559.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1310_12559.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1310_12559.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1310_12559.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1310_12559.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1310_12559.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1310_12559.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1310_12559.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____12591 =
                                 let uu____12596 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____12596 with
                                 | (usubst, uvs1) ->
                                     let uu____12619 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____12620 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____12619, uu____12620) in
                               (match uu____12591 with
                                | (env2, lift2) ->
                                    let uu____12625 =
                                      let uu____12632 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____12632 in
                                    (match uu____12625 with
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
                                             let uu____12658 =
                                               let uu____12659 =
                                                 let uu____12676 =
                                                   let uu____12687 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____12696 =
                                                     let uu____12707 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____12707] in
                                                   uu____12687 :: uu____12696 in
                                                 (lift_wp1, uu____12676) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____12659 in
                                             let uu____12752 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____12658 uu____12752 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____12756 =
                                             let uu____12765 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____12772 =
                                               let uu____12781 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____12788 =
                                                 let uu____12797 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____12797] in
                                               uu____12781 :: uu____12788 in
                                             uu____12765 :: uu____12772 in
                                           let uu____12828 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____12756 uu____12828 in
                                         let uu____12831 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____12831 with
                                          | (expected_k2, uu____12841,
                                             uu____12842) ->
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
                                                   let uu____12846 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____12846)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____12854 =
                             let uu____12855 =
                               let uu____12856 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12856
                                 FStar_List.length in
                             uu____12855 <> Prims.int_one in
                           if uu____12854
                           then
                             let uu____12875 =
                               let uu____12880 =
                                 let uu____12881 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12882 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12883 =
                                   let uu____12884 =
                                     let uu____12885 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12885
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12884
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12881 uu____12882 uu____12883 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12880) in
                             FStar_Errors.raise_error uu____12875 r
                           else ());
                          (let uu____12906 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____12908 =
                                  let uu____12909 =
                                    let uu____12912 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____12912
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____12909
                                    FStar_List.length in
                                uu____12908 <> Prims.int_one) in
                           if uu____12906
                           then
                             let uu____12947 =
                               let uu____12952 =
                                 let uu____12953 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12954 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12955 =
                                   let uu____12956 =
                                     let uu____12957 =
                                       let uu____12960 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____12960
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12957
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12956
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12953 uu____12954 uu____12955 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12952) in
                             FStar_Errors.raise_error uu____12947 r
                           else ());
                          (let uu___1347_12996 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1347_12996.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1347_12996.FStar_Syntax_Syntax.target);
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
    fun uu____13026 ->
      fun r ->
        match uu____13026 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13049 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13073 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13073 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13104 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13104 c in
                     let uu____13113 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13113, uvs1, tps1, c1)) in
            (match uu____13049 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13133 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13133 with
                  | (tps2, c2) ->
                      let uu____13148 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13148 with
                       | (tps3, env3, us) ->
                           let uu____13166 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13166 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13192)::uu____13193 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13212 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13218 =
                                    let uu____13219 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13219 in
                                  if uu____13218
                                  then
                                    let uu____13220 =
                                      let uu____13225 =
                                        let uu____13226 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13227 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13226 uu____13227 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13225) in
                                    FStar_Errors.raise_error uu____13220 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13231 =
                                    let uu____13232 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Generalize.generalize_universes
                                      env0 uu____13232 in
                                  match uu____13231 with
                                  | (uvs2, t) ->
                                      let uu____13261 =
                                        let uu____13266 =
                                          let uu____13279 =
                                            let uu____13280 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13280.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13279) in
                                        match uu____13266 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13295, c5)) -> ([], c5)
                                        | (uu____13337,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13376 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13261 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13404 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13404 with
                                               | (uu____13409, t1) ->
                                                   let uu____13411 =
                                                     let uu____13416 =
                                                       let uu____13417 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13418 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13419 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13417
                                                         uu____13418
                                                         uu____13419 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13416) in
                                                   FStar_Errors.raise_error
                                                     uu____13411 r)
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
              let uu____13455 =
                let uu____13456 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13456 FStar_Ident.string_of_id in
              let uu____13457 =
                let uu____13458 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13458 FStar_Ident.string_of_id in
              let uu____13459 =
                let uu____13460 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13460 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13455 uu____13457
                uu____13459 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13466 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13466 with
            | (us, t, ty) ->
                let uu____13480 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____13480 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____13493 =
                         let uu____13498 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____13498
                           (fun uu____13515 ->
                              match uu____13515 with
                              | (t1, u) ->
                                  let uu____13526 =
                                    let uu____13527 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____13527
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____13526, u)) in
                       match uu____13493 with
                       | (a, u_a) ->
                           let uu____13534 =
                             let uu____13539 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____13539
                               (fun uu____13556 ->
                                  match uu____13556 with
                                  | (t1, u) ->
                                      let uu____13567 =
                                        let uu____13568 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____13568
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13567, u)) in
                           (match uu____13534 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____13584 =
                                    let uu____13585 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____13585.FStar_Syntax_Syntax.n in
                                  match uu____13584 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____13597) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____13624 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____13624 with
                                       | (a', uu____13634)::(b', uu____13636)::bs1
                                           ->
                                           let uu____13666 =
                                             let uu____13667 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____13667
                                               FStar_Pervasives_Native.fst in
                                           let uu____13764 =
                                             let uu____13777 =
                                               let uu____13780 =
                                                 let uu____13781 =
                                                   let uu____13788 =
                                                     let uu____13791 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____13791
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____13788) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____13781 in
                                               let uu____13804 =
                                                 let uu____13807 =
                                                   let uu____13808 =
                                                     let uu____13815 =
                                                       let uu____13818 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____13818
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____13815) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____13808 in
                                                 [uu____13807] in
                                               uu____13780 :: uu____13804 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____13777 in
                                           FStar_All.pipe_right uu____13666
                                             uu____13764)
                                  | uu____13839 ->
                                      let uu____13840 =
                                        let uu____13845 =
                                          let uu____13846 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____13847 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____13846 uu____13847 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____13845) in
                                      FStar_Errors.raise_error uu____13840 r in
                                let bs = a :: b :: rest_bs in
                                let uu____13877 =
                                  let uu____13888 =
                                    let uu____13893 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____13894 =
                                      let uu____13895 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____13895
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____13893 r m u_a uu____13894 in
                                  match uu____13888 with
                                  | (repr, g) ->
                                      let uu____13916 =
                                        let uu____13923 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____13923
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13916, g) in
                                (match uu____13877 with
                                 | (f, guard_f) ->
                                     let uu____13954 =
                                       let x_a =
                                         let uu____13972 =
                                           let uu____13973 =
                                             let uu____13974 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____13974
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____13973 in
                                         FStar_All.pipe_right uu____13972
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____13989 =
                                         let uu____13994 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14013 =
                                           let uu____14014 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14014
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____13994 r n u_b uu____14013 in
                                       match uu____13989 with
                                       | (repr, g) ->
                                           let uu____14035 =
                                             let uu____14042 =
                                               let uu____14043 =
                                                 let uu____14044 =
                                                   let uu____14047 =
                                                     let uu____14050 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14050 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14047 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14044 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14043 in
                                             FStar_All.pipe_right uu____14042
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14035, g) in
                                     (match uu____13954 with
                                      | (g, guard_g) ->
                                          let uu____14093 =
                                            let uu____14098 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14099 =
                                              let uu____14100 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14100
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14098 r p u_b uu____14099 in
                                          (match uu____14093 with
                                           | (repr, guard_repr) ->
                                               let uu____14115 =
                                                 let uu____14120 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14121 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14120
                                                   repr uu____14121 r in
                                               (match uu____14115 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14131 =
                                                        let uu____14134 =
                                                          let uu____14135 =
                                                            let uu____14136 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14136] in
                                                          let uu____14137 =
                                                            let uu____14148 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14148] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14135;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14137;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14134 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14131 in
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
                                                     (let uu____14208 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14208
                                                      then
                                                        let uu____14209 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14214 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14209
                                                          uu____14214
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
                                                          (let uu____14223 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14223) in
                                                      (let uu____14225 =
                                                         let uu____14226 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14226.FStar_Syntax_Syntax.n in
                                                       match uu____14225 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14251 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14251
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14295
                                                                  =
                                                                  let uu____14322
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14322
                                                                    (
                                                                    fun
                                                                    uu____14406
                                                                    ->
                                                                    match uu____14406
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14487
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____14514
                                                                    =
                                                                    let uu____14521
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14521
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____14487,
                                                                    uu____14514)) in
                                                                (match uu____14295
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____14636
                                                                    =
                                                                    let uu____14637
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____14637.FStar_Syntax_Syntax.n in
                                                                    match uu____14636
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____14642,
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
                                                      (let uu____14686 =
                                                         let uu____14691 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____14691) in
                                                       FStar_Errors.log_issue
                                                         r uu____14686);
                                                      (let uu____14692 =
                                                         let uu____14693 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____14693) in
                                                       ((us1, t),
                                                         uu____14692))))))))))))
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
            let uu____14740 =
              let uu____14741 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____14741 FStar_Ident.string_of_id in
            let uu____14742 =
              let uu____14743 =
                let uu____14744 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14744 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____14743 in
            Prims.op_Hat uu____14740 uu____14742 in
          let uu____14745 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____14745 with
          | (us, t, ty) ->
              let uu____14759 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____14759 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____14772 =
                       let uu____14777 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____14777
                         (fun uu____14794 ->
                            match uu____14794 with
                            | (t1, u) ->
                                let uu____14805 =
                                  let uu____14806 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____14806
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____14805, u)) in
                     match uu____14772 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____14822 =
                             let uu____14823 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____14823.FStar_Syntax_Syntax.n in
                           match uu____14822 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____14835)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____14862 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____14862 with
                                | (a', uu____14872)::bs1 ->
                                    let uu____14892 =
                                      let uu____14893 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____14893
                                        FStar_Pervasives_Native.fst in
                                    let uu____14958 =
                                      let uu____14971 =
                                        let uu____14974 =
                                          let uu____14975 =
                                            let uu____14982 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____14982) in
                                          FStar_Syntax_Syntax.NT uu____14975 in
                                        [uu____14974] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____14971 in
                                    FStar_All.pipe_right uu____14892
                                      uu____14958)
                           | uu____14997 ->
                               let uu____14998 =
                                 let uu____15003 =
                                   let uu____15004 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15005 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15004 uu____15005 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15003) in
                               FStar_Errors.raise_error uu____14998 r in
                         let bs = a :: rest_bs in
                         let uu____15029 =
                           let uu____15040 =
                             let uu____15045 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15046 =
                               let uu____15047 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15047
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15045 r m u uu____15046 in
                           match uu____15040 with
                           | (repr, g) ->
                               let uu____15068 =
                                 let uu____15075 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15075
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15068, g) in
                         (match uu____15029 with
                          | (f, guard_f) ->
                              let uu____15106 =
                                let uu____15111 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15112 =
                                  let uu____15113 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15113
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15111 r n u uu____15112 in
                              (match uu____15106 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15128 =
                                     let uu____15133 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15134 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15133 ret_t
                                       uu____15134 r in
                                   (match uu____15128 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15142 =
                                            let uu____15143 =
                                              let uu____15144 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15144] in
                                            let uu____15145 =
                                              let uu____15156 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15156] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15143;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15145;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15142 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15211 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15211
                                          then
                                            let uu____15212 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15212
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
                                             let uu____15219 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15219
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15223 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15223
                                            then
                                              let uu____15224 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15224
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____15232 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____15232) in
                                            (let uu____15234 =
                                               let uu____15235 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____15235.FStar_Syntax_Syntax.n in
                                             match uu____15234 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____15260 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____15260 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____15291 =
                                                        let uu____15310 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____15310
                                                          (fun uu____15385 ->
                                                             match uu____15385
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____15458
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____15458)) in
                                                      (match uu____15291 with
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
                                            (let uu____15531 =
                                               let uu____15536 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____15536) in
                                             FStar_Errors.log_issue r
                                               uu____15531);
                                            (let uu____15537 =
                                               let uu____15538 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____15538) in
                                             ((us1, t), uu____15537))))))))))))