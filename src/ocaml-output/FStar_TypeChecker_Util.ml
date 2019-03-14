open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____60631 = FStar_TypeChecker_Env.get_range env  in
      let uu____60632 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____60631 uu____60632
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____60693 =
          let uu____60695 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____60695  in
        if uu____60693
        then g
        else
          (let uu____60702 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____60754  ->
                     match uu____60754 with
                     | (uu____60761,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____60702 with
           | (solve_now,defer) ->
               ((let uu____60796 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____60796
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____60813  ->
                         match uu____60813 with
                         | (s,p) ->
                             let uu____60823 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60823)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____60838  ->
                         match uu____60838 with
                         | (s,p) ->
                             let uu____60848 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60848)
                      defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___631_60856 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___631_60856.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___631_60856.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___631_60856.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___634_60858 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___634_60858.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___634_60858.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___634_60858.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____60873 =
        let uu____60875 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____60875  in
      if uu____60873
      then
        let us =
          let uu____60880 =
            let uu____60884 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____60884
             in
          FStar_All.pipe_right uu____60880 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____60903 =
            let uu____60909 =
              let uu____60911 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____60911
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____60909)  in
          FStar_Errors.log_issue r uu____60903);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____60934  ->
      match uu____60934 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____60945;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____60947;
          FStar_Syntax_Syntax.lbpos = uu____60948;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____60983 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____60983 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____61021) ->
                          aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____61028)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____61083) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____61119 = FStar_Options.ml_ish ()  in
                                if uu____61119
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____61141 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____61141
                            then
                              let uu____61144 = FStar_Range.string_of_range r
                                 in
                              let uu____61146 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____61144 uu____61146
                            else ());
                           FStar_Util.Inl t2)
                      | uu____61151 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____61153 = aux e1  in
                      match uu____61153 with
                      | FStar_Util.Inr c ->
                          let uu____61159 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____61159
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____61164 =
                               let uu____61170 =
                                 let uu____61172 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____61172
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____61170)
                                in
                             FStar_Errors.raise_error uu____61164 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____61181 ->
               let uu____61182 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____61182 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____61246 =
      match uu____61246 with
      | (p,i) ->
          let uu____61266 = decorated_pattern_as_term p  in
          (match uu____61266 with
           | (vars,te) ->
               let uu____61289 =
                 let uu____61294 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____61294)  in
               (vars, uu____61289))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____61308 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____61308)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____61312 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61312)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____61316 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61316)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____61339 =
          let uu____61358 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____61358 FStar_List.unzip  in
        (match uu____61339 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____61496 =
               let uu____61497 =
                 let uu____61498 =
                   let uu____61515 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____61515, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____61498  in
               mk1 uu____61497  in
             (vars1, uu____61496))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____61554,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____61564,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____61578 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____61589 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____61589 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____61618)::[] -> wp
      | uu____61643 ->
          let uu____61654 =
            let uu____61656 =
              let uu____61658 =
                FStar_List.map
                  (fun uu____61672  ->
                     match uu____61672 with
                     | (x,uu____61681) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____61658 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____61656
             in
          failwith uu____61654
       in
    let uu____61692 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____61692, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____61709 = destruct_comp c  in
        match uu____61709 with
        | (u,uu____61717,wp) ->
            let uu____61719 =
              let uu____61730 =
                let uu____61739 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____61739  in
              [uu____61730]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____61719;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____61772 =
          let uu____61779 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____61780 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____61779 uu____61780  in
        match uu____61772 with | (m,uu____61782,uu____61783) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____61800 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____61800
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe *
          FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) *
          (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.typ)))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____61847 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____61847 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____61884 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____61884 with
             | (a,kwp) ->
                 let uu____61915 = destruct_comp m1  in
                 let uu____61922 = destruct_comp m2  in
                 ((md, a, kwp), uu____61915, uu____61922))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____62007 =
              let uu____62008 =
                let uu____62019 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____62019]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____62008;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____62007
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          let uu____62103 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____62103
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____62119 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        uu____62119 lc.FStar_Syntax_Syntax.cflags
        (fun uu____62122  ->
           let uu____62123 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____62123)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____62131 =
      let uu____62132 = FStar_Syntax_Subst.compress t  in
      uu____62132.FStar_Syntax_Syntax.n  in
    match uu____62131 with
    | FStar_Syntax_Syntax.Tm_arrow uu____62136 -> true
    | uu____62152 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____62222 =
                let uu____62224 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____62224  in
              if uu____62222
              then f
              else (let uu____62231 = reason1 ()  in label uu____62231 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___828_62252 = g  in
            let uu____62253 =
              let uu____62254 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____62254  in
            {
              FStar_TypeChecker_Env.guard_f = uu____62253;
              FStar_TypeChecker_Env.deferred =
                (uu___828_62252.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___828_62252.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___828_62252.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____62275 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62275
        then c
        else
          (let uu____62280 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____62280
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____62342 = FStar_Syntax_Syntax.mk_binder x
                            in
                         [uu____62342]  in
                       let us =
                         let uu____62364 =
                           let uu____62367 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____62367]  in
                         u_res :: uu____62364  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____62373 =
                         let uu____62378 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____62379 =
                           let uu____62380 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____62389 =
                             let uu____62400 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____62409 =
                               let uu____62420 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____62420]  in
                             uu____62400 :: uu____62409  in
                           uu____62380 :: uu____62389  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____62378
                           uu____62379
                          in
                       uu____62373 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____62462 = destruct_comp c1  in
              match uu____62462 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____62498  ->
             let uu____62499 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____62499)
  
let (close_comp_if_refinement_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun t  ->
      fun x  ->
        fun c  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____62522;
                 FStar_Syntax_Syntax.index = uu____62523;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____62525;
                     FStar_Syntax_Syntax.vars = uu____62526;_};_},uu____62527)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____62535 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___585_62547  ->
            match uu___585_62547 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____62550 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____62575 =
            let uu____62578 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____62578 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____62575
            (fun c  ->
               (let uu____62634 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____62634) &&
                 (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                    FStar_Syntax_Util.is_unit))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____62646 = FStar_Syntax_Util.head_and_args' e  in
                match uu____62646 with
                | (head1,uu____62663) ->
                    let uu____62684 =
                      let uu____62685 = FStar_Syntax_Util.un_uinst head1  in
                      uu____62685.FStar_Syntax_Syntax.n  in
                    (match uu____62684 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____62690 =
                           let uu____62692 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____62692
                            in
                         Prims.op_Negation uu____62690
                     | uu____62693 -> true)))
              &&
              (let uu____62696 = should_not_inline_lc lc  in
               Prims.op_Negation uu____62696)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____62724 =
              let uu____62726 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____62726  in
            if uu____62724
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____62733 = FStar_Syntax_Util.is_unit t  in
               if uu____62733
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____62742 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____62742
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____62747 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____62747 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____62757 =
                             let uu____62758 =
                               let uu____62763 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____62764 =
                                 let uu____62765 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____62774 =
                                   let uu____62785 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____62785]  in
                                 uu____62765 :: uu____62774  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____62763
                                 uu____62764
                                in
                             uu____62758 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env
                             uu____62757)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____62819 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____62819
           then
             let uu____62824 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____62826 = FStar_Syntax_Print.term_to_string v1  in
             let uu____62828 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____62824 uu____62826 uu____62828
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____62845 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___586_62851  ->
              match uu___586_62851 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____62854 -> false))
       in
    if uu____62845
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___587_62866  ->
              match uu___587_62866 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____62886 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62886
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____62892 = destruct_comp c1  in
           match uu____62892 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____62906 =
                   let uu____62911 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____62912 =
                     let uu____62913 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____62922 =
                       let uu____62933 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____62942 =
                         let uu____62953 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____62953]  in
                       uu____62933 :: uu____62942  in
                     uu____62913 :: uu____62922  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____62911 uu____62912  in
                 uu____62906 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____62994 = weaken_flags c1.FStar_Syntax_Syntax.flags
                  in
               mk_comp md u_res_t res_t wp1 uu____62994)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____63018 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____63020 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____63020
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____63026 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____63026 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____63074 = destruct_comp c1  in
               match uu____63074 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____63088 =
                       let uu____63093 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____63094 =
                         let uu____63095 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____63104 =
                           let uu____63115 =
                             let uu____63124 =
                               let uu____63125 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____63125 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____63124
                              in
                           let uu____63134 =
                             let uu____63145 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____63145]  in
                           uu____63115 :: uu____63134  in
                         uu____63095 :: uu____63104  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____63093 uu____63094
                        in
                     uu____63088 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t))
  =
  fun reason  ->
    fun env  ->
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____63231 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____63231
            then (lc, g0)
            else
              (let flags =
                 let uu____63243 =
                   let uu____63251 =
                     FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
                   if uu____63251
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____63243 with
                 | (maybe_trivial_post,flags) ->
                     let uu____63281 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___588_63289  ->
                               match uu___588_63289 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____63292 -> []))
                        in
                     FStar_List.append flags uu____63281
                  in
               let strengthen uu____63298 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____63304 = FStar_TypeChecker_Env.guard_form g01
                       in
                    match uu____63304 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____63307 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____63307
                          then
                            let uu____63311 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____63313 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____63311 uu____63313
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____63318 =
                 let uu____63319 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____63319
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____63318,
                 (let uu___983_63321 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___983_63321.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___983_63321.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___983_63321.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___589_63330  ->
            match uu___589_63330 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____63334 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____63363 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____63363
          then e
          else
            (let uu____63370 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____63373 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____63373)
                in
             if uu____63370
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____63426  ->
            match uu____63426 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____63446 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____63446 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____63459 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____63459
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____63469 =
                         FStar_Syntax_Util.is_total_lcomp lc11  in
                       if uu____63469
                       then
                         let uu____63474 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____63474
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____63481 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____63481
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____63490 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____63490
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____63497 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____63497
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____63509 =
                  let uu____63510 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____63510
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____63527  ->
                          let uu____63528 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____63530 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____63535 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____63528 uu____63530 uu____63535);
                     (let aux uu____63553 =
                        let uu____63554 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____63554
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____63585 ->
                              let uu____63586 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____63586
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____63618 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____63618
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____63663 =
                        let uu____63664 =
                          let uu____63666 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____63666  in
                        if uu____63664
                        then
                          let uu____63680 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____63680
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____63703 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____63703))
                        else
                          (let uu____63718 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____63718
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___1049_63760 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1049_63760.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1049_63760.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____63761 =
                                 let uu____63767 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____63767, reason)  in
                               FStar_Util.Inl uu____63761  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____63803 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____63803
                                   (close1 x "c1 Tot")
                             | (uu____63817,FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____63840,uu____63841) -> aux ()
                           else
                             (let uu____63856 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____63856
                              then
                                let uu____63869 =
                                  let uu____63875 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____63875, "both GTot")  in
                                FStar_Util.Inl uu____63869
                              else aux ()))
                         in
                      let uu____63886 = try_simplify ()  in
                      match uu____63886 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____63912  ->
                                let uu____63913 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____63913);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____63927  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____63949 = lift_and_destruct env c11 c21
                                 in
                              match uu____63949 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____64002 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____64002]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____64022 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____64022]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____64069 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____64078 =
                                      let uu____64089 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____64098 =
                                        let uu____64109 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____64118 =
                                          let uu____64129 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____64138 =
                                            let uu____64149 =
                                              let uu____64158 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____64158
                                               in
                                            [uu____64149]  in
                                          uu____64129 :: uu____64138  in
                                        uu____64109 :: uu____64118  in
                                      uu____64089 :: uu____64098  in
                                    uu____64069 :: uu____64078  in
                                  let wp =
                                    let uu____64210 =
                                      let uu____64215 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____64215 wp_args
                                       in
                                    uu____64210 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____64238 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____64238 with
                              | (m,uu____64246,lift2) ->
                                  let c23 =
                                    let uu____64249 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____64249
                                     in
                                  let uu____64250 = destruct_comp c12  in
                                  (match uu____64250 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____64264 =
                                           let uu____64269 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____64270 =
                                             let uu____64271 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____64280 =
                                               let uu____64291 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____64291]  in
                                             uu____64271 :: uu____64280  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64269 uu____64270
                                            in
                                         uu____64264
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____64329 = destruct_comp c1_typ  in
                            match uu____64329 with
                            | (u_res_t1,res_t1,uu____64338) ->
                                let uu____64339 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____64339
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____64344 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____64344
                                   then
                                     (debug1
                                        (fun uu____64354  ->
                                           let uu____64355 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____64357 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____64355 uu____64357);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____64365 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____64368 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____64368)
                                         in
                                      if uu____64365
                                      then
                                        let e1' =
                                          let uu____64389 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____64389
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____64401  ->
                                              let uu____64402 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____64404 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____64402 uu____64404);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____64419  ->
                                              let uu____64420 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____64422 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____64420 uu____64422);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____64429 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____64429
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____64447 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____64471 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____64471)
           in
        let flags =
          if should_return1
          then
            let uu____64479 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____64479
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____64495 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____64499 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____64499
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____64505 =
              let uu____64507 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____64507  in
            (if uu____64505
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___1168_64514 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___1168_64514.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___1168_64514.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___1168_64514.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____64527 =
                 let uu____64528 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____64528
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____64527
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____64531 =
               let uu____64532 =
                 let uu____64533 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____64533
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____64532  in
             FStar_Syntax_Util.comp_set_flags uu____64531 flags)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____64571  ->
              match uu____64571 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____64583 =
                      ((let uu____64587 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____64587) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____64583
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____64605 =
        let uu____64606 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____64606  in
      FStar_Syntax_Syntax.fvar uu____64605 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_Syntax_Syntax.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____64676  ->
                 match uu____64676 with
                 | (uu____64690,eff_label,uu____64692,uu____64693) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____64706 =
          let uu____64714 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____64752  ->
                    match uu____64752 with
                    | (uu____64767,uu____64768,flags,uu____64770) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___590_64787  ->
                                match uu___590_64787 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____64790 -> false))))
             in
          if uu____64714
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____64706 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____64823 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____64825 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____64825
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____64866 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____64867 =
                     let uu____64872 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____64873 =
                       let uu____64874 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____64883 =
                         let uu____64894 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____64903 =
                           let uu____64914 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____64923 =
                             let uu____64934 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____64934]  in
                           uu____64914 :: uu____64923  in
                         uu____64894 :: uu____64903  in
                       uu____64874 :: uu____64883  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____64872 uu____64873
                      in
                   uu____64867 FStar_Pervasives_Native.None uu____64866  in
                 let default_case =
                   let post_k =
                     let uu____64987 =
                       let uu____64996 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____64996]  in
                     let uu____65015 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____64987 uu____65015  in
                   let kwp =
                     let uu____65021 =
                       let uu____65030 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____65030]  in
                     let uu____65049 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65021 uu____65049  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____65056 =
                       let uu____65057 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____65057]  in
                     let uu____65076 =
                       let uu____65079 =
                         let uu____65086 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____65086
                          in
                       let uu____65087 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____65079 uu____65087  in
                     FStar_Syntax_Util.abs uu____65056 uu____65076
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____65111 =
                     should_not_inline_whole_match ||
                       (let uu____65114 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____65114)
                      in
                   if uu____65111 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____65153  ->
                        fun celse  ->
                          match uu____65153 with
                          | (g,eff_label,uu____65170,cthen) ->
                              let uu____65184 =
                                let uu____65209 =
                                  let uu____65210 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____65210
                                   in
                                lift_and_destruct env uu____65209 celse  in
                              (match uu____65184 with
                               | ((md,uu____65212,uu____65213),(uu____65214,uu____65215,wp_then),
                                  (uu____65217,uu____65218,wp_else)) ->
                                   let uu____65238 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____65238 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____65253::[] -> comp
                 | uu____65296 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____65315 = destruct_comp comp1  in
                     (match uu____65315 with
                      | (uu____65322,uu____65323,wp) ->
                          let wp1 =
                            let uu____65328 =
                              let uu____65333 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____65334 =
                                let uu____65335 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____65344 =
                                  let uu____65355 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____65355]  in
                                uu____65335 :: uu____65344  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____65333
                                uu____65334
                               in
                            uu____65328 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65421 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____65421 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____65437 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____65443 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____65437 uu____65443
              else
                (let uu____65452 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____65458 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____65452 uu____65458)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (universe_of_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u_res  ->
      fun c  ->
        let c_lid =
          let uu____65483 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____65483
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____65486 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____65486
        then u_res
        else
          (let is_total =
             let uu____65493 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____65493
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____65504 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____65504 with
              | FStar_Pervasives_Native.None  ->
                  let uu____65507 =
                    let uu____65513 =
                      let uu____65515 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____65515
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____65513)
                     in
                  FStar_Errors.raise_error uu____65507
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          if env.FStar_TypeChecker_Env.is_pattern
          then (e, lc)
          else
            (let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____65560 =
                 let uu____65561 = FStar_Syntax_Subst.compress t2  in
                 uu____65561.FStar_Syntax_Syntax.n  in
               match uu____65560 with
               | FStar_Syntax_Syntax.Tm_type uu____65565 -> true
               | uu____65567 -> false  in
             let uu____65569 =
               let uu____65570 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____65570.FStar_Syntax_Syntax.n  in
             match uu____65569 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____65578 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____65588 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____65588
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____65591 =
                     let uu____65592 =
                       let uu____65593 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____65593
                        in
                     (FStar_Pervasives_Native.None, uu____65592)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____65591
                    in
                 let e1 =
                   let uu____65599 =
                     let uu____65604 =
                       let uu____65605 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____65605]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____65604  in
                   uu____65599 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____65630 -> (e, lc))
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____65665 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____65665
           then
             let uu____65668 = FStar_Syntax_Print.term_to_string e  in
             let uu____65670 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____65672 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____65668 uu____65670 uu____65672
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____65682 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____65682 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____65707 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____65733 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____65733, false)
             else
               (let uu____65743 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____65743, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____65756) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____65768 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____65768
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___1324_65784 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___1324_65784.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___1324_65784.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___1324_65784.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____65791 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____65791 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____65803 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____65814 =
                        let uu____65816 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____65816 = FStar_Syntax_Util.Equal  in
                      if uu____65814
                      then
                        ((let uu____65819 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____65819
                          then
                            let uu____65823 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____65825 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____65823 uu____65825
                          else ());
                         set_result_typ1 c)
                      else
                        (let is_res_t_refinement =
                           let res_t1 =
                             FStar_TypeChecker_Normalize.normalize_refinement
                               FStar_TypeChecker_Normalize.whnf_steps env
                               res_t
                              in
                           match res_t1.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_refine uu____65836 ->
                               true
                           | uu____65844 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____65849 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____65849
                              in
                           let lc1 =
                             let uu____65851 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____65852 =
                               let uu____65853 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____65853)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____65851
                               uu____65852
                              in
                           ((let uu____65857 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65857
                             then
                               let uu____65861 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____65863 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____65865 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____65867 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____65861 uu____65863 uu____65865
                                 uu____65867
                             else ());
                            (let uu____65872 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____65872))
                         else
                           ((let uu____65876 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65876
                             then
                               let uu____65880 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____65882 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____65880 uu____65882
                             else ());
                            set_result_typ1 c))
                       in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1356_65890 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1356_65890.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1356_65890.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1356_65890.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____65896 =
                      let uu____65897 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____65897
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____65903 =
                           let uu____65904 = FStar_Syntax_Subst.compress f1
                              in
                           uu____65904.FStar_Syntax_Syntax.n  in
                         match uu____65903 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____65907,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____65909;
                                            FStar_Syntax_Syntax.vars =
                                              uu____65910;_},uu____65911)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1372_65937 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1372_65937.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1372_65937.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1372_65937.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____65938 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____65941 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____65941
                               then
                                 let uu____65945 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____65947 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____65949 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____65951 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____65945 uu____65947 uu____65949
                                   uu____65951
                               else ());
                              (let u_t_opt = comp_univ_opt c  in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (t.FStar_Syntax_Syntax.pos)) t
                                  in
                               let xexp = FStar_Syntax_Syntax.bv_to_name x
                                  in
                               let cret = return_value env u_t_opt t xexp  in
                               let guard =
                                 if apply_guard1
                                 then
                                   let uu____65964 =
                                     let uu____65969 =
                                       let uu____65970 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____65970]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____65969
                                      in
                                   uu____65964 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____65997 =
                                 let uu____66002 =
                                   FStar_All.pipe_left
                                     (fun _66023  ->
                                        FStar_Pervasives_Native.Some _66023)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____66024 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____66025 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____66026 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____66002
                                   uu____66024 e uu____66025 uu____66026
                                  in
                               match uu____65997 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1388_66030 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1388_66030.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1388_66030.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____66032 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____66032
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____66037 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____66037
                                     then
                                       let uu____66041 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____66041
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___591_66054  ->
                              match uu___591_66054 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____66057 -> []))
                       in
                    let lc1 =
                      let uu____66059 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____66059 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1402_66061 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1402_66061.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1402_66061.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1402_66061.FStar_TypeChecker_Env.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____66097 =
          let uu____66100 =
            let uu____66105 =
              let uu____66106 =
                let uu____66115 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____66115  in
              [uu____66106]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____66105  in
          uu____66100 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____66097  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____66138 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____66138
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____66157 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____66173 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____66190 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____66190
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____66206)::(ens,uu____66208)::uu____66209 ->
                    let uu____66252 =
                      let uu____66255 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____66255  in
                    let uu____66256 =
                      let uu____66257 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____66257  in
                    (uu____66252, uu____66256)
                | uu____66260 ->
                    let uu____66271 =
                      let uu____66277 =
                        let uu____66279 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____66279
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____66277)
                       in
                    FStar_Errors.raise_error uu____66271
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____66299)::uu____66300 ->
                    let uu____66327 =
                      let uu____66332 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____66332
                       in
                    (match uu____66327 with
                     | (us_r,uu____66364) ->
                         let uu____66365 =
                           let uu____66370 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____66370
                            in
                         (match uu____66365 with
                          | (us_e,uu____66402) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____66405 =
                                  let uu____66406 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66406
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66405
                                  us_r
                                 in
                              let as_ens =
                                let uu____66408 =
                                  let uu____66409 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66409
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66408
                                  us_e
                                 in
                              let req =
                                let uu____66413 =
                                  let uu____66418 =
                                    let uu____66419 =
                                      let uu____66430 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66430]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66419
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____66418
                                   in
                                uu____66413 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____66470 =
                                  let uu____66475 =
                                    let uu____66476 =
                                      let uu____66487 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66487]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66476
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____66475
                                   in
                                uu____66470 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____66524 =
                                let uu____66527 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____66527  in
                              let uu____66528 =
                                let uu____66529 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____66529  in
                              (uu____66524, uu____66528)))
                | uu____66532 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Reify;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
         in
      (let uu____66566 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____66566
       then
         let uu____66571 = FStar_Syntax_Print.term_to_string tm  in
         let uu____66573 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____66571
           uu____66573
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.EraseUniverses;
            FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
           in
        (let uu____66627 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____66627
         then
           let uu____66632 = FStar_Syntax_Print.term_to_string tm  in
           let uu____66634 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____66632
             uu____66634
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____66645 =
      let uu____66647 =
        let uu____66648 = FStar_Syntax_Subst.compress t  in
        uu____66648.FStar_Syntax_Syntax.n  in
      match uu____66647 with
      | FStar_Syntax_Syntax.Tm_app uu____66652 -> false
      | uu____66670 -> true  in
    if uu____66645
    then t
    else
      (let uu____66675 = FStar_Syntax_Util.head_and_args t  in
       match uu____66675 with
       | (head1,args) ->
           let uu____66718 =
             let uu____66720 =
               let uu____66721 = FStar_Syntax_Subst.compress head1  in
               uu____66721.FStar_Syntax_Syntax.n  in
             match uu____66720 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____66726 -> false  in
           if uu____66718
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____66758 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____66805 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____66805
            then
              let uu____66808 = FStar_Syntax_Print.term_to_string e  in
              let uu____66810 = FStar_Syntax_Print.term_to_string t  in
              let uu____66812 =
                let uu____66814 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____66814
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____66808 uu____66810 uu____66812
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____66827 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____66827 with
              | (formals,uu____66843) ->
                  let n_implicits =
                    let uu____66865 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____66943  ->
                              match uu____66943 with
                              | (uu____66951,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____66958 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____66958 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____66865 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____67083 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____67083 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____67097 =
                      let uu____67103 =
                        let uu____67105 = FStar_Util.string_of_int n_expected
                           in
                        let uu____67107 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____67109 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____67105 uu____67107 uu____67109
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____67103)
                       in
                    let uu____67113 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____67097 uu____67113
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___592_67131 =
              match uu___592_67131 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____67174 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____67174 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _67305,uu____67292)
                           when _67305 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____67338,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____67340))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67374 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____67374 with
                            | (v1,uu____67415,g) ->
                                ((let uu____67430 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67430
                                  then
                                    let uu____67433 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____67433
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67443 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67443 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67536 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67536))))
                       | (uu____67563,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67600 =
                             let uu____67613 =
                               let uu____67620 =
                                 let uu____67625 = FStar_Dyn.mkdyn env  in
                                 (uu____67625, tau)  in
                               FStar_Pervasives_Native.Some uu____67620  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____67613
                              in
                           (match uu____67600 with
                            | (v1,uu____67658,g) ->
                                ((let uu____67673 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67673
                                  then
                                    let uu____67676 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____67676
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67686 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67686 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67779 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67779))))
                       | (uu____67806,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____67854 =
                       let uu____67881 = inst_n_binders t1  in
                       aux [] uu____67881 bs1  in
                     (match uu____67854 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____67953) -> (e, torig, guard)
                           | (uu____67984,[]) when
                               let uu____68015 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____68015 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____68017 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____68045 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst1 t2
                                  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____68058 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____68070 =
      let uu____68074 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____68074
        (FStar_List.map
           (fun u  ->
              let uu____68086 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____68086 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____68070 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____68114 = FStar_Util.set_is_empty x  in
      if uu____68114
      then []
      else
        (let s =
           let uu____68132 =
             let uu____68135 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____68135  in
           FStar_All.pipe_right uu____68132 FStar_Util.set_elements  in
         (let uu____68151 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____68151
          then
            let uu____68156 =
              let uu____68158 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____68158  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____68156
          else ());
         (let r =
            let uu____68167 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____68167  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____68206 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____68206
                     then
                       let uu____68211 =
                         let uu____68213 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____68213
                          in
                       let uu____68217 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____68219 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____68211 uu____68217 uu____68219
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____68249 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____68249 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____68288) -> generalized_univ_names
        | (uu____68295,[]) -> explicit_univ_names
        | uu____68302 ->
            let uu____68311 =
              let uu____68317 =
                let uu____68319 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____68319
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____68317)
               in
            FStar_Errors.raise_error uu____68311 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____68341 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____68341
       then
         let uu____68346 = FStar_Syntax_Print.term_to_string t  in
         let uu____68348 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____68346 uu____68348
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____68357 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____68357
        then
          let uu____68362 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____68362
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____68371 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____68371
         then
           let uu____68376 = FStar_Syntax_Print.term_to_string t  in
           let uu____68378 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____68376 uu____68378
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name
          Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____68462 =
          let uu____68464 =
            FStar_Util.for_all
              (fun uu____68478  ->
                 match uu____68478 with
                 | (uu____68488,uu____68489,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____68464  in
        if uu____68462
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____68541 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____68541
              then
                let uu____68544 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____68544
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____68551 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____68551
               then
                 let uu____68554 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____68554
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____68572 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____68572 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____68606 =
             match uu____68606 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____68643 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____68643
                   then
                     let uu____68648 =
                       let uu____68650 =
                         let uu____68654 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____68654
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____68650
                         (FStar_String.concat ", ")
                        in
                     let uu____68702 =
                       let uu____68704 =
                         let uu____68708 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____68708
                           (FStar_List.map
                              (fun u  ->
                                 let uu____68721 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____68723 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____68721
                                   uu____68723))
                          in
                       FStar_All.pipe_right uu____68704
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____68648
                       uu____68702
                   else ());
                  (let univs2 =
                     let uu____68737 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____68749 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____68749) univs1
                       uu____68737
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____68756 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____68756
                    then
                      let uu____68761 =
                        let uu____68763 =
                          let uu____68767 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____68767
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____68763
                          (FStar_String.concat ", ")
                         in
                      let uu____68815 =
                        let uu____68817 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____68831 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____68833 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____68831
                                    uu____68833))
                           in
                        FStar_All.pipe_right uu____68817
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____68761 uu____68815
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____68854 =
             let uu____68871 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____68871  in
           match uu____68854 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____68961 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____68961
                 then ()
                 else
                   (let uu____68966 = lec_hd  in
                    match uu____68966 with
                    | (lb1,uu____68974,uu____68975) ->
                        let uu____68976 = lec2  in
                        (match uu____68976 with
                         | (lb2,uu____68984,uu____68985) ->
                             let msg =
                               let uu____68988 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____68990 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____68988 uu____68990
                                in
                             let uu____68993 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____68993))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u  ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u'  ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head))))
                    in
                 let uu____69061 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____69061
                 then ()
                 else
                   (let uu____69066 = lec_hd  in
                    match uu____69066 with
                    | (lb1,uu____69074,uu____69075) ->
                        let uu____69076 = lec2  in
                        (match uu____69076 with
                         | (lb2,uu____69084,uu____69085) ->
                             let msg =
                               let uu____69088 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69090 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____69088 uu____69090
                                in
                             let uu____69093 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____69093))
                  in
               let lecs1 =
                 let uu____69104 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____69157 = univs_and_uvars_of_lec this_lec  in
                        match uu____69157 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____69104 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____69262 = lec_hd  in
                   match uu____69262 with
                   | (lbname,e,c) ->
                       let uu____69272 =
                         let uu____69278 =
                           let uu____69280 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____69282 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____69284 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____69280 uu____69282 uu____69284
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____69278)
                          in
                       let uu____69288 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____69272 uu____69288
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____69307 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____69307 with
                         | FStar_Pervasives_Native.Some uu____69316 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____69324 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____69328 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____69328 with
                              | (bs,kres) ->
                                  ((let uu____69372 =
                                      let uu____69373 =
                                        let uu____69376 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____69376
                                         in
                                      uu____69373.FStar_Syntax_Syntax.n  in
                                    match uu____69372 with
                                    | FStar_Syntax_Syntax.Tm_type uu____69377
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____69381 =
                                          let uu____69383 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____69383  in
                                        if uu____69381
                                        then fail1 kres
                                        else ()
                                    | uu____69388 -> fail1 kres);
                                   (let a =
                                      let uu____69390 =
                                        let uu____69393 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _69396  ->
                                             FStar_Pervasives_Native.Some
                                               _69396) uu____69393
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____69390
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____69404 ->
                                          let uu____69413 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____69413
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres))
                                       in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____69516  ->
                         match uu____69516 with
                         | (lbname,e,c) ->
                             let uu____69562 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____69623 ->
                                   let uu____69636 = (e, c)  in
                                   (match uu____69636 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____69676  ->
                                                   match uu____69676 with
                                                   | (x,uu____69682) ->
                                                       let uu____69683 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____69683)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____69701 =
                                                let uu____69703 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____69703
                                                 in
                                              if uu____69701
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____69712 =
                                            let uu____69713 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____69713.FStar_Syntax_Syntax.n
                                             in
                                          match uu____69712 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____69738 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____69738 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____69749 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____69753 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____69753, gen_tvars))
                                in
                             (match uu____69562 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____69900 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____69900
         then
           let uu____69903 =
             let uu____69905 =
               FStar_List.map
                 (fun uu____69920  ->
                    match uu____69920 with
                    | (lb,uu____69929,uu____69930) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____69905 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____69903
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____69956  ->
                match uu____69956 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____69985 = gen env is_rec lecs  in
           match uu____69985 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____70084  ->
                       match uu____70084 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____70146 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____70146
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____70194  ->
                           match uu____70194 with
                           | (l,us,e,c,gvs) ->
                               let uu____70228 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____70230 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____70232 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____70234 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____70236 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____70228 uu____70230 uu____70232
                                 uu____70234 uu____70236))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____70281  ->
                match uu____70281 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____70325 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____70325, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____70386 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____70386 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____70392 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _70395  -> FStar_Pervasives_Native.Some _70395)
                     uu____70392)
             in
          let is_var e1 =
            let uu____70403 =
              let uu____70404 = FStar_Syntax_Subst.compress e1  in
              uu____70404.FStar_Syntax_Syntax.n  in
            match uu____70403 with
            | FStar_Syntax_Syntax.Tm_name uu____70408 -> true
            | uu____70410 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1858_70431 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1858_70431.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1858_70431.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____70432 -> e2  in
          let env2 =
            let uu___1861_70434 = env1  in
            let uu____70435 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1861_70434.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1861_70434.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1861_70434.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1861_70434.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1861_70434.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1861_70434.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1861_70434.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1861_70434.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1861_70434.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1861_70434.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1861_70434.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1861_70434.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1861_70434.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1861_70434.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1861_70434.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1861_70434.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1861_70434.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____70435;
              FStar_TypeChecker_Env.is_iface =
                (uu___1861_70434.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1861_70434.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1861_70434.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1861_70434.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1861_70434.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1861_70434.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1861_70434.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1861_70434.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1861_70434.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1861_70434.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1861_70434.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1861_70434.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1861_70434.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1861_70434.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1861_70434.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1861_70434.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1861_70434.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1861_70434.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1861_70434.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1861_70434.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1861_70434.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1861_70434.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1861_70434.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1861_70434.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1861_70434.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____70437 = check1 env2 t1 t2  in
          match uu____70437 with
          | FStar_Pervasives_Native.None  ->
              let uu____70444 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____70450 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____70444 uu____70450
          | FStar_Pervasives_Native.Some g ->
              ((let uu____70457 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70457
                then
                  let uu____70462 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____70462
                else ());
               (let uu____70468 = decorate e t2  in (uu____70468, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____70496 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____70496
         then
           let uu____70499 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____70499
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____70513 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____70513
         then
           let uu____70521 = discharge g1  in
           let uu____70523 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____70521, uu____70523)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____70532 =
                let uu____70533 =
                  let uu____70534 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____70534
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____70533
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____70532
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____70536 = destruct_comp c1  in
            match uu____70536 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____70554 = FStar_TypeChecker_Env.get_range env  in
                  let uu____70555 =
                    let uu____70560 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____70561 =
                      let uu____70562 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____70571 =
                        let uu____70582 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____70582]  in
                      uu____70562 :: uu____70571  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____70560 uu____70561  in
                  uu____70555 FStar_Pervasives_Native.None uu____70554  in
                ((let uu____70616 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____70616
                  then
                    let uu____70621 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____70621
                  else ());
                 (let g2 =
                    let uu____70627 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____70627  in
                  let uu____70628 = discharge g2  in
                  let uu____70630 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____70628, uu____70630)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___593_70664 =
        match uu___593_70664 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____70674)::[] -> f fst1
        | uu____70699 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____70711 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____70711
          (fun _70712  -> FStar_TypeChecker_Common.NonTrivial _70712)
         in
      let op_or_e e =
        let uu____70723 =
          let uu____70724 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____70724  in
        FStar_All.pipe_right uu____70723
          (fun _70727  -> FStar_TypeChecker_Common.NonTrivial _70727)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _70734  -> FStar_TypeChecker_Common.NonTrivial _70734)
         in
      let op_or_t t =
        let uu____70745 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____70745
          (fun _70748  -> FStar_TypeChecker_Common.NonTrivial _70748)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _70755  -> FStar_TypeChecker_Common.NonTrivial _70755)
         in
      let short_op_ite uu___594_70761 =
        match uu___594_70761 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____70771)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____70798)::[] ->
            let uu____70839 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____70839
              (fun _70840  -> FStar_TypeChecker_Common.NonTrivial _70840)
        | uu____70841 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____70853 =
          let uu____70861 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____70861)  in
        let uu____70869 =
          let uu____70879 =
            let uu____70887 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____70887)  in
          let uu____70895 =
            let uu____70905 =
              let uu____70913 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____70913)  in
            let uu____70921 =
              let uu____70931 =
                let uu____70939 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____70939)  in
              let uu____70947 =
                let uu____70957 =
                  let uu____70965 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____70965)  in
                [uu____70957; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____70931 :: uu____70947  in
            uu____70905 :: uu____70921  in
          uu____70879 :: uu____70895  in
        uu____70853 :: uu____70869  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____71027 =
            FStar_Util.find_map table
              (fun uu____71042  ->
                 match uu____71042 with
                 | (x,mk1) ->
                     let uu____71059 = FStar_Ident.lid_equals x lid  in
                     if uu____71059
                     then
                       let uu____71064 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____71064
                     else FStar_Pervasives_Native.None)
             in
          (match uu____71027 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____71068 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____71076 =
      let uu____71077 = FStar_Syntax_Util.un_uinst l  in
      uu____71077.FStar_Syntax_Syntax.n  in
    match uu____71076 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____71082 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____71118)::uu____71119 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____71138 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____71147,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____71148))::uu____71149 -> bs
      | uu____71167 ->
          let uu____71168 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____71168 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____71172 =
                 let uu____71173 = FStar_Syntax_Subst.compress t  in
                 uu____71173.FStar_Syntax_Syntax.n  in
               (match uu____71172 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____71177) ->
                    let uu____71198 =
                      FStar_Util.prefix_until
                        (fun uu___595_71238  ->
                           match uu___595_71238 with
                           | (uu____71246,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____71247)) ->
                               false
                           | uu____71252 -> true) bs'
                       in
                    (match uu____71198 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____71288,uu____71289) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____71361,uu____71362) ->
                         let uu____71435 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____71455  ->
                                   match uu____71455 with
                                   | (x,uu____71464) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____71435
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____71513  ->
                                     match uu____71513 with
                                     | (x,i) ->
                                         let uu____71532 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____71532, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____71543 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            let uu____71572 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____71572
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____71603 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____71603
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____71646 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____71646
         then
           ((let uu____71651 = FStar_Ident.text_of_lid lident  in
             d uu____71651);
            (let uu____71653 = FStar_Ident.text_of_lid lident  in
             let uu____71655 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____71653 uu____71655))
         else ());
        (let fv =
           let uu____71661 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____71661
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____71673 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2019_71675 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2019_71675.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2019_71675.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2019_71675.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2019_71675.FStar_Syntax_Syntax.sigattrs)
           }), uu____71673))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___596_71693 =
        match uu___596_71693 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71696 -> false  in
      let reducibility uu___597_71704 =
        match uu___597_71704 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____71711 -> false  in
      let assumption uu___598_71719 =
        match uu___598_71719 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____71723 -> false  in
      let reification uu___599_71731 =
        match uu___599_71731 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____71734 -> true
        | uu____71736 -> false  in
      let inferred uu___600_71744 =
        match uu___600_71744 with
        | FStar_Syntax_Syntax.Discriminator uu____71746 -> true
        | FStar_Syntax_Syntax.Projector uu____71748 -> true
        | FStar_Syntax_Syntax.RecordType uu____71754 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____71764 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____71777 -> false  in
      let has_eq uu___601_71785 =
        match uu___601_71785 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____71789 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (visibility x))
                           || (reducibility x))
                          || (reification x))
                         || (inferred x))
                        || (has_eq x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____71868 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71875 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____71886 =
        let uu____71888 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___602_71894  ->
                  match uu___602_71894 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____71897 -> false))
           in
        FStar_All.pipe_right uu____71888 Prims.op_Negation  in
      if uu____71886
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____71918 =
            let uu____71924 =
              let uu____71926 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____71926 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____71924)  in
          FStar_Errors.raise_error uu____71918 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____71944 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____71952 =
            let uu____71954 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____71954  in
          if uu____71952 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____71964),uu____71965) ->
              ((let uu____71977 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____71977
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____71986 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____71986
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____71997 ->
              let uu____72006 =
                let uu____72008 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((((x = FStar_Syntax_Syntax.Abstract) ||
                                (x =
                                   FStar_Syntax_Syntax.Inline_for_extraction))
                               || (x = FStar_Syntax_Syntax.NoExtract))
                              || (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____72008  in
              if uu____72006 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____72018 ->
              let uu____72025 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____72025 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____72033 ->
              let uu____72040 =
                let uu____72042 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____72042  in
              if uu____72040 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____72052 ->
              let uu____72053 =
                let uu____72055 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72055  in
              if uu____72053 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____72065 ->
              let uu____72066 =
                let uu____72068 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72068  in
              if uu____72066 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____72078 ->
              let uu____72091 =
                let uu____72093 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____72093  in
              if uu____72091 then err'1 () else ()
          | uu____72103 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____72126 =
          let uu____72131 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____72131
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____72126
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____72150 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____72150
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____72168 =
                          let uu____72169 = FStar_Syntax_Subst.compress t1
                             in
                          uu____72169.FStar_Syntax_Syntax.n  in
                        match uu____72168 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____72175 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____72201 =
          let uu____72202 = FStar_Syntax_Subst.compress t1  in
          uu____72202.FStar_Syntax_Syntax.n  in
        match uu____72201 with
        | FStar_Syntax_Syntax.Tm_type uu____72206 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____72209 ->
            let uu____72224 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____72224 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____72257 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____72257
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____72263;
               FStar_Syntax_Syntax.index = uu____72264;
               FStar_Syntax_Syntax.sort = t2;_},uu____72266)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72275,uu____72276) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____72318::[]) ->
            let uu____72357 =
              let uu____72358 = FStar_Syntax_Util.un_uinst head1  in
              uu____72358.FStar_Syntax_Syntax.n  in
            (match uu____72357 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____72363 -> false)
        | uu____72365 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Primops;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF;
            FStar_TypeChecker_Env.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.AllowUnboundUniverses;
            FStar_TypeChecker_Env.Zeta;
            FStar_TypeChecker_Env.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____72375 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____72375
         then
           let uu____72380 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____72380
         else ());
        res
       in aux g t
  