open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____58 =
      let uu____59 = FStar_Tactics_Types.goal_env g in
      let uu____60 = FStar_Tactics_Types.goal_type g in
      bnorm uu____59 uu____60 in
    FStar_Tactics_Types.goal_with_type g uu____58
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____76 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____76
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____92 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____113 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____113
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____124 =
       let uu____125 = FStar_Options.silent () in Prims.op_Negation uu____125 in
     if uu____124 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____133 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____139 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____139)
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____157 = FStar_Tactics_Types.subst_proof_state subst ps in
          FStar_Tactics_Printing.do_dump_proofstate uu____157 msg);
         FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu164 .
    Prims.string -> Prims.string -> 'uuuuuu164 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____177 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____177
let fail2 :
  'uuuuuu186 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu186 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____204 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____204
let fail3 :
  'uuuuuu215 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu215 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____238 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____238
let fail4 :
  'uuuuuu251 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu251 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____279 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____279
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____312 = FStar_Tactics_Monad.run t ps in
         match uu____312 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___68_336 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___68_336.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___68_336.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___68_336.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___68_336.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___68_336.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___68_336.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___68_336.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___68_336.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___68_336.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___68_336.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___68_336.FStar_Tactics_Types.local_state)
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let uu____374 = FStar_Tactics_Monad.run t ps in
         match uu____374 with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    let uu____421 = catch t in
    FStar_Tactics_Monad.bind uu____421
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____448 ->
             FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let trytac_exn :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         try
           (fun uu___94_479 ->
              match () with
              | () ->
                  let uu____484 = trytac t in
                  FStar_Tactics_Monad.run uu____484 ps) ()
         with
         | FStar_Errors.Err (uu____501, msg, uu____503) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____510 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____515, msg, uu____517, uu____518) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____525 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____547 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____547 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____557::(e1, FStar_Pervasives_Native.None)::(e2,
                                                         FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____617::uu____618::(e1, uu____620)::(e2, uu____622)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____699 ->
        let uu____702 = FStar_Syntax_Util.unb2t typ in
        (match uu____702 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____716 = FStar_Syntax_Util.head_and_args t in
             (match uu____716 with
              | (hd, args) ->
                  let uu____765 =
                    let uu____780 =
                      let uu____781 = FStar_Syntax_Subst.compress hd in
                      uu____781.FStar_Syntax_Syntax.n in
                    (uu____780, args) in
                  (match uu____765 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____801, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____802))::(e1,
                                                                   FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____869 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____905 = destruct_eq' typ in
    match uu____905 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____935 = FStar_Syntax_Util.un_squash typ in
        (match uu____935 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        (let uu____977 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____977
         then
           let uu____978 = FStar_Syntax_Print.term_to_string t1 in
           let uu____979 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____978
             uu____979
         else ());
        (try
           (fun uu___172_986 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____993 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____993
                    then
                      let uu____994 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____995 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____996 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____994
                        uu____995 uu____996
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1001 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____1001
                          (fun uu____1005 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____1013, msg, uu____1015) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1021 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1023 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____1024, msg, r, uu____1027) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1034 ->
                  let uu____1035 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1035)
               (fun uu____1037 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____1060 ->
             (let uu____1062 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____1062
              then
                (FStar_Options.push ();
                 (let uu____1064 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____1066 = __do_unify env1 t1 t2 in
              FStar_Tactics_Monad.bind uu____1066
                (fun r ->
                   (let uu____1073 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____1073 then FStar_Options.pop () else ());
                   FStar_Tactics_Monad.ret r)))
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1094 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1094
          (fun tx ->
             let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
             let uu____1108 = do_unify env1 t1 t2 in
             FStar_Tactics_Monad.bind uu____1108
               (fun r ->
                  if r
                  then
                    let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                    let uu____1121 =
                      let uu____1122 = FStar_Util.set_eq uvs1 uvs2 in
                      Prims.op_Negation uu____1122 in
                    (if uu____1121
                     then
                       (FStar_Syntax_Unionfind.rollback tx;
                        FStar_Tactics_Monad.ret false)
                     else FStar_Tactics_Monad.ret true)
                  else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1147 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1147
          (fun tx ->
             let uu____1157 = destruct_eq t1 in
             match uu____1157 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
             | FStar_Pervasives_Native.Some (lhs, uu____1171) ->
                 let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                 let uu____1179 = do_unify env1 t1 t2 in
                 FStar_Tactics_Monad.bind uu____1179
                   (fun r ->
                      if r
                      then
                        let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                        let uu____1192 =
                          let uu____1193 = FStar_Util.set_eq uvs1 uvs2 in
                          Prims.op_Negation uu____1193 in
                        (if uu____1192
                         then
                           (FStar_Syntax_Unionfind.rollback tx;
                            FStar_Tactics_Monad.ret false)
                         else FStar_Tactics_Monad.ret true)
                      else FStar_Tactics_Monad.ret false))
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1213 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____1213 with
      | FStar_Pervasives_Native.Some uu____1218 ->
          let uu____1219 =
            let uu____1220 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____1220 in
          FStar_Tactics_Monad.fail uu____1219
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1236 = FStar_Tactics_Types.goal_env goal in
      let uu____1237 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____1236 solution uu____1237
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____1256 ->
           let uu____1257 =
             let uu____1258 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____1258 in
           let uu____1259 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____1257 uu____1259)
        (fun uu____1262 ->
           let uu____1263 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____1263
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____1271 ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____1273 =
                     let uu____1274 =
                       let uu____1275 = FStar_Tactics_Types.goal_env goal in
                       tts uu____1275 solution in
                     let uu____1276 =
                       let uu____1277 = FStar_Tactics_Types.goal_env goal in
                       let uu____1278 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____1277 uu____1278 in
                     let uu____1279 =
                       let uu____1280 = FStar_Tactics_Types.goal_env goal in
                       let uu____1281 = FStar_Tactics_Types.goal_type goal in
                       tts uu____1280 uu____1281 in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1274 uu____1276 uu____1279 in
                   FStar_Tactics_Monad.fail uu____1273)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1296 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____1296
        (fun uu____1300 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____1302 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1309 = FStar_Syntax_Util.un_squash t1 in
    match uu____1309 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____1320 =
          let uu____1321 = FStar_Syntax_Subst.compress t'1 in
          uu____1321.FStar_Syntax_Syntax.n in
        (match uu____1320 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1325 -> false)
    | uu____1326 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1336 = FStar_Syntax_Util.un_squash t in
    match uu____1336 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1346 =
          let uu____1347 = FStar_Syntax_Subst.compress t' in
          uu____1347.FStar_Syntax_Syntax.n in
        (match uu____1346 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1351 -> false)
    | uu____1352 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____1366 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____1375 =
                   let uu____1376 = FStar_Tactics_Types.goal_type g in
                   uu____1376.FStar_Syntax_Syntax.pos in
                 let uu____1379 =
                   let uu____1384 =
                     let uu____1385 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1385 in
                   (FStar_Errors.Warning_TacAdmit, uu____1384) in
                 FStar_Errors.log_issue uu____1375 uu____1379);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1366
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1400 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___281_1410 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___281_1410.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___281_1410.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___281_1410.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___281_1410.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___281_1410.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___281_1410.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___281_1410.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___281_1410.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___281_1410.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___281_1410.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___281_1410.FStar_Tactics_Types.local_state)
           } in
         let uu____1411 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____1411
           (fun uu____1416 ->
              let uu____1417 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____1417))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1424 ->
    let uu____1427 =
      let uu____1428 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____1428 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____1427
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1471 ->
                let uu____1472 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1472)
             (fun uu____1475 ->
                let e1 =
                  let uu___290_1477 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___290_1477.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___290_1477.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___290_1477.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___290_1477.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___290_1477.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___290_1477.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___290_1477.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___290_1477.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___290_1477.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___290_1477.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___290_1477.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___290_1477.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___290_1477.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___290_1477.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___290_1477.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___290_1477.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___290_1477.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___290_1477.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___290_1477.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___290_1477.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___290_1477.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___290_1477.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___290_1477.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___290_1477.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___290_1477.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___290_1477.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___290_1477.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___290_1477.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___290_1477.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___290_1477.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___290_1477.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___290_1477.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___290_1477.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___290_1477.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___290_1477.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___290_1477.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___290_1477.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___290_1477.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___290_1477.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___290_1477.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___290_1477.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___290_1477.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___290_1477.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___290_1477.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___290_1477.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___290_1477.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___294_1488 ->
                     match () with
                     | () ->
                         let uu____1497 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1497) ()
                with
                | FStar_Errors.Err (uu____1525, msg, uu____1527) ->
                    let uu____1532 = tts e1 t in
                    let uu____1533 =
                      let uu____1534 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1534
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1532 uu____1533 msg
                | FStar_Errors.Error
                    (uu____1541, msg, uu____1543, uu____1544) ->
                    let uu____1549 = tts e1 t in
                    let uu____1550 =
                      let uu____1551 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1551
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1549 uu____1550 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1600 ->
                let uu____1601 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1601)
             (fun uu____1604 ->
                let e1 =
                  let uu___313_1606 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___313_1606.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___313_1606.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___313_1606.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___313_1606.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___313_1606.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___313_1606.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___313_1606.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___313_1606.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___313_1606.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___313_1606.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___313_1606.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___313_1606.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___313_1606.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___313_1606.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___313_1606.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___313_1606.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___313_1606.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___313_1606.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___313_1606.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___313_1606.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___313_1606.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___313_1606.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___313_1606.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___313_1606.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___313_1606.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___313_1606.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___313_1606.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___313_1606.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___313_1606.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___313_1606.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___313_1606.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___313_1606.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___313_1606.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___313_1606.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___313_1606.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___313_1606.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___313_1606.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___313_1606.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___313_1606.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___313_1606.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___313_1606.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___313_1606.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___313_1606.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___313_1606.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___313_1606.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___313_1606.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___317_1620 ->
                     match () with
                     | () ->
                         let uu____1629 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1629 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1668, msg, uu____1670) ->
                    let uu____1675 = tts e1 t in
                    let uu____1676 =
                      let uu____1677 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1677
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1675 uu____1676 msg
                | FStar_Errors.Error
                    (uu____1684, msg, uu____1686, uu____1687) ->
                    let uu____1692 = tts e1 t in
                    let uu____1693 =
                      let uu____1694 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1694
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1692 uu____1693 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1743 ->
                let uu____1744 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1744)
             (fun uu____1748 ->
                let e1 =
                  let uu___340_1750 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___340_1750.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___340_1750.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___340_1750.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___340_1750.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___340_1750.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___340_1750.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___340_1750.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___340_1750.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___340_1750.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___340_1750.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___340_1750.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___340_1750.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___340_1750.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___340_1750.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___340_1750.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___340_1750.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___340_1750.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___340_1750.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___340_1750.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___340_1750.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___340_1750.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___340_1750.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___340_1750.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___340_1750.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___340_1750.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___340_1750.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___340_1750.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___340_1750.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___340_1750.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___340_1750.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___340_1750.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___340_1750.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___340_1750.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___340_1750.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___340_1750.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___340_1750.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___340_1750.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___340_1750.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___340_1750.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___340_1750.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___340_1750.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___340_1750.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___340_1750.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___340_1750.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___340_1750.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___340_1750.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___343_1752 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___343_1752.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___343_1752.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___343_1752.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___343_1752.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___343_1752.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___343_1752.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___343_1752.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___343_1752.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___343_1752.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___343_1752.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___343_1752.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___343_1752.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___343_1752.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___343_1752.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___343_1752.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___343_1752.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___343_1752.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___343_1752.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___343_1752.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___343_1752.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___343_1752.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___343_1752.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___343_1752.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___343_1752.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___343_1752.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___343_1752.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___343_1752.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___343_1752.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___343_1752.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___343_1752.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___343_1752.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___343_1752.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___343_1752.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___343_1752.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___343_1752.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___343_1752.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___343_1752.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___343_1752.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___343_1752.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___343_1752.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___343_1752.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___343_1752.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___343_1752.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___343_1752.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___343_1752.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___343_1752.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___347_1763 ->
                     match () with
                     | () ->
                         let uu____1772 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1772) ()
                with
                | FStar_Errors.Err (uu____1800, msg, uu____1802) ->
                    let uu____1807 = tts e2 t in
                    let uu____1808 =
                      let uu____1809 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1809
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1807 uu____1808 msg
                | FStar_Errors.Error
                    (uu____1816, msg, uu____1818, uu____1819) ->
                    let uu____1824 = tts e2 t in
                    let uu____1825 =
                      let uu____1826 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1826
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1824 uu____1825 msg))
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1853 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___370_1871 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1871.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1871.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1871.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1871.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1871.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1871.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1871.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1871.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___370_1871.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1871.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1871.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1895 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1895
        (fun old_pol ->
           let uu____1901 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1901
             (fun uu____1905 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1909 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1909
                       (fun uu____1913 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1916 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1916
    (fun uu___0_1925 ->
       match uu___0_1925 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1931 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1931)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1953 ->
             let uu____1954 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1954)
          (fun uu____1957 ->
             let uu____1958 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1958
               (fun uu____1962 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1966 =
                         let uu____1967 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1967.FStar_TypeChecker_Common.guard_f in
                       match uu____1966 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1971 = istrivial e f in
                           if uu____1971
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1981 =
                                          let uu____1986 =
                                            let uu____1987 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1987 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1986) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1981);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1990 ->
                                           let uu____1991 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1991)
                                        (fun uu____1994 ->
                                           let uu____1995 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1995
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___399_2002 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___399_2002.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___399_2002.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___399_2002.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___399_2002.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2005 ->
                                           let uu____2006 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2006)
                                        (fun uu____2009 ->
                                           let uu____2010 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____2010
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___406_2017 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___406_2017.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___406_2017.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___406_2017.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___406_2017.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2020 ->
                                           let uu____2021 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2021)
                                        (fun uu____2023 ->
                                           try
                                             (fun uu___413_2028 ->
                                                match () with
                                                | () ->
                                                    let uu____2031 =
                                                      let uu____2032 =
                                                        let uu____2033 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2033 in
                                                      Prims.op_Negation
                                                        uu____2032 in
                                                    if uu____2031
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____2038 ->
                                                           let uu____2039 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2039)
                                                        (fun uu____2041 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___412_2044 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____2049 ->
                                                    let uu____2050 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2050)
                                                 (fun uu____2052 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2067 =
        let uu____2070 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____2070
          (fun uu____2090 ->
             match uu____2090 with
             | (uu____2099, lc, uu____2101) ->
                 let uu____2102 =
                   let uu____2103 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____2103
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____2102) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____2067
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2130 =
        let uu____2135 = tcc e t in
        FStar_Tactics_Monad.bind uu____2135
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____2130
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2158 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____2164 =
           let uu____2165 = FStar_Tactics_Types.goal_env goal in
           let uu____2166 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____2165 uu____2166 in
         if uu____2164
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2170 =
              let uu____2171 = FStar_Tactics_Types.goal_env goal in
              let uu____2172 = FStar_Tactics_Types.goal_type goal in
              tts uu____2171 uu____2172 in
            fail1 "Not a trivial goal: %s" uu____2170))
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu____2221 =
               try
                 (fun uu___464_2244 ->
                    match () with
                    | () ->
                        let uu____2255 =
                          let uu____2264 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____2264
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____2255) ()
               with
               | uu___463_2274 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____2221
               (fun uu____2310 ->
                  match uu____2310 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___446_2336 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___446_2336.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___446_2336.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___446_2336.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___446_2336.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___446_2336.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___446_2336.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___446_2336.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___446_2336.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___446_2336.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___446_2336.FStar_Tactics_Types.local_state)
                        } in
                      let uu____2337 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____2337
                        (fun uu____2345 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___452_2361 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___452_2361.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___452_2361.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___452_2361.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___452_2361.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___452_2361.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___452_2361.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___452_2361.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___452_2361.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___452_2361.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___452_2361.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____2362 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____2362
                                       (fun uu____2370 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___458_2386 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___458_2386.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____2387 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2387
                                                      (fun uu____2395 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2401 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____2422 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____2422
      (fun uu____2435 ->
         match uu____2435 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2472::uu____2473 ->
             let uu____2476 =
               let uu____2485 = map tau in
               divide FStar_BigInt.one tau uu____2485 in
             FStar_Tactics_Monad.bind uu____2476
               (fun uu____2503 ->
                  match uu____2503 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2544 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2549 ->
             let uu____2550 = map t2 in
             FStar_Tactics_Monad.bind uu____2550
               (fun uu____2558 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2544
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2567 ->
    let uu____2570 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2579 =
             let uu____2586 =
               let uu____2587 = FStar_Tactics_Types.goal_env goal in
               let uu____2588 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2587 uu____2588 in
             FStar_Syntax_Util.arrow_one uu____2586 in
           match uu____2579 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2597 =
                 let uu____2598 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2598 in
               if uu____2597
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2603 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2603 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2619 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2619
                    (fun uu____2635 ->
                       match uu____2635 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2659 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2659
                             (fun uu____2665 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2667 =
                                  let uu____2670 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2670 in
                                FStar_Tactics_Monad.bind uu____2667
                                  (fun uu____2672 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2677 =
                 let uu____2678 = FStar_Tactics_Types.goal_env goal in
                 let uu____2679 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2678 uu____2679 in
               fail1 "goal is not an arrow (%s)" uu____2677) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2570
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2694 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2715 =
            let uu____2722 =
              let uu____2723 = FStar_Tactics_Types.goal_env goal in
              let uu____2724 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2723 uu____2724 in
            FStar_Syntax_Util.arrow_one uu____2722 in
          match uu____2715 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2737 =
                let uu____2738 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2738 in
              if uu____2737
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2751 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2751 in
                 let bs =
                   let uu____2761 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2761; b] in
                 let env' =
                   let uu____2787 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2787 bs in
                 let uu____2788 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2788
                   (fun uu____2813 ->
                      match uu____2813 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2827 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2830 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2827
                              FStar_Parser_Const.effect_Tot_lid uu____2830 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2848 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2848 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2870 =
                                   let uu____2871 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2871.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2870 in
                               let uu____2884 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2884
                                 (fun uu____2893 ->
                                    let uu____2894 =
                                      let uu____2897 =
                                        bnorm_goal
                                          (let uu___529_2900 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___529_2900.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___529_2900.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___529_2900.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___529_2900.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2897 in
                                    FStar_Tactics_Monad.bind uu____2894
                                      (fun uu____2907 ->
                                         let uu____2908 =
                                           let uu____2913 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2913, b) in
                                         FStar_Tactics_Monad.ret uu____2908)))))
          | FStar_Pervasives_Native.None ->
              let uu____2922 =
                let uu____2923 = FStar_Tactics_Types.goal_env goal in
                let uu____2924 = FStar_Tactics_Types.goal_type goal in
                tts uu____2923 uu____2924 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2922))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2946 ->
              let uu____2947 =
                let uu____2948 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2948 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2947)
           (fun uu____2953 ->
              let steps =
                let uu____2957 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2957 in
              let t =
                let uu____2961 = FStar_Tactics_Types.goal_env goal in
                let uu____2962 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2961 uu____2962 in
              let uu____2963 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2963))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2987 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2995 -> g.FStar_Tactics_Types.opts
                 | uu____2998 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____3003 ->
                    let uu____3004 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3004)
                 (fun uu____3007 ->
                    let uu____3008 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____3008
                      (fun uu____3029 ->
                         match uu____3029 with
                         | (t1, uu____3039, uu____3040) ->
                             let steps =
                               let uu____3044 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3044 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____3050 ->
                                  let uu____3051 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3051)
                               (fun uu____3053 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2987
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____3064 ->
    let uu____3067 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____3074 =
             let uu____3085 = FStar_Tactics_Types.goal_env g in
             let uu____3086 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____3085 uu____3086 in
           match uu____3074 with
           | (uu____3089, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____3114 =
                 let uu____3119 =
                   let uu____3124 =
                     let uu____3125 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____3125] in
                   FStar_Syntax_Subst.open_term uu____3124 phi in
                 match uu____3119 with
                 | (bvs, phi1) ->
                     let uu____3150 =
                       let uu____3151 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____3151 in
                     (uu____3150, phi1) in
               (match uu____3114 with
                | (bv1, phi1) ->
                    let uu____3170 =
                      let uu____3173 = FStar_Tactics_Types.goal_env g in
                      let uu____3174 =
                        let uu____3175 =
                          let uu____3178 =
                            let uu____3179 =
                              let uu____3186 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____3186) in
                            FStar_Syntax_Syntax.NT uu____3179 in
                          [uu____3178] in
                        FStar_Syntax_Subst.subst uu____3175 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____3173 uu____3174
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____3170
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3194 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____3067
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____3218 = FStar_Tactics_Types.goal_env goal in
               let uu____3219 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____3218 uu____3219
             else FStar_Tactics_Types.goal_env goal in
           let uu____3221 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____3221
             (fun uu____3240 ->
                match uu____3240 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3255 ->
                         let uu____3256 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____3257 =
                           let uu____3258 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____3258
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3256 uu____3257)
                      (fun uu____3261 ->
                         let uu____3262 =
                           let uu____3265 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____3265 guard in
                         FStar_Tactics_Monad.bind uu____3262
                           (fun uu____3267 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3271 ->
                                   let uu____3272 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____3273 =
                                     let uu____3274 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3274 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3272 uu____3273)
                                (fun uu____3277 ->
                                   let uu____3278 =
                                     let uu____3281 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____3282 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____3281 typ uu____3282 in
                                   FStar_Tactics_Monad.bind uu____3278
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3288 =
                                             let uu____3293 =
                                               let uu____3298 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____3298 in
                                             let uu____3299 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3293 typ uu____3299 in
                                           match uu____3288 with
                                           | (typ1, goalt) ->
                                               let uu____3304 =
                                                 let uu____3305 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____3305 t1 in
                                               let uu____3306 =
                                                 let uu____3307 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____3308 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____3307 uu____3308 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3304 typ1 goalt
                                                 uu____3306)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____3328 =
          FStar_Tactics_Monad.mlog
            (fun uu____3333 ->
               let uu____3334 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3334)
            (fun uu____3337 ->
               let uu____3338 =
                 let uu____3345 = __exact_now set_expected_typ tm in
                 catch uu____3345 in
               FStar_Tactics_Monad.bind uu____3338
                 (fun uu___2_3354 ->
                    match uu___2_3354 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3365 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3368 ->
                             let uu____3369 =
                               let uu____3376 =
                                 let uu____3379 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____3379
                                   (fun uu____3384 ->
                                      let uu____3385 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____3385
                                        (fun uu____3389 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____3376 in
                             FStar_Tactics_Monad.bind uu____3369
                               (fun uu___1_3396 ->
                                  match uu___1_3396 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3405 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3407 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3408 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3410 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3412 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3328
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            let f = if only_match then do_match else do_unify in
            let uu____3505 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____3505
              (fun uu___3_3517 ->
                 if uu___3_3517
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3536 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3536 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3557 = term_to_string e ty1 in
                        let uu____3558 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3557
                          uu____3558
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3573 =
                          let uu____3574 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3574 in
                        if uu____3573
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3594 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3594
                             (fun uu____3618 ->
                                match uu____3618 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3645 ->
                                         let uu____3646 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3646)
                                      (fun uu____3650 ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 -> __try_unify_by_application only_match [] e ty1 ty2
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tm ->
        let uu____3732 =
          FStar_Tactics_Monad.mlog
            (fun uu____3737 ->
               let uu____3738 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3738)
            (fun uu____3740 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3749 ->
                         let uu____3750 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3751 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3752 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3750 uu____3751 uu____3752)
                      (fun uu____3755 ->
                         let uu____3756 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3756
                           (fun uu____3777 ->
                              match uu____3777 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3790 =
                                    let uu____3801 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3801 in
                                  FStar_Tactics_Monad.bind uu____3790
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3822 ->
                                            let uu____3823 =
                                              FStar_Common.string_of_list
                                                (fun uu____3834 ->
                                                   match uu____3834 with
                                                   | (t, uu____3842,
                                                      uu____3843) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3823)
                                         (fun uu____3850 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3865) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3866 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3889 ->
                                                   fun w ->
                                                     match uu____3889 with
                                                     | (uvt, q, uu____3907)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3939 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3956 ->
                                                   fun s ->
                                                     match uu____3956 with
                                                     | (uu____3968,
                                                        uu____3969, uv) ->
                                                         let uu____3971 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3971) uvs
                                                uu____3939 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3980 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3980
                                              (fun uu____3985 ->
                                                 let uu____3986 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____4003 ->
                                                        match uu____4003 with
                                                        | (uvt, q, uv) ->
                                                            let uu____4015 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____4015
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____4020
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____4021
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____4021
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____4025
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___692_4031
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___692_4031.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___692_4031.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___692_4031.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____4028] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____4025)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3986
                                                   (fun uu____4035 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3732
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____4060 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____4060
    then
      let uu____4067 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4082 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4135 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____4067 with
      | (pre, post) ->
          let post1 =
            let uu____4167 =
              let uu____4178 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____4178] in
            FStar_Syntax_Util.mk_app post uu____4167 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4208 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____4208
       then
         let uu____4215 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____4215
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4292 = f x e in
            FStar_Tactics_Monad.bind uu____4292
              (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu____4316 =
          let uu____4319 =
            FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
              (fun ps ->
                 FStar_Tactics_Monad.mlog
                   (fun uu____4326 ->
                      let uu____4327 = FStar_Syntax_Print.term_to_string tm in
                      FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4327)
                   (fun uu____4330 ->
                      let is_unit_t t =
                        let uu____4337 =
                          let uu____4338 = FStar_Syntax_Subst.compress t in
                          uu____4338.FStar_Syntax_Syntax.n in
                        match uu____4337 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu____4342 -> false in
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           let uu____4348 = __tc env1 tm in
                           FStar_Tactics_Monad.bind uu____4348
                             (fun uu____4371 ->
                                match uu____4371 with
                                | (tm1, t, guard) ->
                                    let uu____4383 =
                                      FStar_Syntax_Util.arrow_formals_comp t in
                                    (match uu____4383 with
                                     | (bs, comp) ->
                                         let uu____4392 = lemma_or_sq comp in
                                         (match uu____4392 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Tactics_Monad.fail
                                                "not a lemma or squashed function"
                                          | FStar_Pervasives_Native.Some
                                              (pre, post) ->
                                              let uu____4411 =
                                                fold_left
                                                  (fun uu____4473 ->
                                                     fun uu____4474 ->
                                                       match (uu____4473,
                                                               uu____4474)
                                                       with
                                                       | ((b, aq),
                                                          (uvs, imps, subst))
                                                           ->
                                                           let b_t =
                                                             FStar_Syntax_Subst.subst
                                                               subst
                                                               b.FStar_Syntax_Syntax.sort in
                                                           let uu____4625 =
                                                             is_unit_t b_t in
                                                           if uu____4625
                                                           then
                                                             FStar_All.pipe_left
                                                               FStar_Tactics_Monad.ret
                                                               (((FStar_Syntax_Util.exp_unit,
                                                                   aq) ::
                                                                 uvs), imps,
                                                                 ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                 :: subst))
                                                           else
                                                             (let uu____4745
                                                                =
                                                                FStar_Tactics_Monad.new_uvar
                                                                  "apply_lemma"
                                                                  env1 b_t in
                                                              FStar_Tactics_Monad.bind
                                                                uu____4745
                                                                (fun
                                                                   uu____4781
                                                                   ->
                                                                   match uu____4781
                                                                   with
                                                                   | 
                                                                   (t1, u) ->
                                                                    FStar_All.pipe_left
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst)))))
                                                  ([], [], []) bs in
                                              FStar_Tactics_Monad.bind
                                                uu____4411
                                                (fun uu____4969 ->
                                                   match uu____4969 with
                                                   | (uvs, implicits1, subst)
                                                       ->
                                                       let implicits2 =
                                                         FStar_List.rev
                                                           implicits1 in
                                                       let uvs1 =
                                                         FStar_List.rev uvs in
                                                       let pre1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst pre in
                                                       let post1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst post in
                                                       let post_u =
                                                         env1.FStar_TypeChecker_Env.universe_of
                                                           env1 post1 in
                                                       let cmp_func =
                                                         if noinst
                                                         then do_match
                                                         else
                                                           if noinst_lhs
                                                           then
                                                             do_match_on_lhs
                                                           else do_unify in
                                                       let uu____5097 =
                                                         let uu____5100 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal in
                                                         let uu____5101 =
                                                           FStar_Syntax_Util.mk_squash
                                                             post_u post1 in
                                                         cmp_func env1
                                                           uu____5100
                                                           uu____5101 in
                                                       FStar_Tactics_Monad.bind
                                                         uu____5097
                                                         (fun b ->
                                                            if
                                                              Prims.op_Negation
                                                                b
                                                            then
                                                              let uu____5110
                                                                =
                                                                let uu____5115
                                                                  =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                let uu____5116
                                                                  =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                FStar_TypeChecker_Err.print_discrepancy
                                                                  (tts env1)
                                                                  uu____5115
                                                                  uu____5116 in
                                                              match uu____5110
                                                              with
                                                              | (post2,
                                                                 goalt) ->
                                                                  let uu____5121
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                  fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____5121
                                                                    post2
                                                                    goalt
                                                            else
                                                              (let uu____5123
                                                                 =
                                                                 solve' goal
                                                                   FStar_Syntax_Util.exp_unit in
                                                               FStar_Tactics_Monad.bind
                                                                 uu____5123
                                                                 (fun
                                                                    uu____5131
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____5158
                                                                    =
                                                                    let uu____5161
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____5161 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5158 in
                                                                    FStar_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu____5198
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5198)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____5214
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu____5214
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5232)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____5258)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5275
                                                                    -> false) in
                                                                    let uu____5276
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits2
                                                                    (FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____5317
                                                                    = imp in
                                                                    match uu____5317
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____5328
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____5328
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5350)
                                                                    ->
                                                                    let uu____5375
                                                                    =
                                                                    let uu____5376
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____5376.FStar_Syntax_Syntax.n in
                                                                    (match uu____5375
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____5384)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___818_5404
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___818_5404.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___818_5404.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___818_5404.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___818_5404.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5407
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5413
                                                                    ->
                                                                    let uu____5414
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____5415
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5414
                                                                    uu____5415)
                                                                    (fun
                                                                    uu____5419
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____5421
                                                                    =
                                                                    let uu____5424
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5425
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____5426
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5425
                                                                    uu____5426
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____5424
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5421
                                                                    (fun
                                                                    uu____5431
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5276
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5493
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____5493
                                                                    then
                                                                    let uu____5496
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____5496
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____5510
                                                                    =
                                                                    let uu____5511
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____5511
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____5510)
                                                                    sub_goals1 in
                                                                    let uu____5512
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5512
                                                                    (fun
                                                                    uu____5518
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____5520
                                                                    =
                                                                    let uu____5523
                                                                    =
                                                                    let uu____5524
                                                                    =
                                                                    let uu____5525
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____5525 in
                                                                    Prims.op_Negation
                                                                    uu____5524 in
                                                                    if
                                                                    uu____5523
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5520
                                                                    (fun
                                                                    uu____5530
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
          focus uu____4319 in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
          uu____4316
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____5581 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5581 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5616 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5616
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5638 = aux e' in
               FStar_Util.map_opt uu____5638
                 (fun uu____5669 ->
                    match uu____5669 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5695 = aux e in
      FStar_Util.map_opt uu____5695
        (fun uu____5726 ->
           match uu____5726 with
           | (e', bv, bvs) -> (e', bv, (FStar_List.rev bvs)))
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_List.fold_left
        (fun e1 -> fun b -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu____5801 =
          let uu____5812 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5812 in
        match uu____5801 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5852 =
              let uu____5865 = FStar_Syntax_Subst.close_binders bs in
              let uu____5874 = FStar_Syntax_Subst.close bs t in
              (uu____5865, uu____5874) in
            (match uu____5852 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5918 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5925 = FStar_List.tail bs' in uu____5918 ::
                     uu____5925 in
                 let uu____5946 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5946 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5962 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5962 in
                      let new_env =
                        let uu____5978 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5978 in
                      let uu____5989 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5989
                        (fun uu____6012 ->
                           match uu____6012 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____6031 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____6034 =
                                   FStar_List.map
                                     (fun uu____6055 ->
                                        match uu____6055 with
                                        | (bv, q) ->
                                            let uu____6068 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6068) bs in
                                 FStar_Syntax_Util.mk_app uu____6031
                                   uu____6034 in
                               let uu____6069 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____6069
                                 (fun uu____6079 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____6117 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6125 = h in
           match uu____6125 with
           | (bv, uu____6129) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6137 ->
                    let uu____6138 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____6139 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6138
                      uu____6139)
                 (fun uu____6142 ->
                    let uu____6143 =
                      let uu____6154 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____6154 in
                    match uu____6143 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6180 =
                          let uu____6187 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6187 in
                        (match uu____6180 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6196 =
                               let uu____6197 = FStar_Syntax_Subst.compress x in
                               uu____6197.FStar_Syntax_Syntax.n in
                             (match uu____6196 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6224 =
                                    let uu____6229 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6230 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6229, uu____6230) in
                                  (match uu____6224 with
                                   | (bs', t') ->
                                       let uu____6235 =
                                         let uu____6240 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6241 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6240, uu____6241) in
                                       (match uu____6235 with
                                        | (bs'1, t'1) ->
                                            let uu____6246 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6246 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6256 =
                                                     let uu____6259 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6259 in
                                                   push_bvs e0 uu____6256 in
                                                 let uu____6270 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6270
                                                   (fun uu____6287 ->
                                                      match uu____6287 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6300 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6303 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6324
                                                                   ->
                                                                   match uu____6324
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6332)
                                                                    ->
                                                                    let uu____6337
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6337)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6300
                                                              uu____6303 in
                                                          let uu____6338 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6338
                                                            (fun uu____6342
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6343 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6344 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6117
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6369 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6391 = b in
             match uu____6391 with
             | (bv, q) ->
                 let bv' =
                   let uu____6407 =
                     let uu___940_6408 = bv in
                     let uu____6409 =
                       let uu____6410 =
                         let uu____6415 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6415) in
                       FStar_Ident.mk_ident uu____6410 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6409;
                       FStar_Syntax_Syntax.index =
                         (uu___940_6408.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___940_6408.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6407 in
                 let uu____6416 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6416
                   (fun uu___4_6438 ->
                      match uu___4_6438 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6469 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6469
                            (fun uu____6479 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6369
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6513 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6522 = b in
           match uu____6522 with
           | (bv, uu____6526) ->
               let uu____6531 =
                 let uu____6542 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6542 in
               (match uu____6531 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6568 = FStar_Syntax_Util.type_u () in
                    (match uu____6568 with
                     | (ty, u) ->
                         let uu____6577 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6577
                           (fun uu____6595 ->
                              match uu____6595 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___967_6605 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___967_6605.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___967_6605.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6609 =
                                      let uu____6610 =
                                        let uu____6617 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6617) in
                                      FStar_Syntax_Syntax.NT uu____6610 in
                                    [uu____6609] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___972_6629 = b1 in
                                         let uu____6630 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___972_6629.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___972_6629.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6630
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6637 ->
                                       let new_goal =
                                         let uu____6639 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6640 =
                                           let uu____6641 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6641 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6639 uu____6640 in
                                       let uu____6642 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6642
                                         (fun uu____6647 ->
                                            let uu____6648 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6648)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6513
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6671 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6680 = b in
             match uu____6680 with
             | (bv, uu____6684) ->
                 let uu____6689 =
                   let uu____6700 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6700 in
                 (match uu____6689 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6729 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6729 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___993_6734 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___993_6734.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___993_6734.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6736 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6736)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6671
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6747 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6753 =
           let uu____6760 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6760 in
         match uu____6753 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6776 =
                 let uu____6779 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6779 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6776 in
             let uu____6794 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6794
               (fun uu____6809 ->
                  match uu____6809 with
                  | (r, u_r) ->
                      let uu____6818 =
                        let uu____6821 =
                          let uu____6822 =
                            let uu____6823 =
                              let uu____6832 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6832 in
                            [uu____6823] in
                          let uu____6849 =
                            let uu____6850 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6850.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6822
                            uu____6849 in
                        set_solution goal uu____6821 in
                      FStar_Tactics_Monad.bind uu____6818
                        (fun uu____6855 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____6867 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6867
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6887 ->
              let uu____6888 = FStar_Syntax_Print.binder_to_string b in
              let uu____6889 =
                let uu____6890 =
                  let uu____6891 =
                    let uu____6900 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6900 in
                  FStar_All.pipe_right uu____6891 FStar_List.length in
                FStar_All.pipe_right uu____6890 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6888 uu____6889)
           (fun uu____6917 ->
              let uu____6918 =
                let uu____6929 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6929 in
              match uu____6918 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6973 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6973
                        then
                          let uu____6976 =
                            let uu____6977 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6977 in
                          FStar_Tactics_Monad.fail uu____6976
                        else check bvs2 in
                  let uu____6979 =
                    let uu____6980 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6980 in
                  if uu____6979
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6984 = check bvs in
                     FStar_Tactics_Monad.bind uu____6984
                       (fun uu____6990 ->
                          let env' = push_bvs e' bvs in
                          let uu____6992 =
                            let uu____6999 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6999 in
                          FStar_Tactics_Monad.bind uu____6992
                            (fun uu____7008 ->
                               match uu____7008 with
                               | (ut, uvar_ut) ->
                                   let uu____7017 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____7017
                                     (fun uu____7022 ->
                                        let uu____7023 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____7023))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7030 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____7036 =
           let uu____7043 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____7043 in
         match uu____7036 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____7051) ->
             let uu____7056 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____7056)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7073 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7073 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7091 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7091 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7110 =
             let uu____7113 = FStar_Tactics_Types.goal_env g in
             do_unify uu____7113 l r in
           FStar_Tactics_Monad.bind uu____7110
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7120 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7120 l in
                   let r1 =
                     let uu____7122 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7122 r in
                   let uu____7123 =
                     let uu____7126 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____7126 l1 r1 in
                   FStar_Tactics_Monad.bind uu____7123
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7132 =
                             let uu____7137 =
                               let uu____7142 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____7142 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7137 l1 r1 in
                           match uu____7132 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7153 ->
    let uu____7156 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7164 =
             let uu____7171 =
               let uu____7172 = FStar_Tactics_Types.goal_env g in
               let uu____7173 = FStar_Tactics_Types.goal_type g in
               whnf uu____7172 uu____7173 in
             destruct_eq uu____7171 in
           match uu____7164 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7186 =
                 let uu____7187 = FStar_Tactics_Types.goal_env g in
                 let uu____7188 = FStar_Tactics_Types.goal_type g in
                 tts uu____7187 uu____7188 in
               fail1 "not an equality (%s)" uu____7186) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7156
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7199 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7207 =
           let uu____7214 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7214 in
         FStar_Tactics_Monad.bind uu____7207
           (fun uu____7223 ->
              match uu____7223 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1079_7233 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1079_7233.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1079_7233.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1079_7233.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1079_7233.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7237 ->
                       let t_eq =
                         let uu____7239 =
                           let uu____7240 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7240 in
                         let uu____7241 = FStar_Tactics_Types.goal_type g in
                         let uu____7242 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7239 uu____7241 u
                           uu____7242 in
                       let uu____7243 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7243
                         (fun uu____7248 ->
                            let uu____7249 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7249
                              (fun uu____7253 -> FStar_Tactics_Monad.ret ())))))
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu____7376 = f x y in
              if uu____7376 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7396 -> (acc, l11, l21) in
        let uu____7411 = aux [] l1 l2 in
        match uu____7411 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____7516 = FStar_Tactics_Types.get_phi g1 in
      match uu____7516 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7522 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7522 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7534 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7534 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7565 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7565 phi1 in
                    let t2 =
                      let uu____7575 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7575 phi2 in
                    let uu____7584 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7584
                      (fun uu____7589 ->
                         let uu____7590 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7590
                           (fun uu____7597 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1131_7602 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7603 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1131_7602.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1131_7602.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1131_7602.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1131_7602.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7603;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1131_7602.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1131_7602.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1131_7602.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1131_7602.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1131_7602.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1131_7602.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1131_7602.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1131_7602.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1131_7602.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1131_7602.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1131_7602.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1131_7602.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1131_7602.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1131_7602.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1131_7602.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1131_7602.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1131_7602.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1131_7602.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1131_7602.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1131_7602.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1131_7602.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1131_7602.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1131_7602.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1131_7602.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1131_7602.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1131_7602.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1131_7602.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1131_7602.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1131_7602.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1131_7602.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1131_7602.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1131_7602.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1131_7602.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1131_7602.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1131_7602.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1131_7602.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1131_7602.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1131_7602.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1131_7602.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1131_7602.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1131_7602.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7606 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7606
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7615 ->
                                        let uu____7616 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7617 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7618 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7616 uu____7617 uu____7618)
                                     (fun uu____7620 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7627 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7643 =
               FStar_Tactics_Monad.set
                 (let uu___1146_7648 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1146_7648.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1146_7648.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1146_7648.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1146_7648.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1146_7648.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1146_7648.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1146_7648.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1146_7648.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1146_7648.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1146_7648.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1146_7648.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7643
               (fun uu____7651 ->
                  let uu____7652 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7652
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7657 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7669 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7682 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7682);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1157_7689 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1157_7689.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1157_7689.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1157_7689.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1157_7689.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7669
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7701 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7714 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7720 =
           (FStar_Options.lax ()) ||
             (let uu____7722 = FStar_Tactics_Types.goal_env g in
              uu____7722.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7720)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7737 =
        FStar_Tactics_Monad.mlog
          (fun uu____7742 ->
             let uu____7743 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7743)
          (fun uu____7745 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7751 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7751 ty in
                  let uu____7752 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7752
                    (fun uu____7771 ->
                       match uu____7771 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7785 ->
                                let uu____7786 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7786)
                             (fun uu____7788 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7791 ->
                                     let uu____7792 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7792)
                                  (fun uu____7795 ->
                                     let uu____7796 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7796
                                       (fun uu____7800 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7737
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7823 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7829 =
              let uu____7836 =
                let uu____7837 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7837 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7836 in
            FStar_Tactics_Monad.bind uu____7829
              (fun uu____7853 ->
                 match uu____7853 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7823
        (fun typ ->
           let uu____7865 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7865
             (fun uu____7879 ->
                match uu____7879 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7897 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7916 -> g.FStar_Tactics_Types.opts
             | uu____7919 -> FStar_Options.peek () in
           let uu____7922 = FStar_Syntax_Util.head_and_args t in
           match uu____7922 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7942);
                FStar_Syntax_Syntax.pos = uu____7943;
                FStar_Syntax_Syntax.vars = uu____7944;_},
              uu____7945) ->
               let env2 =
                 let uu___1211_7987 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1211_7987.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1211_7987.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1211_7987.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1211_7987.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1211_7987.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1211_7987.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1211_7987.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1211_7987.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1211_7987.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1211_7987.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1211_7987.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1211_7987.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1211_7987.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1211_7987.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1211_7987.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1211_7987.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1211_7987.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1211_7987.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1211_7987.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1211_7987.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1211_7987.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1211_7987.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1211_7987.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1211_7987.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1211_7987.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1211_7987.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1211_7987.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1211_7987.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1211_7987.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1211_7987.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1211_7987.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1211_7987.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1211_7987.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1211_7987.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1211_7987.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1211_7987.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1211_7987.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1211_7987.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1211_7987.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1211_7987.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1211_7987.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1211_7987.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1211_7987.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1211_7987.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1211_7987.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1211_7987.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7989 = let uu____7992 = bnorm_goal g in [uu____7992] in
               FStar_Tactics_Monad.add_goals uu____7989
           | uu____7993 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7897
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____8042 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____8042
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____8053 = trytac comp in
      FStar_Tactics_Monad.bind uu____8053
        (fun uu___5_8061 ->
           match uu___5_8061 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8087 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8093 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8093
                 (fun uu____8113 ->
                    match uu____8113 with
                    | (t11, ty1, g1) ->
                        let uu____8125 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8125
                          (fun uu____8145 ->
                             match uu____8145 with
                             | (t21, ty2, g2) ->
                                 let uu____8157 =
                                   proc_guard "match_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8157
                                   (fun uu____8162 ->
                                      let uu____8163 =
                                        proc_guard "match_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8163
                                        (fun uu____8169 ->
                                           let uu____8170 =
                                             do_match e ty1 ty2 in
                                           let uu____8173 =
                                             do_match e t11 t21 in
                                           tac_and uu____8170 uu____8173))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "match_env")
          uu____8087
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8199 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8205 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8205
                 (fun uu____8225 ->
                    match uu____8225 with
                    | (t11, ty1, g1) ->
                        let uu____8237 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8237
                          (fun uu____8257 ->
                             match uu____8257 with
                             | (t21, ty2, g2) ->
                                 let uu____8269 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8269
                                   (fun uu____8274 ->
                                      let uu____8275 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8275
                                        (fun uu____8281 ->
                                           let uu____8282 =
                                             do_unify e ty1 ty2 in
                                           let uu____8285 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8282 uu____8285))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8199
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8318 ->
             let uu____8319 = FStar_Options.unsafe_tactic_exec () in
             if uu____8319
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8340 ->
           let uu____8341 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8341)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8351 =
      FStar_Tactics_Monad.mlog
        (fun uu____8356 ->
           let uu____8357 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8357)
        (fun uu____8359 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8363 =
                  let uu____8372 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8372 ty in
                FStar_Tactics_Monad.bind uu____8363
                  (fun uu____8384 ->
                     match uu____8384 with
                     | (ty1, uu____8394, guard) ->
                         let uu____8396 =
                           let uu____8399 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8399 guard in
                         FStar_Tactics_Monad.bind uu____8396
                           (fun uu____8402 ->
                              let uu____8403 =
                                let uu____8406 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8407 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8406 uu____8407 ty1 in
                              FStar_Tactics_Monad.bind uu____8403
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8413 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8413
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8419 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8420 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8419 uu____8420 in
                                      let nty =
                                        let uu____8422 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8422 ty1 in
                                      let uu____8423 =
                                        let uu____8426 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8426 ng nty in
                                      FStar_Tactics_Monad.bind uu____8423
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8432 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8432
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8351
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b ->
    fun msg -> fun k -> if b then FStar_Tactics_Monad.fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu____8495 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8513 =
             let uu____8522 = FStar_Tactics_Types.goal_env g in
             __tc uu____8522 s_tm in
           FStar_Tactics_Monad.bind uu____8513
             (fun uu____8540 ->
                match uu____8540 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8558 =
                      let uu____8561 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8561 guard in
                    FStar_Tactics_Monad.bind uu____8558
                      (fun uu____8574 ->
                         let s_ty1 =
                           let uu____8576 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8576
                             s_ty in
                         let uu____8577 =
                           let uu____8592 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8592 in
                         match uu____8577 with
                         | (h, args) ->
                             let uu____8623 =
                               let uu____8630 =
                                 let uu____8631 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8631.FStar_Syntax_Syntax.n in
                               match uu____8630 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8646;
                                      FStar_Syntax_Syntax.vars = uu____8647;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8657 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8623
                               (fun uu____8677 ->
                                  match uu____8677 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8693 =
                                        let uu____8696 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8696 t_lid in
                                      (match uu____8693 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu____8735 =
                                                  erasable &&
                                                    (let uu____8737 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8737) in
                                                failwhen uu____8735
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8745 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8757 ->
                                                          let uu____8758 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8758
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8773
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8801
                                                                    =
                                                                    let uu____8804
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8804
                                                                    c_lid in
                                                                    match uu____8801
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,
                                                                    c_us,
                                                                    c_ty,
                                                                    _t_lid,
                                                                    nparam,
                                                                    mut1) ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____8877
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8882
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8882
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8905
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8905
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8924
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8947
                                                                    =
                                                                    let uu____8952
                                                                    =
                                                                    let uu____8953
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8953 in
                                                                    let uu____8954
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8952,
                                                                    uu____8954) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8947 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1353_8957
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1353_8957.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1353_8957.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8983
                                                                    ->
                                                                    match uu____8983
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____9002
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____9002,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9027
                                                                    ->
                                                                    fun
                                                                    uu____9028
                                                                    ->
                                                                    match 
                                                                    (uu____9027,
                                                                    uu____9028)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9054),
                                                                    (bv',
                                                                    uu____9056))
                                                                    ->
                                                                    let uu____9077
                                                                    =
                                                                    let uu____9084
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____9084) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9077)
                                                                    bs bs' in
                                                                    let uu____9089
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____9098
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____9089,
                                                                    uu____9098) in
                                                                    (match uu____8924
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____9145
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____9145
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____9218
                                                                    =
                                                                    let uu____9219
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____9219 in
                                                                    failwhen
                                                                    uu____9218
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9236
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___6_9252
                                                                    =
                                                                    match uu___6_9252
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9255)
                                                                    -> true
                                                                    | 
                                                                    uu____9256
                                                                    -> false in
                                                                    let uu____9259
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9259
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____9394
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9456
                                                                    ->
                                                                    match uu____9456
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9476),
                                                                    (t,
                                                                    uu____9478))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9546
                                                                    ->
                                                                    match uu____9546
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9572),
                                                                    (t,
                                                                    uu____9574))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9629
                                                                    ->
                                                                    match uu____9629
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu____9679
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1412_9702
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1412_9702.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9679
                                                                    with
                                                                    | 
                                                                    (uu____9715,
                                                                    uu____9716,
                                                                    uu____9717,
                                                                    uu____9718,
                                                                    pat_t,
                                                                    uu____9720,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9732
                                                                    =
                                                                    let uu____9733
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9733 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9732 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9737
                                                                    =
                                                                    let uu____9746
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9746] in
                                                                    let uu____9765
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9737
                                                                    uu____9765 in
                                                                    let nty =
                                                                    let uu____9771
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9771 in
                                                                    let uu____9774
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9774
                                                                    (fun
                                                                    uu____9803
                                                                    ->
                                                                    match uu____9803
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu____9829
                                                                    =
                                                                    let uu____9840
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9840] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9829 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9876
                                                                    =
                                                                    let uu____9887
                                                                    =
                                                                    let uu____9892
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9892) in
                                                                    (g', br,
                                                                    uu____9887) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9876)))))))
                                                                    | 
                                                                    uu____9913
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8773
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9962
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9962
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu____10035
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10035
                                                                    (fun
                                                                    uu____10046
                                                                    ->
                                                                    let uu____10047
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10047
                                                                    (fun
                                                                    uu____10057
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10064 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8495
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10109::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10137 = init xs in x :: uu____10137
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____10149 =
      let uu____10152 = top_env () in
      FStar_Tactics_Monad.bind uu____10152
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____10168) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu____10233 = last args in
               (match uu____10233 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10263 =
                      let uu____10264 =
                        let uu____10269 =
                          let uu____10270 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10270
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10269, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10264 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10263)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10281, uu____10282) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10334 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10334 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10375 =
                           let uu____10376 =
                             let uu____10381 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10381) in
                           FStar_Reflection_Data.Tv_Abs uu____10376 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10375))
           | FStar_Syntax_Syntax.Tm_type uu____10384 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10408 ->
               let uu____10423 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10423 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10453 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10453 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10506 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10518 =
                 let uu____10519 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10519 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10518
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10540 =
                 let uu____10541 =
                   let uu____10546 =
                     let uu____10547 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10547 in
                   (uu____10546, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10541 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10540
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10581 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10586 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10586 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10639 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10675 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10679 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10679 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10699 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Util.Inl bv1 ->
                                     FStar_All.pipe_left
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu____10705 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10759 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10759
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10778 =
                       let uu____10789 =
                         FStar_List.map
                           (fun uu____10810 ->
                              match uu____10810 with
                              | (p1, b) ->
                                  let uu____10827 = inspect_pat p1 in
                                  (uu____10827, b)) ps in
                       (fv, uu____10789) in
                     FStar_Reflection_Data.Pat_Cons uu____10778
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_10921 ->
                      match uu___7_10921 with
                      | (pat, uu____10943, t5) ->
                          let uu____10961 = inspect_pat pat in
                          (uu____10961, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10970 ->
               ((let uu____10972 =
                   let uu____10977 =
                     let uu____10978 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10979 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10978 uu____10979 in
                   (FStar_Errors.Warning_CantInspect, uu____10977) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10972);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10149
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10992 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10992
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10996 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10996
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11000 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11000
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____11007 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11007
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____11032 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11032
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____11049 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11049
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____11068 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11068
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11072 =
          let uu____11073 =
            let uu____11074 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____11074 in
          FStar_Syntax_Syntax.mk uu____11073 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11072
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____11079 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11079
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11091 =
          let uu____11092 =
            let uu____11093 =
              let uu____11106 =
                let uu____11109 =
                  let uu____11110 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____11110] in
                FStar_Syntax_Subst.close uu____11109 t2 in
              ((false, [lb]), uu____11106) in
            FStar_Syntax_Syntax.Tm_let uu____11093 in
          FStar_Syntax_Syntax.mk uu____11092 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11091
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11150 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____11150 with
         | (lbs, body) ->
             let uu____11165 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11165)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11199 =
                let uu____11200 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____11200 in
              FStar_All.pipe_left wrap uu____11199
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____11215 =
                let uu____11216 =
                  let uu____11229 =
                    FStar_List.map
                      (fun uu____11250 ->
                         match uu____11250 with
                         | (p1, b) ->
                             let uu____11261 = pack_pat p1 in
                             (uu____11261, b)) ps in
                  (fv, uu____11229) in
                FStar_Syntax_Syntax.Pat_cons uu____11216 in
              FStar_All.pipe_left wrap uu____11215
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11307 ->
               match uu___8_11307 with
               | (pat, t1) ->
                   let uu____11324 = pack_pat pat in
                   (uu____11324, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11372 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11372
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11400 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11400
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11446 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11446
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11485 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11485
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11502 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11508 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11508 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11502
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11537 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1717_11544 = ps in
                 let uu____11545 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1717_11544.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1717_11544.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1717_11544.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1717_11544.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1717_11544.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1717_11544.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1717_11544.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1717_11544.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1717_11544.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1717_11544.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1717_11544.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11545
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11537
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env1 ->
    fun typ ->
      let uu____11570 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env1 typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____11570 with
      | (u, ctx_uvars, g_u) ->
          let uu____11602 = FStar_List.hd ctx_uvars in
          (match uu____11602 with
           | (ctx_uvar, uu____11616) ->
               let g =
                 let uu____11618 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar uu____11618 false
                   "" in
               (g, g_u))
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11624 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11624 with
    | (env2, uu____11632) ->
        let env3 =
          let uu___1734_11638 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1734_11638.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1734_11638.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1734_11638.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1734_11638.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1734_11638.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1734_11638.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1734_11638.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1734_11638.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1734_11638.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1734_11638.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1734_11638.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1734_11638.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1734_11638.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1734_11638.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1734_11638.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1734_11638.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1734_11638.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1734_11638.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1734_11638.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1734_11638.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1734_11638.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1734_11638.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1734_11638.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1734_11638.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1734_11638.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1734_11638.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1734_11638.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1734_11638.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1734_11638.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1734_11638.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1734_11638.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1734_11638.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1734_11638.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1734_11638.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1734_11638.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1734_11638.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1734_11638.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1734_11638.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1734_11638.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1734_11638.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1734_11638.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1734_11638.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1734_11638.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1734_11638.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1734_11638.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1734_11638.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1737_11640 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1737_11640.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1737_11640.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1737_11640.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1737_11640.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1737_11640.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1737_11640.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1737_11640.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1737_11640.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1737_11640.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1737_11640.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1737_11640.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1737_11640.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1737_11640.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1737_11640.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1737_11640.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1737_11640.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1737_11640.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1737_11640.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1737_11640.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1737_11640.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1737_11640.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1737_11640.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1737_11640.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1737_11640.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1737_11640.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1737_11640.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1737_11640.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1737_11640.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1737_11640.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1737_11640.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1737_11640.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1737_11640.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1737_11640.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1737_11640.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1737_11640.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1737_11640.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1737_11640.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1737_11640.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1737_11640.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1737_11640.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1737_11640.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1737_11640.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1737_11640.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1737_11640.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1737_11640.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1737_11640.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env5 =
          let uu___1740_11642 = env4 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1740_11642.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1740_11642.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1740_11642.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1740_11642.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1740_11642.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1740_11642.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1740_11642.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1740_11642.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1740_11642.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1740_11642.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1740_11642.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1740_11642.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1740_11642.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1740_11642.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1740_11642.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1740_11642.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1740_11642.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1740_11642.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1740_11642.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1740_11642.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1740_11642.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1740_11642.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1740_11642.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1740_11642.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1740_11642.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1740_11642.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1740_11642.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1740_11642.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1740_11642.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1740_11642.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1740_11642.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1740_11642.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1740_11642.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1740_11642.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1740_11642.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1740_11642.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1740_11642.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1740_11642.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1740_11642.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1740_11642.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1740_11642.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1740_11642.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1740_11642.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1740_11642.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1740_11642.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1740_11642.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac = false
          } in
        env5
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng ->
    fun env1 ->
      fun goals ->
        fun imps ->
          let env2 = tac_env env1 in
          let ps =
            let uu____11673 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11674 = FStar_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____11673;
              FStar_Tactics_Types.local_state = uu____11674
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu____11697 = goal_of_goal_ty env2 typ in
        match uu____11697 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11709 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11709)
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env1 ->
    fun i ->
      let uu____11720 = FStar_Options.peek () in
      FStar_Tactics_Types.mk_goal
        (let uu___1759_11723 = env1 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1759_11723.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1759_11723.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1759_11723.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1759_11723.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1759_11723.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1759_11723.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1759_11723.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1759_11723.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1759_11723.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1759_11723.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1759_11723.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1759_11723.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1759_11723.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1759_11723.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1759_11723.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1759_11723.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1759_11723.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1759_11723.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___1759_11723.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___1759_11723.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1759_11723.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1759_11723.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1759_11723.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1759_11723.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1759_11723.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1759_11723.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1759_11723.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1759_11723.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1759_11723.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1759_11723.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1759_11723.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1759_11723.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1759_11723.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1759_11723.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1759_11723.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1759_11723.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1759_11723.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1759_11723.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1759_11723.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1759_11723.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1759_11723.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1759_11723.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1759_11723.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1759_11723.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1759_11723.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1759_11723.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____11720 false
        i.FStar_TypeChecker_Common.imp_reason
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals = FStar_List.map (goal_of_implicit env2) imps in
        let w =
          let uu____11748 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11748 in
        let ps =
          let uu____11750 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____11751 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps ->
                 fun msg -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____11750;
            FStar_Tactics_Types.local_state = uu____11751
          } in
        (ps, w)