open Prims
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee -> match projectee with | { tac_f;_} -> tac_f
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f -> { tac_f = f }
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t -> fun ps -> t.tac_f ps
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      let uu____112 = FStar_Options.tactics_failhard () in
      if uu____112
      then run t ps
      else
        (try (fun uu___20_119 -> match () with | () -> run t ps) ()
         with
         | FStar_Errors.Err (uu____129, msg, uu____131) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | FStar_Errors.Error (uu____136, msg, uu____138, uu____139) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | e -> FStar_Tactics_Result.Failed (e, ps))
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun ps -> FStar_Tactics_Result.Success (x, ps))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun ps ->
           let uu____200 = run t1 ps in
           match uu____200 with
           | FStar_Tactics_Result.Success (a1, q) ->
               let uu____207 = t2 a1 in run uu____207 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (idtac : unit tac) = ret ()
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu____226 -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu____263 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____263
          then
            FStar_Tactics_Printing.do_dump_proofstate ps
              (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Common.TacticFailure msg), ps))
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____310 = f x in
          bind uu____310
            (fun y ->
               let uu____318 = mapM f xs in
               bind uu____318 (fun ys -> ret (y :: ys)))
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu____340 = FStar_Options.defensive () in
    if uu____340
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu____345 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu____345) in
      let b2 =
        b1 &&
          (let uu____348 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu____348) in
      let rec aux b3 e =
        let uu____360 = FStar_TypeChecker_Env.pop_bv e in
        match uu____360 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu____378 =
        (let uu____381 = aux b2 env in Prims.op_Negation uu____381) &&
          (let uu____383 = FStar_ST.op_Bang nwarn in
           uu____383 < (Prims.of_int (5))) in
      (if uu____378
       then
         ((let uu____391 =
             let uu____392 = FStar_Tactics_Types.goal_type g in
             uu____392.FStar_Syntax_Syntax.pos in
           let uu____395 =
             let uu____400 =
               let uu____401 =
                 FStar_Tactics_Printing.goal_to_string_verbose g in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____401 in
             (FStar_Errors.Warning_IllFormedGoal, uu____400) in
           FStar_Errors.log_issue uu____391 uu____395);
          (let uu____402 =
             let uu____403 = FStar_ST.op_Bang nwarn in
             uu____403 + Prims.int_one in
           FStar_ST.op_Colon_Equals nwarn uu____402))
       else ())
    else ()
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu____427 = FStar_Options.defensive () in
    if uu____427 then FStar_List.iter check_valid_goal gs else ()
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___98_446 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_446.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___98_446.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___98_446.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_446.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_446.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc = (uu___98_446.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___98_446.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___98_446.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___98_446.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___98_446.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___98_446.FStar_Tactics_Types.local_state)
            }))
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___102_464 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_464.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___102_464.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___102_464.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___102_464.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_464.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_464.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_464.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_464.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_464.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___102_464.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___102_464.FStar_Tactics_Types.local_state)
            }))
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___0_482 ->
       match uu___0_482 with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu____491 = FStar_Tactics_Types.check_goal_solved' hd in
           (match uu____491 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu____498 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd in
                  let uu____499 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu____498 uu____499);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStar_List.filter
           (fun g ->
              let uu____517 = FStar_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu____517) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu____529 =
         let uu___118_530 = ps in
         let uu____531 = FStar_List.tl ps.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___118_530.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___118_530.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____531;
           FStar_Tactics_Types.smt_goals =
             (uu___118_530.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___118_530.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___118_530.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___118_530.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___118_530.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___118_530.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___118_530.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___118_530.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___118_530.FStar_Tactics_Types.local_state)
         } in
       set uu____529)
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu____548 =
            let uu___123_549 = ps in
            let uu____550 =
              let uu____553 = FStar_List.tl ps.FStar_Tactics_Types.goals in g
                :: uu____553 in
            {
              FStar_Tactics_Types.main_context =
                (uu___123_549.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___123_549.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu____550;
              FStar_Tactics_Types.smt_goals =
                (uu___123_549.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___123_549.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___123_549.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___123_549.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___123_549.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___123_549.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___123_549.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___123_549.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___123_549.FStar_Tactics_Types.local_state)
            } in
          set uu____548))
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___128_575 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___128_575.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___128_575.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___128_575.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___128_575.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___128_575.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___128_575.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___128_575.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___128_575.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___128_575.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___128_575.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___128_575.FStar_Tactics_Types.local_state)
            }))
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___133_595 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___133_595.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___133_595.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___133_595.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___133_595.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___133_595.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___133_595.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___133_595.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___133_595.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___133_595.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___133_595.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___133_595.FStar_Tactics_Types.local_state)
            }))
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___138_615 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_615.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___138_615.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append ps.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___138_615.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_615.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_615.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_615.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___138_615.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___138_615.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___138_615.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___138_615.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___138_615.FStar_Tactics_Types.local_state)
            }))
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___143_635 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___143_635.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___143_635.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___143_635.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append ps.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___143_635.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___143_635.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___143_635.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___143_635.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___143_635.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___143_635.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___143_635.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___143_635.FStar_Tactics_Types.local_state)
            }))
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           (let uu___147_649 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___147_649.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___147_649.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___147_649.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___147_649.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___147_649.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___147_649.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___147_649.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___147_649.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___147_649.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___147_649.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___147_649.FStar_Tactics_Types.local_state)
            }))
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        let uu____677 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
        match uu____677 with
        | (u, ctx_uvar, g_u) ->
            let uu____711 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits in
            bind uu____711
              (fun uu____720 ->
                 let uu____721 =
                   let uu____726 =
                     let uu____727 = FStar_List.hd ctx_uvar in
                     FStar_Pervasives_Native.fst uu____727 in
                   (u, uu____726) in
                 ret uu____721)
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let typ =
              let uu____772 = env.FStar_TypeChecker_Env.universe_of env phi in
              FStar_Syntax_Util.mk_squash uu____772 phi in
            let uu____773 = new_uvar reason env typ in
            bind uu____773
              (fun uu____788 ->
                 match uu____788 with
                 | (uu____795, ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label in
                     ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let uu____827 = mk_irrelevant_goal reason env phi opts label in
            bind uu____827 (fun goal -> add_goals [goal])
let (add_irrelevant_goal :
  FStar_Tactics_Types.goal ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> unit tac)
  =
  fun base_goal ->
    fun reason ->
      fun env ->
        fun phi ->
          add_irrelevant_goal' reason env phi
            base_goal.FStar_Tactics_Types.opts
            base_goal.FStar_Tactics_Types.label
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu____884 = run t ps in
           match uu____884 with
           | FStar_Tactics_Result.Success (a1, q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Common.TacticFailure msg, q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Common.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f -> fun cont -> bind get (fun ps -> log ps f; cont ())
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStar_Tactics_Types.all_implicits in
       let g =
         let uu___206_960 = FStar_TypeChecker_Env.trivial_guard in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___206_960.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (uu___206_960.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (uu___206_960.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___206_960.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         } in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___210_963 = ps in
         {
           FStar_Tactics_Types.main_context =
             (uu___210_963.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___210_963.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___210_963.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___210_963.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___210_963.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___210_963.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___210_963.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___210_963.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___210_963.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___210_963.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___210_963.FStar_Tactics_Types.local_state)
         } in
       set ps')