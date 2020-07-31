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
      let uu____111 = FStar_Options.tactics_failhard () in
      if uu____111
      then run t ps
      else
        (try (fun uu___20_118 -> match () with | () -> run t ps) ()
         with
         | FStar_Errors.Err (uu____128, msg, uu____130) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | FStar_Errors.Error (uu____135, msg, uu____137, uu____138) ->
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
           let uu____199 = run t1 ps in
           match uu____199 with
           | FStar_Tactics_Result.Success (a1, q) ->
               let uu____206 = t2 a1 in run uu____206 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (idtac : unit tac) = ret ()
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu____225 -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu____262 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____262
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
          let uu____309 = f x in
          bind uu____309
            (fun y ->
               let uu____317 = mapM f xs in
               bind uu____317 (fun ys -> ret (y :: ys)))
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu____339 = FStar_Options.defensive () in
    if uu____339
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu____344 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu____344) in
      let b2 =
        b1 &&
          (let uu____347 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu____347) in
      let rec aux b3 e =
        let uu____359 = FStar_TypeChecker_Env.pop_bv e in
        match uu____359 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu____377 =
        (let uu____380 = aux b2 env in Prims.op_Negation uu____380) &&
          (let uu____382 = FStar_ST.op_Bang nwarn in
           uu____382 < (Prims.of_int (5))) in
      (if uu____377
       then
         ((let uu____390 =
             let uu____391 = FStar_Tactics_Types.goal_type g in
             uu____391.FStar_Syntax_Syntax.pos in
           let uu____394 =
             let uu____399 =
               let uu____400 =
                 FStar_Tactics_Printing.goal_to_string_verbose g in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____400 in
             (FStar_Errors.Warning_IllFormedGoal, uu____399) in
           FStar_Errors.log_issue uu____390 uu____394);
          (let uu____401 =
             let uu____402 = FStar_ST.op_Bang nwarn in
             uu____402 + Prims.int_one in
           FStar_ST.op_Colon_Equals nwarn uu____401))
       else ())
    else ()
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu____426 = FStar_Options.defensive () in
    if uu____426 then FStar_List.iter check_valid_goal gs else ()
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___98_445 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_445.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___98_445.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___98_445.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_445.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_445.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc = (uu___98_445.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___98_445.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___98_445.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___98_445.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___98_445.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___98_445.FStar_Tactics_Types.local_state)
            }))
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___102_463 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_463.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___102_463.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___102_463.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___102_463.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_463.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_463.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_463.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_463.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_463.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___102_463.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___102_463.FStar_Tactics_Types.local_state)
            }))
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___0_481 ->
       match uu___0_481 with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu____490 = FStar_Tactics_Types.check_goal_solved' hd in
           (match uu____490 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu____497 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd in
                  let uu____498 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu____497 uu____498);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStar_List.filter
           (fun g ->
              let uu____516 = FStar_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu____516) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu____528 =
         let uu___118_529 = ps in
         let uu____530 = FStar_List.tl ps.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___118_529.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___118_529.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____530;
           FStar_Tactics_Types.smt_goals =
             (uu___118_529.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___118_529.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___118_529.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___118_529.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___118_529.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___118_529.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___118_529.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___118_529.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___118_529.FStar_Tactics_Types.local_state)
         } in
       set uu____528)
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu____547 =
            let uu___123_548 = ps in
            let uu____549 =
              let uu____552 = FStar_List.tl ps.FStar_Tactics_Types.goals in g
                :: uu____552 in
            {
              FStar_Tactics_Types.main_context =
                (uu___123_548.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___123_548.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu____549;
              FStar_Tactics_Types.smt_goals =
                (uu___123_548.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___123_548.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___123_548.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___123_548.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___123_548.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___123_548.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___123_548.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___123_548.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___123_548.FStar_Tactics_Types.local_state)
            } in
          set uu____547))
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___128_574 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___128_574.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___128_574.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___128_574.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___128_574.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___128_574.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___128_574.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___128_574.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___128_574.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___128_574.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___128_574.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___128_574.FStar_Tactics_Types.local_state)
            }))
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___133_594 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___133_594.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___133_594.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___133_594.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___133_594.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___133_594.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___133_594.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___133_594.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___133_594.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___133_594.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___133_594.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___133_594.FStar_Tactics_Types.local_state)
            }))
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___138_614 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_614.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___138_614.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append ps.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___138_614.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_614.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_614.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_614.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___138_614.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___138_614.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___138_614.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___138_614.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___138_614.FStar_Tactics_Types.local_state)
            }))
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___143_634 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___143_634.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___143_634.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___143_634.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append ps.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___143_634.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___143_634.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___143_634.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___143_634.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___143_634.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___143_634.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___143_634.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___143_634.FStar_Tactics_Types.local_state)
            }))
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           (let uu___147_648 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___147_648.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___147_648.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___147_648.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___147_648.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___147_648.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___147_648.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___147_648.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___147_648.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___147_648.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___147_648.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___147_648.FStar_Tactics_Types.local_state)
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
        let uu____676 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
        match uu____676 with
        | (u, ctx_uvar, g_u) ->
            let uu____710 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits in
            bind uu____710
              (fun uu____719 ->
                 let uu____720 =
                   let uu____725 =
                     let uu____726 = FStar_List.hd ctx_uvar in
                     FStar_Pervasives_Native.fst uu____726 in
                   (u, uu____725) in
                 ret uu____720)
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
              let uu____771 = env.FStar_TypeChecker_Env.universe_of env phi in
              FStar_Syntax_Util.mk_squash uu____771 phi in
            let uu____772 = new_uvar reason env typ in
            bind uu____772
              (fun uu____787 ->
                 match uu____787 with
                 | (uu____794, ctx_uvar) ->
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
            let uu____826 = mk_irrelevant_goal reason env phi opts label in
            bind uu____826 (fun goal -> add_goals [goal])
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
           let uu____883 = run t ps in
           match uu____883 with
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
         let uu___206_959 = FStar_TypeChecker_Env.trivial_guard in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___206_959.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (uu___206_959.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (uu___206_959.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___206_959.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         } in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___210_962 = ps in
         {
           FStar_Tactics_Types.main_context =
             (uu___210_962.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___210_962.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___210_962.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___210_962.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___210_962.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___210_962.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___210_962.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___210_962.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___210_962.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___210_962.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___210_962.FStar_Tactics_Types.local_state)
         } in
       set ps')