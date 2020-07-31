open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'uuuuuu35 'uuuuuu36 'uuuuuu37 .
    ('uuuuuu35, ('uuuuuu36 * 'uuuuuu37)) FStar_Util.either ->
      ('uuuuuu35, 'uuuuuu36) FStar_Util.either
  =
  fun uu___0_54 ->
    match uu___0_54 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r, uu____69) -> FStar_Util.Inr r
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let initialize_hints_db : 'uuuuuu92 . Prims.string -> 'uuuuuu92 -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu____104 = FStar_Options.record_hints () in
       if uu____104
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       let uu____120 = FStar_Util.read_hints val_filename in
       match uu____120 with
       | FStar_Util.HintsOK hints ->
           let expected_digest = FStar_Util.digest_of_file norm_src_filename in
           ((let uu____124 = FStar_Options.hint_info () in
             if uu____124
             then
               FStar_Util.print3 "(%s) digest is %s from %s.\n"
                 norm_src_filename
                 (if hints.FStar_Util.module_digest = expected_digest
                  then "valid; using hints"
                  else "invalid; using potentially stale hints") val_filename
             else ());
            FStar_ST.op_Colon_Equals replaying_hints
              (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
       | FStar_Util.MalformedJson ->
           let uu____138 = FStar_Options.use_hints () in
           if uu____138
           then
             let uu____139 =
               let uu____144 =
                 FStar_Util.format1
                   "Malformed JSON hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu____144) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu____139
           else ()
       | FStar_Util.UnableToOpen ->
           let uu____147 = FStar_Options.use_hints () in
           if uu____147
           then
             let uu____148 =
               let uu____153 =
                 FStar_Util.format1
                   "Unable to open hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu____153) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu____148
           else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu____161 = FStar_Options.record_hints () in
     if uu____161
     then
       let hints =
         let uu____163 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____163 in
       let hints_db =
         let uu____177 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____177; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun fname ->
    fun f ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let (filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e ->
    fun theory ->
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____258 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_265 ->
                     match uu___1_265 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____267 -> false)))
              ||
              (let uu____269 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____269) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.of_int (10000)) in
        let keep_decl uu___2_286 =
          match uu___2_286 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names ->
              (FStar_List.iter
                 (fun x ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names;
               true)
          | FStar_SMTEncoding_Term.Module uu____294 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____301 -> true in
        FStar_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Module (name, decls) ->
                   let uu____321 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl) in
                   FStar_All.pipe_right uu____321
                     (fun decls1 ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____338 ->
                   let uu____339 = keep_decl d in
                   if uu____339 then d :: out else out) [] theory_rev in
      pruned_theory
let rec (filter_assertions_with_stats :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int *
          Prims.int))
  =
  fun e ->
    fun core ->
      fun theory ->
        match core with
        | FStar_Pervasives_Native.None ->
            let uu____384 = filter_using_facts_from e theory in
            (uu____384, false, Prims.int_zero, Prims.int_zero)
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory in
            let uu____397 =
              let uu____406 =
                let uu____415 =
                  let uu____418 =
                    let uu____419 =
                      let uu____420 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ") in
                      Prims.op_Hat "UNSAT CORE: " uu____420 in
                    FStar_SMTEncoding_Term.Caption uu____419 in
                  [uu____418] in
                (uu____415, Prims.int_zero, Prims.int_zero) in
              FStar_List.fold_left
                (fun uu____439 ->
                   fun d ->
                     match uu____439 with
                     | (theory1, n_retained, n_pruned) ->
                         (match d with
                          | FStar_SMTEncoding_Term.Assume a ->
                              if
                                FStar_List.contains
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  core1
                              then
                                ((d :: theory1),
                                  (n_retained + Prims.int_one), n_pruned)
                              else
                                if
                                  FStar_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + Prims.int_one))
                          | FStar_SMTEncoding_Term.Module (name, decls) ->
                              let uu____503 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1)) in
                              FStar_All.pipe_right uu____503
                                (fun uu____551 ->
                                   match uu____551 with
                                   | (decls1, uu____571, r, p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____582 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____406 theory_rev in
            (match uu____397 with
             | (theory', n_retained, n_pruned) ->
                 (theory', true, n_retained, n_pruned))
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e ->
    fun core ->
      fun theory ->
        let uu____629 = filter_assertions_with_stats e core theory in
        match uu____629 with
        | (theory1, b, uu____648, uu____649) -> (theory1, b)
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e ->
    fun x ->
      let uu____676 = filter_using_facts_from e x in (uu____676, false)
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages: FStar_Errors.error Prims.list }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_reason
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_fuel
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_ifuel
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_hint
let (__proj__Mkerrors__item__error_messages :
  errors -> FStar_Errors.error Prims.list) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
let (error_to_short_string : errors -> Prims.string) =
  fun err ->
    let uu____809 = FStar_Util.string_of_int err.error_fuel in
    let uu____810 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____809
      uu____810
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____823 =
        let uu____824 = FStar_Util.string_of_int err.error_fuel in
        let uu____825 = FStar_Util.string_of_int err.error_ifuel in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____824 uu____825
          (if FStar_Option.isSome err.error_hint then "with hint" else "") in
      [uu____823]
    else []
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env ;
  query_decl: FStar_SMTEncoding_Term.decl ;
  query_name: Prims.string ;
  query_index: Prims.int ;
  query_range: FStar_Range.range ;
  query_fuel: Prims.int ;
  query_ifuel: Prims.int ;
  query_rlimit: Prims.int ;
  query_hint: FStar_SMTEncoding_Z3.unsat_core ;
  query_errors: errors Prims.list ;
  query_all_labels: FStar_SMTEncoding_Term.error_labels ;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list ;
  query_hash: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkquery_settings__item__query_env :
  query_settings -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_env
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_decl
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_name
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_index
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_range
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_fuel
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_ifuel
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_rlimit
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hint
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_errors
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_all_labels
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_suffix
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hash
let (with_fuel_and_diagnostics :
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun settings ->
    fun label_assumptions ->
      let n = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1244 =
        let uu____1247 =
          let uu____1248 =
            let uu____1249 = FStar_Util.string_of_int n in
            let uu____1250 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1249 uu____1250 in
          FStar_SMTEncoding_Term.Caption uu____1248 in
        let uu____1251 =
          let uu____1254 =
            let uu____1255 =
              let uu____1262 =
                let uu____1263 =
                  let uu____1268 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1271 = FStar_SMTEncoding_Term.n_fuel n in
                  (uu____1268, uu____1271) in
                FStar_SMTEncoding_Util.mkEq uu____1263 in
              (uu____1262, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1255 in
          let uu____1272 =
            let uu____1275 =
              let uu____1276 =
                let uu____1283 =
                  let uu____1284 =
                    let uu____1289 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1292 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1289, uu____1292) in
                  FStar_SMTEncoding_Util.mkEq uu____1284 in
                (uu____1283, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1276 in
            [uu____1275; settings.query_decl] in
          uu____1254 :: uu____1272 in
        uu____1247 :: uu____1251 in
      let uu____1293 =
        let uu____1296 =
          let uu____1299 =
            let uu____1302 =
              let uu____1303 =
                let uu____1308 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1308) in
              FStar_SMTEncoding_Term.SetOption uu____1303 in
            [uu____1302;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore] in
          let uu____1309 =
            let uu____1312 =
              let uu____1315 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ()) in
              if uu____1315
              then [FStar_SMTEncoding_Term.GetStatistics]
              else [] in
            FStar_List.append uu____1312 settings.query_suffix in
          FStar_List.append uu____1299 uu____1309 in
        FStar_List.append label_assumptions uu____1296 in
      FStar_List.append uu____1244 uu____1293
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu____1338 = FStar_ST.op_Bang replaying_hints in
      match uu____1338 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1358 ->
               match uu___3_1358 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1364 -> FStar_Pervasives_Native.None)
      | uu____1367 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1384 -> FStar_Pervasives_Native.None
      | uu____1385 ->
          let uu____1386 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1386 with
           | (msg, error_labels) ->
               let err =
                 let uu____1396 =
                   FStar_List.map
                     (fun uu____1420 ->
                        match uu____1420 with
                        | (uu____1437, x, y) ->
                            let uu____1440 = FStar_Errors.get_ctx () in
                            (FStar_Errors.Error_Z3SolverError, x, y,
                              uu____1440)) error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1396
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____1455 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1455
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1456 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let uu____1468 =
                with_fuel_and_diagnostics settings label_assumptions in
              FStar_SMTEncoding_Z3.ask settings.query_range
                (filter_assertions settings.query_env settings.query_hint)
                settings.query_hash settings.query_all_labels uu____1468
                FStar_Pervasives_Native.None false in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err ->
            match err.error_messages with | [] -> false | uu____1491 -> true))
let (errors_to_report : query_settings -> FStar_Errors.error Prims.list) =
  fun settings ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means Z3 could not prove the query, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg in
    let basic_errors =
      let smt_error =
        let uu____1517 = FStar_Options.query_stats () in
        if uu____1517
        then
          let uu____1522 =
            let uu____1523 =
              let uu____1524 =
                FStar_All.pipe_right settings.query_errors
                  (FStar_List.map error_to_short_string) in
              FStar_All.pipe_right uu____1524 (FStar_String.concat ";\n\t") in
            FStar_All.pipe_right uu____1523 format_smt_error in
          FStar_All.pipe_right uu____1522
            (fun uu____1537 -> FStar_Util.Inr uu____1537)
        else
          (let uu____1539 =
             FStar_List.fold_left
               (fun uu____1558 ->
                  fun err ->
                    match uu____1558 with
                    | (ic, cc, uc) ->
                        let err1 =
                          FStar_Util.substring_from err.error_reason
                            (FStar_String.length "unknown because ") in
                        if
                          ((FStar_Util.starts_with err1 "canceled") ||
                             (FStar_Util.starts_with err1 "(resource"))
                            || (FStar_Util.starts_with err1 "timeout")
                        then (ic, (cc + Prims.int_one), uc)
                        else
                          if FStar_Util.starts_with err1 "(incomplete"
                          then ((ic + Prims.int_one), cc, uc)
                          else (ic, cc, (uc + Prims.int_one)))
               (Prims.int_zero, Prims.int_zero, Prims.int_zero)
               settings.query_errors in
           match uu____1539 with
           | (incomplete_count, canceled_count, unknown_count) ->
               FStar_All.pipe_right
                 (match (incomplete_count, canceled_count, unknown_count)
                  with
                  | (uu____1602, uu____1603, uu____1604) when
                      ((uu____1603 = Prims.int_zero) &&
                         (uu____1604 = Prims.int_zero))
                        && (incomplete_count > Prims.int_zero)
                      ->
                      "The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel"
                  | (uu____1606, uu____1605, uu____1607) when
                      ((uu____1606 = Prims.int_zero) &&
                         (uu____1607 = Prims.int_zero))
                        && (canceled_count > Prims.int_zero)
                      ->
                      "The SMT query timed out, you might want to increase the rlimit"
                  | (uu____1608, uu____1609, uu____1610) ->
                      "Try with --query_stats to get more details")
                 (fun uu____1611 -> FStar_Util.Inl uu____1611)) in
      let uu____1612 = find_localized_errors settings.query_errors in
      match uu____1612 with
      | FStar_Pervasives_Native.Some err ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            err.error_messages smt_error
      | FStar_Pervasives_Native.None ->
          let uu____1618 =
            let uu____1621 =
              let uu____1622 = FStar_Errors.get_ctx () in
              (FStar_Errors.Error_UnknownFatal_AssertionFailure,
                "Unknown assertion failed", (settings.query_range),
                uu____1622) in
            [uu____1621] in
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            uu____1618 smt_error in
    (let uu____1628 = FStar_Options.detail_errors () in
     if uu____1628
     then
       let initial_fuel =
         let uu___252_1630 = settings in
         let uu____1631 = FStar_Options.initial_fuel () in
         let uu____1632 = FStar_Options.initial_ifuel () in
         {
           query_env = (uu___252_1630.query_env);
           query_decl = (uu___252_1630.query_decl);
           query_name = (uu___252_1630.query_name);
           query_index = (uu___252_1630.query_index);
           query_range = (uu___252_1630.query_range);
           query_fuel = uu____1631;
           query_ifuel = uu____1632;
           query_rlimit = (uu___252_1630.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___252_1630.query_errors);
           query_all_labels = (uu___252_1630.query_all_labels);
           query_suffix = (uu___252_1630.query_suffix);
           query_hash = (uu___252_1630.query_hash)
         } in
       let ask_z3 label_assumptions =
         let uu____1645 =
           with_fuel_and_diagnostics initial_fuel label_assumptions in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1645 FStar_Pervasives_Native.None
           false in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ());
    basic_errors
let (report_errors : query_settings -> unit) =
  fun qry_settings ->
    let uu____1654 = errors_to_report qry_settings in
    FStar_Errors.add_errors uu____1654
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let process_unsat_core core =
        let accumulator uu____1690 =
          let r = FStar_Util.mk_ref [] in
          let uu____1698 =
            let module_names = FStar_Util.mk_ref [] in
            ((fun m ->
                let ms = FStar_ST.op_Bang module_names in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____1755 ->
                 let uu____1756 = FStar_ST.op_Bang module_names in
                 FStar_All.pipe_right uu____1756
                   (FStar_Util.sort_with FStar_String.compare))) in
          match uu____1698 with | (add, get) -> (add, get) in
        let uu____1811 = accumulator () in
        match uu____1811 with
        | (add_module_name, get_module_names) ->
            let uu____1842 = accumulator () in
            (match uu____1842 with
             | (add_discarded_name, get_discarded_names) ->
                 let parse_axiom_name s =
                   let chars = FStar_String.list_of_string s in
                   let first_upper_index =
                     FStar_Util.try_find_index FStar_Util.is_upper chars in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStar_Util.substring_from s first_upper_index1 in
                       let components =
                         FStar_String.split [46] name_and_suffix in
                       let excluded_suffixes =
                         ["fuel_instrumented";
                         "_pretyping";
                         "_Tm_refine";
                         "_Tm_abs";
                         "@";
                         "_interpretation_Tm_arrow";
                         "MaxFuel_assumption";
                         "MaxIFuel_assumption"] in
                       let exclude_suffix s1 =
                         let s2 = FStar_Util.trim_string s1 in
                         let sopt =
                           FStar_Util.find_map excluded_suffixes
                             (fun sfx ->
                                if FStar_Util.contains s2 sfx
                                then
                                  let uu____1915 =
                                    FStar_List.hd (FStar_Util.split s2 sfx) in
                                  FStar_Pervasives_Native.Some uu____1915
                                else FStar_Pervasives_Native.None) in
                         match sopt with
                         | FStar_Pervasives_Native.None ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3] in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu____1931 ->
                             let uu____1934 = FStar_Util.prefix components in
                             (match uu____1934 with
                              | (module_name, last) ->
                                  let components1 =
                                    let uu____1952 = exclude_suffix last in
                                    FStar_List.append module_name uu____1952 in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____1956::[] -> ()
                                    | uu____1957 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1)) in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____1966 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".") in
                          [uu____1966]) in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1 in
                      ((let uu____1980 =
                          let uu____1981 = get_module_names () in
                          FStar_All.pipe_right uu____1981
                            (FStar_String.concat "\nZ3 Proof Stats:\t") in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____1980);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____1987 =
                          let uu____1988 = get_discarded_names () in
                          FStar_All.pipe_right uu____1988
                            (FStar_String.concat ", ") in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____1987)))) in
      let uu____1993 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ()) in
      if uu____1993
      then
        let uu____1994 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1994 with
        | (status_string, errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s in
            let uu____2003 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2013 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None) in
            (match uu____2003 with
             | (tag, core) ->
                 let range =
                   let uu____2019 =
                     let uu____2020 =
                       FStar_Range.string_of_range settings.query_range in
                     Prims.op_Hat uu____2020 (Prims.op_Hat at_log_file ")") in
                   Prims.op_Hat "(" uu____2019 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu____2024 = FStar_Options.query_stats () in
                   if uu____2024
                   then
                     let f k v a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v " "))) in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu____2042 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one) in
                     Prims.op_Hat uu____2042 "}"
                   else "" in
                 ((let uu____2045 =
                     let uu____2048 =
                       let uu____2051 =
                         let uu____2054 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu____2055 =
                           let uu____2058 =
                             let uu____2061 =
                               let uu____2064 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time in
                               let uu____2065 =
                                 let uu____2068 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu____2069 =
                                   let uu____2072 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu____2073 =
                                     let uu____2076 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu____2076; stats] in
                                   uu____2072 :: uu____2073 in
                                 uu____2068 :: uu____2069 in
                               uu____2064 :: uu____2065 in
                             used_hint_tag :: uu____2061 in
                           tag :: uu____2058 in
                         uu____2054 :: uu____2055 in
                       (settings.query_name) :: uu____2051 in
                     range :: uu____2048 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2045);
                  (let uu____2078 = FStar_Options.print_z3_statistics () in
                   if uu____2078 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____2099 ->
                          match uu____2099 with
                          | (uu____2106, msg, range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
let (store_hint : FStar_Util.hint -> unit) =
  fun hint ->
    let uu____2117 = FStar_ST.op_Bang recorded_hints in
    match uu____2117 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
    | uu____2147 -> ()
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____2161 =
        let uu____2162 = FStar_Options.record_hints () in
        Prims.op_Negation uu____2162 in
      if uu____2161
      then ()
      else
        (let mk_hint core =
           {
             FStar_Util.hint_name = (settings.query_name);
             FStar_Util.hint_index = (settings.query_index);
             FStar_Util.fuel = (settings.query_fuel);
             FStar_Util.ifuel = (settings.query_ifuel);
             FStar_Util.unsat_core = core;
             FStar_Util.query_elapsed_time = Prims.int_zero;
             FStar_Util.hash =
               (match z3result.FStar_SMTEncoding_Z3.z3result_status with
                | FStar_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStar_SMTEncoding_Z3.z3result_query_hash
                | uu____2182 -> FStar_Pervasives_Native.None)
           } in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu____2185 =
               let uu____2186 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____2186 in
             store_hint uu____2185
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2191 -> ())
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun result ->
      let errs = query_errors settings result in
      query_info settings result;
      record_hint settings result;
      detail_hint_replay settings result;
      errs
let (fold_queries :
  query_settings Prims.list ->
    (query_settings -> FStar_SMTEncoding_Z3.z3result) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list, query_settings) FStar_Util.either)
  =
  fun qs ->
    fun ask ->
      fun f ->
        let rec aux acc qs1 =
          match qs1 with
          | [] -> FStar_Util.Inl acc
          | q::qs2 ->
              let res = ask q in
              let uu____2300 = f q res in
              (match uu____2300 with
               | FStar_Pervasives_Native.None -> FStar_Util.Inr q
               | FStar_Pervasives_Native.Some errs -> aux (errs :: acc) qs2) in
        aux [] qs
let (full_query_id : query_settings -> Prims.string) =
  fun settings ->
    let uu____2317 =
      let uu____2318 =
        let uu____2319 =
          let uu____2320 = FStar_Util.string_of_int settings.query_index in
          Prims.op_Hat uu____2320 ")" in
        Prims.op_Hat ", " uu____2319 in
      Prims.op_Hat settings.query_name uu____2318 in
    Prims.op_Hat "(" uu____2317
let collect : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l ->
    let acc = [] in
    let rec add_one acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h, n)::t ->
          if h = x
          then (h, (n + Prims.int_one)) :: t
          else (let uu____2423 = add_one t x in (h, n) :: uu____2423) in
    FStar_List.fold_left add_one acc l
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit)
  =
  fun env ->
    fun all_labels ->
      fun prefix ->
        fun query ->
          fun suffix ->
            FStar_SMTEncoding_Z3.giveZ3 prefix;
            (let uu____2474 =
               let uu____2481 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2490, FStar_Pervasives_Native.None) ->
                     failwith "No query name set!"
                 | (uu____2509, FStar_Pervasives_Native.Some (q, n)) ->
                     let uu____2526 = FStar_Ident.string_of_lid q in
                     (uu____2526, n) in
               match uu____2481 with
               | (qname, index) ->
                   let rlimit =
                     let uu____2536 = FStar_Options.z3_rlimit_factor () in
                     let uu____2537 =
                       let uu____2538 = FStar_Options.z3_rlimit () in
                       uu____2538 * (Prims.parse_int "544656") in
                     uu____2536 * uu____2537 in
                   let next_hint = get_hint_for qname index in
                   let default_settings =
                     let uu____2543 = FStar_TypeChecker_Env.get_range env in
                     let uu____2544 = FStar_Options.initial_fuel () in
                     let uu____2545 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index;
                       query_range = uu____2543;
                       query_fuel = uu____2544;
                       query_ifuel = uu____2545;
                       query_rlimit = rlimit;
                       query_hint = FStar_Pervasives_Native.None;
                       query_errors = [];
                       query_all_labels = all_labels;
                       query_suffix = suffix;
                       query_hash =
                         (match next_hint with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              { FStar_Util.hint_name = uu____2550;
                                FStar_Util.hint_index = uu____2551;
                                FStar_Util.fuel = uu____2552;
                                FStar_Util.ifuel = uu____2553;
                                FStar_Util.unsat_core = uu____2554;
                                FStar_Util.query_elapsed_time = uu____2555;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____2474 with
             | (default_settings, next_hint) ->
                 let use_hints_setting =
                   let uu____2574 =
                     (FStar_Options.use_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   if uu____2574
                   then
                     let uu____2579 =
                       FStar_All.pipe_right next_hint FStar_Util.must in
                     match uu____2579 with
                     | { FStar_Util.hint_name = uu____2584;
                         FStar_Util.hint_index = uu____2585;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2589;
                         FStar_Util.hash = h;_} ->
                         [(let uu___452_2598 = default_settings in
                           {
                             query_env = (uu___452_2598.query_env);
                             query_decl = (uu___452_2598.query_decl);
                             query_name = (uu___452_2598.query_name);
                             query_index = (uu___452_2598.query_index);
                             query_range = (uu___452_2598.query_range);
                             query_fuel = i;
                             query_ifuel = j;
                             query_rlimit = (uu___452_2598.query_rlimit);
                             query_hint = (FStar_Pervasives_Native.Some core);
                             query_errors = (uu___452_2598.query_errors);
                             query_all_labels =
                               (uu___452_2598.query_all_labels);
                             query_suffix = (uu___452_2598.query_suffix);
                             query_hash = (uu___452_2598.query_hash)
                           })]
                   else [] in
                 let initial_fuel_max_ifuel =
                   let uu____2605 =
                     let uu____2606 = FStar_Options.max_ifuel () in
                     let uu____2607 = FStar_Options.initial_ifuel () in
                     uu____2606 > uu____2607 in
                   if uu____2605
                   then
                     let uu____2610 =
                       let uu___456_2611 = default_settings in
                       let uu____2612 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___456_2611.query_env);
                         query_decl = (uu___456_2611.query_decl);
                         query_name = (uu___456_2611.query_name);
                         query_index = (uu___456_2611.query_index);
                         query_range = (uu___456_2611.query_range);
                         query_fuel = (uu___456_2611.query_fuel);
                         query_ifuel = uu____2612;
                         query_rlimit = (uu___456_2611.query_rlimit);
                         query_hint = (uu___456_2611.query_hint);
                         query_errors = (uu___456_2611.query_errors);
                         query_all_labels = (uu___456_2611.query_all_labels);
                         query_suffix = (uu___456_2611.query_suffix);
                         query_hash = (uu___456_2611.query_hash)
                       } in
                     [uu____2610]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2617 =
                     let uu____2618 =
                       let uu____2619 = FStar_Options.max_fuel () in
                       uu____2619 / (Prims.of_int (2)) in
                     let uu____2620 = FStar_Options.initial_fuel () in
                     uu____2618 > uu____2620 in
                   if uu____2617
                   then
                     let uu____2623 =
                       let uu___460_2624 = default_settings in
                       let uu____2625 =
                         let uu____2626 = FStar_Options.max_fuel () in
                         uu____2626 / (Prims.of_int (2)) in
                       let uu____2627 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___460_2624.query_env);
                         query_decl = (uu___460_2624.query_decl);
                         query_name = (uu___460_2624.query_name);
                         query_index = (uu___460_2624.query_index);
                         query_range = (uu___460_2624.query_range);
                         query_fuel = uu____2625;
                         query_ifuel = uu____2627;
                         query_rlimit = (uu___460_2624.query_rlimit);
                         query_hint = (uu___460_2624.query_hint);
                         query_errors = (uu___460_2624.query_errors);
                         query_all_labels = (uu___460_2624.query_all_labels);
                         query_suffix = (uu___460_2624.query_suffix);
                         query_hash = (uu___460_2624.query_hash)
                       } in
                     [uu____2623]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2632 =
                     (let uu____2637 = FStar_Options.max_fuel () in
                      let uu____2638 = FStar_Options.initial_fuel () in
                      uu____2637 > uu____2638) &&
                       (let uu____2641 = FStar_Options.max_ifuel () in
                        let uu____2642 = FStar_Options.initial_ifuel () in
                        uu____2641 >= uu____2642) in
                   if uu____2632
                   then
                     let uu____2645 =
                       let uu___464_2646 = default_settings in
                       let uu____2647 = FStar_Options.max_fuel () in
                       let uu____2648 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___464_2646.query_env);
                         query_decl = (uu___464_2646.query_decl);
                         query_name = (uu___464_2646.query_name);
                         query_index = (uu___464_2646.query_index);
                         query_range = (uu___464_2646.query_range);
                         query_fuel = uu____2647;
                         query_ifuel = uu____2648;
                         query_rlimit = (uu___464_2646.query_rlimit);
                         query_hint = (uu___464_2646.query_hint);
                         query_errors = (uu___464_2646.query_errors);
                         query_all_labels = (uu___464_2646.query_all_labels);
                         query_suffix = (uu___464_2646.query_suffix);
                         query_hash = (uu___464_2646.query_hash)
                       } in
                     [uu____2645]
                   else [] in
                 let min_fuel =
                   let uu____2653 =
                     let uu____2654 = FStar_Options.min_fuel () in
                     let uu____2655 = FStar_Options.initial_fuel () in
                     uu____2654 < uu____2655 in
                   if uu____2653
                   then
                     let uu____2658 =
                       let uu___468_2659 = default_settings in
                       let uu____2660 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___468_2659.query_env);
                         query_decl = (uu___468_2659.query_decl);
                         query_name = (uu___468_2659.query_name);
                         query_index = (uu___468_2659.query_index);
                         query_range = (uu___468_2659.query_range);
                         query_fuel = uu____2660;
                         query_ifuel = Prims.int_one;
                         query_rlimit = (uu___468_2659.query_rlimit);
                         query_hint = (uu___468_2659.query_hint);
                         query_errors = (uu___468_2659.query_errors);
                         query_all_labels = (uu___468_2659.query_all_labels);
                         query_suffix = (uu___468_2659.query_suffix);
                         query_hash = (uu___468_2659.query_hash)
                       } in
                     [uu____2658]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config =
                   (let uu____2672 = FStar_Options.z3_refresh () in
                    if uu____2672
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2674 = with_fuel_and_diagnostics config [] in
                    let uu____2677 =
                      let uu____2680 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2680 in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2674
                      uu____2677 (used_hint config)) in
                 let check_all_configs configs =
                   fold_queries configs check_one_config process_result in
                 let quake_and_check_all_configs configs =
                   let lo = FStar_Options.quake_lo () in
                   let hi = FStar_Options.quake_hi () in
                   let seed = FStar_Options.z3_seed () in
                   let name = full_query_id default_settings in
                   let quaking =
                     (hi > Prims.int_one) &&
                       (let uu____2719 = FStar_Options.retry () in
                        Prims.op_Negation uu____2719) in
                   let quaking_or_retrying = hi > Prims.int_one in
                   let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
                   let lo1 =
                     if lo < Prims.int_one
                     then Prims.int_one
                     else if lo > hi1 then hi1 else lo in
                   let run_one seed1 =
                     let uu____2738 = FStar_Options.z3_refresh () in
                     if uu____2738
                     then
                       FStar_Options.with_saved_options
                         (fun uu____2753 ->
                            FStar_Options.set_option "z3seed"
                              (FStar_Options.Int seed1);
                            check_all_configs configs)
                     else check_all_configs configs in
                   let rec fold_nat' f acc lo2 hi2 =
                     if lo2 > hi2
                     then acc
                     else
                       (let uu____2799 = f acc lo2 in
                        fold_nat' f uu____2799 (lo2 + Prims.int_one) hi2) in
                   let best_fuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let best_ifuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let maybe_improve r n =
                     let uu____2857 = FStar_ST.op_Bang r in
                     match uu____2857 with
                     | FStar_Pervasives_Native.None ->
                         FStar_ST.op_Colon_Equals r
                           (FStar_Pervasives_Native.Some n)
                     | FStar_Pervasives_Native.Some m ->
                         if n < m
                         then
                           FStar_ST.op_Colon_Equals r
                             (FStar_Pervasives_Native.Some n)
                         else () in
                   let uu____2892 =
                     fold_nat'
                       (fun uu____2927 ->
                          fun n ->
                            match uu____2927 with
                            | (nsucc, nfail, rs) ->
                                let uu____2976 =
                                  (let uu____2979 =
                                     FStar_Options.quake_keep () in
                                   Prims.op_Negation uu____2979) &&
                                    ((nsucc >= lo1) || (nfail > (hi1 - lo1))) in
                                if uu____2976
                                then (nsucc, nfail, rs)
                                else
                                  ((let uu____3004 =
                                      (quaking_or_retrying &&
                                         ((FStar_Options.interactive ()) ||
                                            (FStar_Options.debug_any ())))
                                        && (n > Prims.int_zero) in
                                    if uu____3004
                                    then
                                      let uu____3005 =
                                        if quaking
                                        then
                                          let uu____3006 =
                                            FStar_Util.string_of_int nsucc in
                                          FStar_Util.format1
                                            "succeeded %s times and "
                                            uu____3006
                                        else "" in
                                      let uu____3008 =
                                        if quaking
                                        then FStar_Util.string_of_int nfail
                                        else
                                          (let uu____3010 =
                                             FStar_Util.string_of_int nfail in
                                           Prims.op_Hat uu____3010 " times") in
                                      let uu____3011 =
                                        FStar_Util.string_of_int (hi1 - n) in
                                      FStar_Util.print5
                                        "%s: so far query %s %sfailed %s (%s runs remain)\n"
                                        (if quaking then "Quake" else "Retry")
                                        name uu____3005 uu____3008 uu____3011
                                    else ());
                                   (let r = run_one (seed + n) in
                                    let uu____3021 =
                                      match r with
                                      | FStar_Util.Inr cfg ->
                                          (maybe_improve best_fuel
                                             cfg.query_fuel;
                                           maybe_improve best_ifuel
                                             cfg.query_ifuel;
                                           ((nsucc + Prims.int_one), nfail))
                                      | uu____3035 ->
                                          (nsucc, (nfail + Prims.int_one)) in
                                    match uu____3021 with
                                    | (nsucc1, nfail1) ->
                                        (nsucc1, nfail1, (r :: rs)))))
                       (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
                       (hi1 - Prims.int_one) in
                   match uu____2892 with
                   | (nsuccess, nfailures, rs) ->
                       let total_ran = nsuccess + nfailures in
                       (if quaking
                        then
                          (let fuel_msg =
                             let uu____3108 =
                               let uu____3117 = FStar_ST.op_Bang best_fuel in
                               let uu____3130 = FStar_ST.op_Bang best_ifuel in
                               (uu____3117, uu____3130) in
                             match uu____3108 with
                             | (FStar_Pervasives_Native.Some f,
                                FStar_Pervasives_Native.Some i) ->
                                 let uu____3153 = FStar_Util.string_of_int f in
                                 let uu____3154 = FStar_Util.string_of_int i in
                                 FStar_Util.format2
                                   " (best fuel=%s, best ifuel=%s)"
                                   uu____3153 uu____3154
                             | (uu____3155, uu____3156) -> "" in
                           let uu____3165 = FStar_Util.string_of_int nsuccess in
                           let uu____3166 =
                             FStar_Util.string_of_int total_ran in
                           FStar_Util.print5
                             "Quake: query %s succeeded %s/%s times%s%s\n"
                             name uu____3165 uu____3166
                             (if total_ran < hi1
                              then " (early finish)"
                              else "") fuel_msg)
                        else ();
                        if nsuccess < lo1
                        then
                          (let all_errs =
                             FStar_List.concatMap
                               (fun uu___4_3184 ->
                                  match uu___4_3184 with
                                  | FStar_Util.Inr uu____3195 -> []
                                  | FStar_Util.Inl es -> [es]) rs in
                           let uu____3209 =
                             quaking_or_retrying &&
                               (let uu____3211 = FStar_Options.query_stats () in
                                Prims.op_Negation uu____3211) in
                           if uu____3209
                           then
                             let errors_to_report1 errs =
                               errors_to_report
                                 (let uu___559_3226 = default_settings in
                                  {
                                    query_env = (uu___559_3226.query_env);
                                    query_decl = (uu___559_3226.query_decl);
                                    query_name = (uu___559_3226.query_name);
                                    query_index = (uu___559_3226.query_index);
                                    query_range = (uu___559_3226.query_range);
                                    query_fuel = (uu___559_3226.query_fuel);
                                    query_ifuel = (uu___559_3226.query_ifuel);
                                    query_rlimit =
                                      (uu___559_3226.query_rlimit);
                                    query_hint = (uu___559_3226.query_hint);
                                    query_errors = errs;
                                    query_all_labels =
                                      (uu___559_3226.query_all_labels);
                                    query_suffix =
                                      (uu___559_3226.query_suffix);
                                    query_hash = (uu___559_3226.query_hash)
                                  }) in
                             let errs =
                               FStar_List.map errors_to_report1 all_errs in
                             let errs1 =
                               let uu____3253 =
                                 FStar_All.pipe_right errs FStar_List.flatten in
                               FStar_All.pipe_right uu____3253 collect in
                             let errs2 =
                               FStar_All.pipe_right errs1
                                 (FStar_List.map
                                    (fun uu____3332 ->
                                       match uu____3332 with
                                       | ((e, m, r, ctx), n) ->
                                           if n > Prims.int_one
                                           then
                                             let uu____3386 =
                                               let uu____3387 =
                                                 let uu____3388 =
                                                   FStar_Util.string_of_int n in
                                                 FStar_Util.format1
                                                   " (%s times)" uu____3388 in
                                               Prims.op_Hat m uu____3387 in
                                             (e, uu____3386, r, ctx)
                                           else (e, m, r, ctx))) in
                             (FStar_Errors.add_errors errs2;
                              (let rng =
                                 match FStar_Pervasives_Native.snd
                                         env.FStar_TypeChecker_Env.qtbl_name_and_index
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (l, uu____3405) ->
                                     FStar_Ident.range_of_lid l
                                 | uu____3410 -> FStar_Range.dummyRange in
                               if quaking
                               then
                                 let uu____3417 =
                                   let uu____3422 =
                                     let uu____3423 =
                                       FStar_Util.string_of_int nsuccess in
                                     let uu____3424 =
                                       FStar_Util.string_of_int total_ran in
                                     let uu____3425 =
                                       FStar_Util.string_of_int lo1 in
                                     let uu____3426 =
                                       FStar_Util.string_of_int hi1 in
                                     FStar_Util.format6
                                       "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                                       name uu____3423 uu____3424 uu____3425
                                       uu____3426
                                       (if total_ran < hi1
                                        then " (early abort)"
                                        else "") in
                                   (FStar_Errors.Error_QuakeFailed,
                                     uu____3422) in
                                 FStar_TypeChecker_Err.log_issue env rng
                                   uu____3417
                               else ()))
                           else
                             (let report errs =
                                report_errors
                                  (let uu___583_3442 = default_settings in
                                   {
                                     query_env = (uu___583_3442.query_env);
                                     query_decl = (uu___583_3442.query_decl);
                                     query_name = (uu___583_3442.query_name);
                                     query_index =
                                       (uu___583_3442.query_index);
                                     query_range =
                                       (uu___583_3442.query_range);
                                     query_fuel = (uu___583_3442.query_fuel);
                                     query_ifuel =
                                       (uu___583_3442.query_ifuel);
                                     query_rlimit =
                                       (uu___583_3442.query_rlimit);
                                     query_hint = (uu___583_3442.query_hint);
                                     query_errors = errs;
                                     query_all_labels =
                                       (uu___583_3442.query_all_labels);
                                     query_suffix =
                                       (uu___583_3442.query_suffix);
                                     query_hash = (uu___583_3442.query_hash)
                                   }) in
                              FStar_List.iter report all_errs))
                        else ()) in
                 let skip =
                   (FStar_Options.admit_smt_queries ()) ||
                     (let uu____3450 = FStar_Options.admit_except () in
                      match uu____3450 with
                      | FStar_Pervasives_Native.Some id ->
                          if FStar_Util.starts_with id "("
                          then
                            let uu____3454 = full_query_id default_settings in
                            uu____3454 <> id
                          else default_settings.query_name <> id
                      | FStar_Pervasives_Native.None -> false) in
                 if skip
                 then
                   let uu____3456 =
                     (FStar_Options.record_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   (if uu____3456
                    then
                      let uu____3459 =
                        FStar_All.pipe_right next_hint FStar_Util.must in
                      FStar_All.pipe_right uu____3459 store_hint
                    else ())
                 else quake_and_check_all_configs all_configs)
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  valid_intro: Prims.bool ;
  valid_elim: Prims.bool }
let (__proj__Mksolver_cfg__item__seed : solver_cfg -> Prims.int) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> seed
let (__proj__Mksolver_cfg__item__cliopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> cliopt
let (__proj__Mksolver_cfg__item__facts :
  solver_cfg -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> facts
let (__proj__Mksolver_cfg__item__valid_intro : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_intro
let (__proj__Mksolver_cfg__item__valid_elim : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_elim
let (_last_cfg : solver_cfg FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (get_cfg : FStar_TypeChecker_Env.env -> solver_cfg) =
  fun env ->
    let uu____3630 = FStar_Options.z3_seed () in
    let uu____3631 = FStar_Options.z3_cliopt () in
    let uu____3634 = FStar_Options.smtencoding_valid_intro () in
    let uu____3635 = FStar_Options.smtencoding_valid_elim () in
    {
      seed = uu____3630;
      cliopt = uu____3631;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____3634;
      valid_elim = uu____3635
    }
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____3641 =
      let uu____3644 = get_cfg env in FStar_Pervasives_Native.Some uu____3644 in
    FStar_ST.op_Colon_Equals _last_cfg uu____3641
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    let uu____3660 = FStar_ST.op_Bang _last_cfg in
    match uu____3660 with
    | FStar_Pervasives_Native.None -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____3675 = let uu____3676 = get_cfg env in cfg = uu____3676 in
        Prims.op_Negation uu____3675
let (do_solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____3702 = should_refresh tcenv in
         if uu____3702
         then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
         else ());
        (let uu____3706 =
           let uu____3707 =
             let uu____3708 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3708 in
           FStar_Util.format1 "Starting query at %s" uu____3707 in
         FStar_SMTEncoding_Encode.push uu____3706);
        (let pop uu____3714 =
           let uu____3715 =
             let uu____3716 =
               let uu____3717 = FStar_TypeChecker_Env.get_range tcenv in
               FStar_All.pipe_left FStar_Range.string_of_range uu____3717 in
             FStar_Util.format1 "Ending query at %s" uu____3716 in
           FStar_SMTEncoding_Encode.pop uu____3715 in
         try
           (fun uu___624_3731 ->
              match () with
              | () ->
                  let uu____3732 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
                  (match uu____3732 with
                   | (prefix, labels, qry, suffix) ->
                       let tcenv1 =
                         FStar_TypeChecker_Env.incr_query_index tcenv in
                       (match qry with
                        | FStar_SMTEncoding_Term.Assume
                            {
                              FStar_SMTEncoding_Term.assumption_term =
                                {
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.FalseOp,
                                     uu____3764);
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3765;
                                  FStar_SMTEncoding_Term.rng = uu____3766;_};
                              FStar_SMTEncoding_Term.assumption_caption =
                                uu____3767;
                              FStar_SMTEncoding_Term.assumption_name =
                                uu____3768;
                              FStar_SMTEncoding_Term.assumption_fact_ids =
                                uu____3769;_}
                            -> pop ()
                        | uu____3786 when tcenv1.FStar_TypeChecker_Env.admit
                            -> pop ()
                        | FStar_SMTEncoding_Term.Assume uu____3787 ->
                            (ask_and_report_errors tcenv1 labels prefix qry
                               suffix;
                             pop ())
                        | uu____3789 -> failwith "Impossible"))) ()
         with
         | FStar_SMTEncoding_Env.Inner_let_rec names ->
             (pop ();
              (let uu____3803 =
                 let uu____3808 =
                   let uu____3809 =
                     let uu____3810 =
                       FStar_List.map FStar_Pervasives_Native.fst names in
                     FStar_String.concat "," uu____3810 in
                   FStar_Util.format1
                     "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                     uu____3809 in
                 (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                   uu____3808) in
               FStar_TypeChecker_Err.log_issue tcenv
                 tcenv.FStar_TypeChecker_Env.range uu____3803)))
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu____3841 = FStar_Options.no_smt () in
        if uu____3841
        then
          let uu____3842 =
            let uu____3847 =
              let uu____3848 = FStar_Syntax_Print.term_to_string q in
              FStar_Util.format1
                "Q = %s\nA query could not be solved internally, and --no_smt was given"
                uu____3848 in
            (FStar_Errors.Error_NoSMTButNeeded, uu____3847) in
          FStar_TypeChecker_Err.log_issue tcenv
            tcenv.FStar_TypeChecker_Env.range uu____3842
        else
          (let uu____3850 =
             let uu____3853 =
               let uu____3854 = FStar_TypeChecker_Env.current_module tcenv in
               FStar_Ident.string_of_lid uu____3854 in
             FStar_Pervasives_Native.Some uu____3853 in
           FStar_Profiling.profile
             (fun uu____3856 -> do_solve use_env_msg tcenv q) uu____3850
             "FStar.TypeChecker.SMTEncoding.solve_top_level")
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init =
      (fun e -> save_cfg e; FStar_SMTEncoding_Encode.init e);
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____3868 =
             let uu____3875 = FStar_Options.peek () in (e, g, uu____3875) in
           [uu____3868]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3890 -> ());
    FStar_TypeChecker_Env.push = (fun uu____3892 -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3894 -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3896 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback = (fun uu____3905 -> fun uu____3906 -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3917 -> fun uu____3918 -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____3924 =
             let uu____3931 = FStar_Options.peek () in (e, g, uu____3931) in
           [uu____3924]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3947 -> fun uu____3948 -> fun uu____3949 -> ());
    FStar_TypeChecker_Env.finish = (fun uu____3955 -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3957 -> ())
  }