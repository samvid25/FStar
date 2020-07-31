open Prims
let (tc_one_file :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
        FStar_TypeChecker_Env.env_t * Prims.string Prims.list))
  =
  fun remaining ->
    fun env ->
      let uu____32 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____66 =
              FStar_Universal.tc_one_file_for_ide env
                (FStar_Pervasives_Native.Some intf) impl
                FStar_Parser_Dep.empty_parsing_data in
            (match uu____66 with
             | (uu____85, env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu____101 =
              FStar_Universal.tc_one_file_for_ide env
                FStar_Pervasives_Native.None intf_or_impl
                FStar_Parser_Dep.empty_parsing_data in
            (match uu____101 with
             | (uu____120, env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible" in
      match uu____32 with
      | ((intf, impl), env1, remaining1) -> ((intf, impl), env1, remaining1)
type env_t = FStar_TypeChecker_Env.env
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t * modul_t) Prims.list
let (pop : FStar_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env ->
    fun msg ->
      (let uu____207 = FStar_TypeChecker_Tc.pop_context env msg in ());
      FStar_Options.pop ()
let (push_with_kind :
  FStar_TypeChecker_Env.env ->
    Prims.bool -> Prims.bool -> Prims.string -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun lax ->
      fun restore_cmd_line_options ->
        fun msg ->
          let env1 =
            let uu___30_229 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___30_229.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___30_229.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___30_229.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___30_229.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___30_229.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___30_229.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___30_229.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___30_229.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___30_229.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___30_229.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___30_229.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___30_229.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___30_229.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___30_229.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___30_229.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___30_229.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___30_229.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___30_229.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___30_229.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___30_229.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax;
              FStar_TypeChecker_Env.lax_universes =
                (uu___30_229.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___30_229.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___30_229.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___30_229.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___30_229.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___30_229.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___30_229.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___30_229.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___30_229.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___30_229.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___30_229.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___30_229.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___30_229.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___30_229.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___30_229.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___30_229.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___30_229.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___30_229.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___30_229.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___30_229.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___30_229.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___30_229.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___30_229.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___30_229.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___30_229.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___30_229.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let res = FStar_TypeChecker_Tc.push_context env1 msg in
          FStar_Options.push ();
          if restore_cmd_line_options
          then
            (let uu____233 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____233 (fun uu____234 -> ()))
          else ();
          res
let (check_frag :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env * Prims.int)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun curmod ->
      fun frag ->
        try
          (fun uu___41_280 ->
             match () with
             | () ->
                 let uu____291 =
                   FStar_Universal.tc_one_fragment curmod env frag in
                 (match uu____291 with
                  | (m, env1) ->
                      let uu____314 =
                        let uu____323 = FStar_Errors.get_err_count () in
                        (m, env1, uu____323) in
                      FStar_Pervasives_Native.Some uu____314)) ()
        with
        | FStar_Errors.Error (e, msg, r, ctx) when
            let uu____359 = FStar_Options.trace_error () in
            Prims.op_Negation uu____359 ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r, ctx)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg, ctx) when
            let uu____378 = FStar_Options.trace_error () in
            Prims.op_Negation uu____378 ->
            ((let uu____380 =
                let uu____383 =
                  let uu____384 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____384, ctx) in
                [uu____383] in
              FStar_TypeChecker_Err.add_errors env uu____380);
             FStar_Pervasives_Native.None)
let (report_fail : unit -> unit) =
  fun uu____399 ->
    (let uu____401 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____401 (fun uu____406 -> ()));
    FStar_Errors.clear ()
type input_chunks =
  | Push of (Prims.bool * Prims.int * Prims.int) 
  | Pop of Prims.string 
  | Code of (Prims.string * (Prims.string * Prims.string)) 
  | Info of (Prims.string * Prims.bool * (Prims.string * Prims.int *
  Prims.int) FStar_Pervasives_Native.option) 
  | Completions of Prims.string 
let (uu___is_Push : input_chunks -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____472 -> false
let (__proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int)) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_Pop : input_chunks -> Prims.bool) =
  fun projectee -> match projectee with | Pop _0 -> true | uu____503 -> false
let (__proj__Pop__item___0 : input_chunks -> Prims.string) =
  fun projectee -> match projectee with | Pop _0 -> _0
let (uu___is_Code : input_chunks -> Prims.bool) =
  fun projectee ->
    match projectee with | Code _0 -> true | uu____524 -> false
let (__proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string))) =
  fun projectee -> match projectee with | Code _0 -> _0
let (uu___is_Info : input_chunks -> Prims.bool) =
  fun projectee ->
    match projectee with | Info _0 -> true | uu____575 -> false
let (__proj__Info__item___0 :
  input_chunks ->
    (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Info _0 -> _0
let (uu___is_Completions : input_chunks -> Prims.bool) =
  fun projectee ->
    match projectee with | Completions _0 -> true | uu____630 -> false
let (__proj__Completions__item___0 : input_chunks -> Prims.string) =
  fun projectee -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder ;
  stdin: FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref ;
  buffer: input_chunks Prims.list FStar_ST.ref ;
  log: FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref }
let (__proj__Mkinteractive_state__item__chunk :
  interactive_state -> FStar_Util.string_builder) =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> chunk
let (__proj__Mkinteractive_state__item__stdin :
  interactive_state ->
    FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> stdin
let (__proj__Mkinteractive_state__item__buffer :
  interactive_state -> input_chunks Prims.list FStar_ST.ref) =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> buffer
let (__proj__Mkinteractive_state__item__log :
  interactive_state ->
    FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> log
let (the_interactive_state : interactive_state) =
  let uu____783 = FStar_Util.new_string_builder () in
  let uu____784 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let uu____791 = FStar_Util.mk_ref [] in
  let uu____798 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  { chunk = uu____783; stdin = uu____784; buffer = uu____791; log = uu____798
  }
let rec (read_chunk : unit -> input_chunks) =
  fun uu____809 ->
    let s = the_interactive_state in
    let log =
      let uu____816 = FStar_Options.debug_any () in
      if uu____816
      then
        let transcript =
          let uu____821 = FStar_ST.op_Bang s.log in
          match uu____821 with
          | FStar_Pervasives_Native.Some transcript -> transcript
          | FStar_Pervasives_Native.None ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.op_Colon_Equals s.log
                 (FStar_Pervasives_Native.Some transcript);
               transcript) in
        fun line ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____850 -> ()) in
    let stdin =
      let uu____852 = FStar_ST.op_Bang s.stdin in
      match uu____852 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i) in
    let line =
      let uu____879 = FStar_Util.read_line stdin in
      match uu____879 with
      | FStar_Pervasives_Native.None -> FStar_All.exit Prims.int_zero
      | FStar_Pervasives_Native.Some l -> l in
    log line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____894::ok::fail::[] -> (ok, fail)
         | uu____897 -> ("ok", "fail") in
       let str = FStar_Util.string_of_string_builder s.chunk in
       (FStar_Util.clear_string_builder s.chunk; Code (str, responses))
     else
       if FStar_Util.starts_with l "#pop"
       then (FStar_Util.clear_string_builder s.chunk; Pop l)
       else
         if FStar_Util.starts_with l "#push"
         then
           (FStar_Util.clear_string_builder s.chunk;
            (let lc_lax =
               let uu____911 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____911 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____927 = FStar_Util.int_of_string l1 in
                   let uu____928 = FStar_Util.int_of_string c in
                   (true, uu____927, uu____928)
               | l1::c::[] ->
                   let uu____931 = FStar_Util.int_of_string l1 in
                   let uu____932 = FStar_Util.int_of_string c in
                   (false, uu____931, uu____932)
               | uu____933 ->
                   (FStar_Errors.log_issue FStar_Range.dummyRange
                      (FStar_Errors.Warning_WrongErrorLocation,
                        (Prims.op_Hat
                           "Error locations may be wrong, unrecognized string after #push: "
                           lc_lax));
                    (false, Prims.int_one, Prims.int_zero)) in
             Push lc))
         else
           if FStar_Util.starts_with l "#info "
           then
             (match FStar_Util.split l " " with
              | uu____938::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____955::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____961 =
                      let uu____976 =
                        let uu____985 =
                          let uu____992 = FStar_Util.int_of_string row in
                          let uu____993 = FStar_Util.int_of_string col in
                          (file, uu____992, uu____993) in
                        FStar_Pervasives_Native.Some uu____985 in
                      (symbol, false, uu____976) in
                    Info uu____961))
              | uu____1008 ->
                  (FStar_Errors.log_issue FStar_Range.dummyRange
                     (FStar_Errors.Error_IDEUnrecognized,
                       (Prims.op_Hat "Unrecognized \"#info\" request: " l));
                   FStar_All.exit Prims.int_one))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____1013::prefix::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix)
                | uu____1016 ->
                    (FStar_Errors.log_issue FStar_Range.dummyRange
                       (FStar_Errors.Error_IDEUnrecognized,
                         (Prims.op_Hat
                            "Unrecognized \"#completions\" request: " l));
                     FStar_All.exit Prims.int_one))
             else
               if l = "#finish"
               then FStar_All.exit Prims.int_zero
               else
                 (FStar_Util.string_builder_append s.chunk line;
                  FStar_Util.string_builder_append s.chunk "\n";
                  read_chunk ()))
let (shift_chunk : unit -> input_chunks) =
  fun uu____1028 ->
    let s = the_interactive_state in
    let uu____1030 = FStar_ST.op_Bang s.buffer in
    match uu____1030 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
let (fill_buffer : unit -> unit) =
  fun uu____1062 ->
    let s = the_interactive_state in
    let uu____1064 =
      let uu____1067 = FStar_ST.op_Bang s.buffer in
      let uu____1080 = let uu____1083 = read_chunk () in [uu____1083] in
      FStar_List.append uu____1067 uu____1080 in
    FStar_ST.op_Colon_Equals s.buffer uu____1064
let (deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option *
      FStar_Parser_Dep.deps))
  =
  fun filename ->
    let uu____1109 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache in
    match uu____1109 with
    | (deps, dep_graph) ->
        let uu____1132 =
          FStar_List.partition
            (fun x ->
               let uu____1145 = FStar_Parser_Dep.lowercase_module_name x in
               let uu____1146 =
                 FStar_Parser_Dep.lowercase_module_name filename in
               uu____1145 <> uu____1146) deps in
        (match uu____1132 with
         | (deps1, same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1175 =
                       (let uu____1178 = FStar_Parser_Dep.is_interface intf in
                        Prims.op_Negation uu____1178) ||
                         (let uu____1180 =
                            FStar_Parser_Dep.is_implementation impl in
                          Prims.op_Negation uu____1180) in
                     if uu____1175
                     then
                       let uu____1181 =
                         let uu____1186 =
                           FStar_Util.format2
                             "Found %s and %s but not an interface + implementation"
                             intf impl in
                         (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                           uu____1186) in
                       FStar_Errors.log_issue FStar_Range.dummyRange
                         uu____1181
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu____1189 ->
                   ((let uu____1193 =
                       let uu____1198 =
                         FStar_Util.format1 "Unexpected: ended up with %s"
                           (FStar_String.concat " " same_name) in
                       (FStar_Errors.Warning_UnexpectedFile, uu____1198) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____1193);
                    FStar_Pervasives_Native.None) in
             (deps1, maybe_intf, dep_graph))
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option * Prims.string *
    FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time)
    Prims.list
let rec (tc_deps :
  modul_t ->
    stack_t ->
      FStar_TypeChecker_Env.env ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t * FStar_TypeChecker_Env.env * m_timestamps))
  =
  fun m ->
    fun stack ->
      fun env ->
        fun remaining ->
          fun ts ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____1258 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____1273 = FStar_Options.lax () in
                  push_with_kind env uu____1273 true "typecheck_modul" in
                let uu____1274 = tc_one_file remaining env1 in
                (match uu____1274 with
                 | ((intf, impl), env2, remaining1) ->
                     let uu____1313 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____1326 =
                               FStar_Parser_ParseIt.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____1326
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Parser_ParseIt.get_file_last_modification_time
                           impl in
                       (intf_t, impl_t) in
                     (match uu____1313 with
                      | (intf_t, impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let (update_deps :
  Prims.string ->
    modul_t ->
      stack_t -> env_t -> m_timestamps -> (stack_t * env_t * m_timestamps))
  =
  fun filename ->
    fun m ->
      fun stk ->
        fun env ->
          fun ts ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt =
                FStar_Parser_ParseIt.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some intf1,
                    FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Parser_ParseIt.get_file_last_modification_time
                         intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> false
                 | (uu____1443, uu____1444) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None ->
                    (match depnames1 with
                     | dep::depnames' ->
                         if dep = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1557 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep::depnames' ->
                         if (depintf = intf1) && (dep = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1585 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1658::ts3 ->
                    (pop env1 "";
                     (let uu____1699 =
                        let uu____1714 = FStar_List.hd stack in
                        let uu____1723 = FStar_List.tl stack in
                        (uu____1714, uu____1723) in
                      match uu____1699 with
                      | ((env2, uu____1745), stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1809 = ts_elt in
                  (match uu____1809 with
                   | (intf, impl, intf_t, impl_t) ->
                       let uu____1840 = match_dep depnames intf impl in
                       (match uu____1840 with
                        | (b, depnames') ->
                            let uu____1859 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1859
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1876 =
                                 let uu____1885 = FStar_List.hd st in
                                 let uu____1894 = FStar_List.tl st in
                                 (uu____1885, uu____1894) in
                               match uu____1876 with
                               | (stack_elt, st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1947 = deps_of_our_file filename in
            match uu____1947 with
            | (filenames, uu____1965, dep_graph) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let (format_info :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Range.range ->
          Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun env ->
    fun name ->
      fun typ ->
        fun range ->
          fun doc ->
            let uu____2052 = FStar_Range.string_of_range range in
            let uu____2053 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____2054 =
              match doc with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2052 name
              uu____2053 uu____2054
let rec (go :
  (Prims.int * Prims.int) ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> unit)
  =
  fun line_col ->
    fun filename ->
      fun stack ->
        fun curmod ->
          fun env ->
            fun ts ->
              let uu____2094 = shift_chunk () in
              match uu____2094 with
              | Info (symbol, fqn_only, pos_opt) ->
                  let info_at_pos_opt =
                    match pos_opt with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (file, row, col) ->
                        FStar_TypeChecker_Err.info_at_pos env file row col in
                  let info_opt =
                    match info_at_pos_opt with
                    | FStar_Pervasives_Native.Some uu____2189 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____2244 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".") in
                             FStar_Ident.lid_of_ids uu____2244 in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____2247 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                match uu____2247 with
                                | FStar_Pervasives_Native.None -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1) in
                           let uu____2251 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1 in
                           FStar_All.pipe_right uu____2251
                             (FStar_Util.map_option
                                (fun uu____2306 ->
                                   match uu____2306 with
                                   | ((uu____2325, typ), r) ->
                                       ((FStar_Util.Inr lid1), typ, r)))) in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
                        let uu____2368 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____2385 = FStar_Ident.string_of_lid lid in
                              (uu____2385, FStar_Pervasives_Native.None) in
                        (match uu____2368 with
                         | (name, doc) ->
                             let uu____2394 =
                               format_info env name typ rng doc in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____2394));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([], uu____2435) ->
                        FStar_Pervasives_Native.Some ([], Prims.int_zero)
                    | (uu____2450, []) -> FStar_Pervasives_Native.None
                    | (hs::ts1, hc::tc) ->
                        let hc_text = FStar_Ident.string_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____2500 ->
                               let uu____2503 = measure_anchored_match ts1 tc in
                               FStar_All.pipe_right uu____2503
                                 (FStar_Util.map_option
                                    (fun uu____2543 ->
                                       match uu____2543 with
                                       | (matched, len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + Prims.int_one)
                                                + len)))))
                        else FStar_Pervasives_Native.None in
                  let rec locate_match needle candidate =
                    let uu____2602 = measure_anchored_match needle candidate in
                    match uu____2602 with
                    | FStar_Pervasives_Native.Some (matched, n) ->
                        FStar_Pervasives_Native.Some ([], matched, n)
                    | FStar_Pervasives_Native.None ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc ->
                             let uu____2681 = locate_match needle tc in
                             FStar_All.pipe_right uu____2681
                               (FStar_Util.map_option
                                  (fun uu____2742 ->
                                     match uu____2742 with
                                     | (prefix, matched, len) ->
                                         ((hc :: prefix), matched, len)))) in
                  let str_of_ids ids =
                    let uu____2788 =
                      FStar_List.map FStar_Ident.string_of_id ids in
                    FStar_Util.concat_l "." uu____2788 in
                  let match_lident_against needle lident =
                    let uu____2818 =
                      let uu____2821 = FStar_Ident.ns_of_lid lident in
                      let uu____2824 =
                        let uu____2827 = FStar_Ident.ident_of_lid lident in
                        [uu____2827] in
                      FStar_List.append uu____2821 uu____2824 in
                    locate_match needle uu____2818 in
                  let shorten_namespace uu____2851 =
                    match uu____2851 with
                    | (prefix, matched, match_len) ->
                        let naked_match =
                          match matched with
                          | uu____2882::[] -> true
                          | uu____2883 -> false in
                        let uu____2886 =
                          FStar_Syntax_DsEnv.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix
                            naked_match in
                        (match uu____2886 with
                         | (stripped_ns, shortened) ->
                             let uu____2913 = str_of_ids shortened in
                             let uu____2914 = str_of_ids matched in
                             let uu____2915 = str_of_ids stripped_ns in
                             (uu____2913, uu____2914, uu____2915, match_len)) in
                  let prepare_candidate uu____2935 =
                    match uu____2935 with
                    | (prefix, matched, stripped_ns, match_len) ->
                        if prefix = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.op_Hat prefix (Prims.op_Hat "." matched)),
                            stripped_ns,
                            (((FStar_String.length prefix) + match_len) +
                               Prims.int_one)) in
                  let needle = FStar_Util.split search_term "." in
                  let all_lidents_in_env = FStar_TypeChecker_Env.lidents env in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id =
                      let exported_names =
                        FStar_Syntax_DsEnv.transitive_exported_ids
                          env.FStar_TypeChecker_Env.dsenv m in
                      let matched_length =
                        FStar_List.fold_left
                          (fun out ->
                             fun s ->
                               ((FStar_String.length s) + out) +
                                 Prims.int_one) (FStar_String.length id)
                          orig_ns in
                      FStar_All.pipe_right exported_names
                        (FStar_List.filter_map
                           (fun n ->
                              if FStar_Util.starts_with n id
                              then
                                let lid =
                                  let uu____3069 = FStar_Ident.ids_of_lid m in
                                  let uu____3070 = FStar_Ident.id_of_text n in
                                  FStar_Ident.lid_of_ns_and_id uu____3069
                                    uu____3070 in
                                let uu____3071 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                FStar_Option.map
                                  (fun fqn ->
                                     let uu____3087 =
                                       let uu____3090 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       let uu____3093 =
                                         let uu____3096 =
                                           FStar_Ident.ident_of_lid fqn in
                                         [uu____3096] in
                                       FStar_List.append uu____3090
                                         uu____3093 in
                                     ([], uu____3087, matched_length))
                                  uu____3071
                              else FStar_Pervasives_Native.None)) in
                    let case_b_find_matches_in_env uu____3129 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____3204 ->
                              match uu____3204 with
                              | (ns, id, uu____3217) ->
                                  let uu____3226 =
                                    let uu____3229 =
                                      FStar_Ident.lid_of_ids id in
                                    FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____3229 in
                                  (match uu____3226 with
                                   | FStar_Pervasives_Native.None -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____3231 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id) in
                                       FStar_Ident.lid_equals l uu____3231))) in
                    let uu____3232 = FStar_Util.prefix needle in
                    match uu____3232 with
                    | (ns, id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____3278 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____3282 =
                                FStar_Syntax_DsEnv.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true in
                              (match uu____3282 with
                               | FStar_Pervasives_Native.None ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x ->
                                let uu____3347 = shorten_namespace x in
                                prepare_candidate uu____3347)) in
                  ((let uu____3357 =
                      FStar_Util.sort_with
                        (fun uu____3380 ->
                           fun uu____3381 ->
                             match (uu____3380, uu____3381) with
                             | ((cd1, ns1, uu____3408),
                                (cd2, ns2, uu____3411)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | uu____3424 when
                                      uu____3424 = Prims.int_zero ->
                                      FStar_String.compare ns1 ns2
                                  | n -> n)) matches in
                    FStar_List.iter
                      (fun uu____3437 ->
                         match uu____3437 with
                         | (candidate, ns, match_len) ->
                             let uu____3447 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____3447 ns
                               candidate) uu____3357);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____3451 =
                      match stack with
                      | [] ->
                          (FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_IDETooManyPops,
                               "too many pops");
                           FStar_All.exit Prims.int_one)
                      | hd::tl -> (hd, tl) in
                    match uu____3451 with
                    | ((env1, curmod1), stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax, l, c) ->
                  let uu____3511 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____3548 =
                        update_deps filename curmod stack env ts in
                      (true, uu____3548)
                    else (false, (stack, env, ts)) in
                  (match uu____3511 with
                   | (restore_cmd_line_options, (stack1, env1, ts1)) ->
                       let stack2 = (env1, curmod) :: stack1 in
                       let env2 =
                         push_with_kind env1 lax restore_cmd_line_options
                           "#push" in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text, (ok, fail)) ->
                  let fail1 curmod1 tcenv =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail;
                    go line_col filename stack curmod1 tcenv ts in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_fname = "<input>";
                      FStar_Parser_ParseIt.frag_text = text;
                      FStar_Parser_ParseIt.frag_line =
                        (FStar_Pervasives_Native.fst line_col);
                      FStar_Parser_ParseIt.frag_col =
                        (FStar_Pervasives_Native.snd line_col)
                    } in
                  let res = check_frag env curmod frag in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1, env1, n_errs) ->
                       if n_errs = Prims.int_zero
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          go line_col filename stack curmod1 env1 ts)
                       else fail1 curmod1 env1
                   | uu____3639 -> fail1 curmod env)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    (let uu____3656 =
       let uu____3657 = FStar_Options.codegen () in
       FStar_Option.isSome uu____3657 in
     if uu____3656
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen,
           "code-generation is not supported in interactive mode, ignoring the codegen flag")
     else ());
    (let uu____3661 = deps_of_our_file filename in
     match uu____3661 with
     | (filenames, maybe_intf, dep_graph) ->
         let env = FStar_Universal.init_env dep_graph in
         let uu____3684 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____3684 with
          | (stack, env1, ts) ->
              let initial_range =
                let uu____3711 =
                  FStar_Range.mk_pos Prims.int_one Prims.int_zero in
                let uu____3712 =
                  FStar_Range.mk_pos Prims.int_one Prims.int_zero in
                FStar_Range.mk_range filename uu____3711 uu____3712 in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None -> env2 in
              let uu____3716 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____3716
              then
                let uu____3717 =
                  let uu____3718 = FStar_Options.file_list () in
                  FStar_List.hd uu____3718 in
                FStar_SMTEncoding_Solver.with_hints_db uu____3717
                  (fun uu____3722 ->
                     go (Prims.int_one, Prims.int_zero) filename stack
                       FStar_Pervasives_Native.None env3 ts)
              else
                go (Prims.int_one, Prims.int_zero) filename stack
                  FStar_Pervasives_Native.None env3 ts))