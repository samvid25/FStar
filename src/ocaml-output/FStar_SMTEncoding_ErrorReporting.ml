open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Not_a_wp_implication uu____10 -> true
    | uu____11 -> false
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Not_a_wp_implication uu____17 -> uu____17
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l ->
    FStar_List.sortWith
      (fun uu____67 ->
         fun uu____68 ->
           match (uu____67, uu____68) with
           | (((uu____109, uu____110, r1), uu____112),
              ((uu____113, uu____114, r2), uu____116)) ->
               FStar_Range.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l ->
    FStar_Util.remove_dups
      (fun uu____176 ->
         fun uu____177 ->
           match (uu____176, uu____177) with
           | ((uu____202, m1, r1), (uu____205, m2, r2)) ->
               (r1 = r2) && (m1 = m2)) l
type msg = (Prims.string * FStar_Range.range)
type ranges =
  (Prims.string FStar_Pervasives_Native.option * FStar_Range.range)
    Prims.list
let (fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (label * FStar_SMTEncoding_Term.term))
  =
  let ctr = FStar_Util.mk_ref Prims.int_zero in
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStar_Util.incr ctr;
          (let uu____256 =
             let uu____257 = FStar_ST.op_Bang ctr in
             FStar_Util.string_of_int uu____257 in
           FStar_Util.format1 "label_%s" uu____256) in
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label1 = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt = FStar_SMTEncoding_Term.mkOr (lterm, t) range in (label1, lt)
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels * FStar_SMTEncoding_Term.term))
  =
  fun use_env_msg ->
    fun r ->
      fun q ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None, uu____323) -> false
          | (FStar_Pervasives_Native.Some nm, FStar_SMTEncoding_Term.FreeV
             fv) ->
              let uu____336 = FStar_SMTEncoding_Term.fv_name fv in
              nm = uu____336
          | (uu____337, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____345, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT", tm1::uu____347)) ->
              is_a_post_condition post_name_opt tm1
          | uu____356 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> cs
          | uu____378 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall,
               ({
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStar_SMTEncoding_Term.freevars = uu____386;
                  FStar_SMTEncoding_Term.rng = uu____387;_}::[])::[],
               iopt, uu____389,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp, l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____392;
                 FStar_SMTEncoding_Term.rng = uu____393;_})
              -> true
          | uu____434 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____443 =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____462 = f () in (true, uu____462) in
        match uu____443 with
        | (flag, msg_prefix) ->
            let fresh_label1 msg1 ropt rng t =
              let msg2 =
                if flag
                then
                  Prims.op_Hat "Failed to verify implicit argument: "
                    (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg1))
                else msg1 in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____502 =
                      let uu____503 = FStar_Range.use_range rng in
                      let uu____504 = FStar_Range.use_range r1 in
                      FStar_Range.rng_included uu____503 uu____504 in
                    if uu____502
                    then rng
                    else
                      (let uu____506 = FStar_Range.def_range rng in
                       FStar_Range.set_def_range r1 uu____506) in
              fresh_label msg2 rng1 t in
            let rec aux default_msg ropt post_name_opt labels1 q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____557 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Integer uu____560 -> (labels1, q1)
              | FStar_SMTEncoding_Term.String uu____563 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Real uu____566 -> (labels1, q1)
              | FStar_SMTEncoding_Term.LblPos uu____569 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg, "could not prove post-condition", uu____581) ->
                  let fallback msg1 =
                    aux default_msg ropt post_name_opt labels1 arg in
                  (try
                     (fun uu___144_623 ->
                        match () with
                        | () ->
                            (match arg.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.Quant
                                 (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                  post::sorts,
                                  {
                                    FStar_SMTEncoding_Term.tm =
                                      FStar_SMTEncoding_Term.App
                                      (FStar_SMTEncoding_Term.Imp,
                                       lhs::rhs::[]);
                                    FStar_SMTEncoding_Term.freevars =
                                      uu____642;
                                    FStar_SMTEncoding_Term.rng = rng;_})
                                 ->
                                 let post_name =
                                   let uu____673 =
                                     let uu____674 = FStar_Ident.next_id () in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____674 in
                                   Prims.op_Hat "^^post_condition_" uu____673 in
                                 let names =
                                   let uu____678 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post) in
                                   let uu____679 =
                                     FStar_List.map
                                       (fun s ->
                                          let uu____685 =
                                            let uu____690 =
                                              let uu____691 =
                                                let uu____692 =
                                                  FStar_Ident.next_id () in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____692 in
                                              Prims.op_Hat "^^" uu____691 in
                                            (uu____690, s) in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____685) sorts in
                                   uu____678 :: uu____679 in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names in
                                 let uu____696 =
                                   let uu____701 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs in
                                   let uu____702 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs in
                                   (uu____701, uu____702) in
                                 (match uu____696 with
                                  | (lhs1, rhs1) ->
                                      let uu____711 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And,
                                             clauses_lhs)
                                            ->
                                            let uu____729 =
                                              FStar_Util.prefix clauses_lhs in
                                            (match uu____729 with
                                             | (req, ens) ->
                                                 (match ens.FStar_SMTEncoding_Term.tm
                                                  with
                                                  | FStar_SMTEncoding_Term.Quant
                                                      (FStar_SMTEncoding_Term.Forall,
                                                       pats_ens, iopt_ens,
                                                       sorts_ens,
                                                       {
                                                         FStar_SMTEncoding_Term.tm
                                                           =
                                                           FStar_SMTEncoding_Term.App
                                                           (FStar_SMTEncoding_Term.Imp,
                                                            ensures_conjuncts::post1::[]);
                                                         FStar_SMTEncoding_Term.freevars
                                                           = uu____759;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____789 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1 in
                                                      if uu____789
                                                      then
                                                        let uu____796 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels1
                                                            ensures_conjuncts in
                                                        (match uu____796 with
                                                         | (labels2,
                                                            ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu____838 ->
                                                                   pats_ens in
                                                             let ens1 =
                                                               let uu____844
                                                                 =
                                                                 let uu____845
                                                                   =
                                                                   let uu____864
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk
                                                                    (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.Imp,
                                                                    [ensures_conjuncts1;
                                                                    post1]))
                                                                    rng_ens in
                                                                   (FStar_SMTEncoding_Term.Forall,
                                                                    pats_ens1,
                                                                    iopt_ens,
                                                                    sorts_ens,
                                                                    uu____864) in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____845 in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____844
                                                                 ens.FStar_SMTEncoding_Term.rng in
                                                             let lhs2 =
                                                               FStar_SMTEncoding_Term.mk
                                                                 (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.And,
                                                                    (FStar_List.append
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStar_SMTEncoding_Term.rng in
                                                             let uu____878 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names lhs2 in
                                                             (labels2,
                                                               uu____878))
                                                      else
                                                        (let uu____882 =
                                                           let uu____883 =
                                                             let uu____884 =
                                                               let uu____885
                                                                 =
                                                                 let uu____886
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1 in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____886 in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____885 in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____884 in
                                                           Not_a_wp_implication
                                                             uu____883 in
                                                         FStar_Exn.raise
                                                           uu____882)
                                                  | uu____893 ->
                                                      let uu____894 =
                                                        let uu____895 =
                                                          let uu____896 =
                                                            let uu____897 =
                                                              let uu____898 =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____898 in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____897 in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____896 in
                                                        Not_a_wp_implication
                                                          uu____895 in
                                                      FStar_Exn.raise
                                                        uu____894))
                                        | uu____905 ->
                                            let uu____906 =
                                              let uu____907 =
                                                let uu____908 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1 in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____908 in
                                              Not_a_wp_implication uu____907 in
                                            FStar_Exn.raise uu____906 in
                                      (match uu____711 with
                                       | (labels2, lhs2) ->
                                           let uu____927 =
                                             let uu____934 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels2 rhs1 in
                                             match uu____934 with
                                             | (labels3, rhs2) ->
                                                 let uu____953 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names rhs2 in
                                                 (labels3, uu____953) in
                                           (match uu____927 with
                                            | (labels3, rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng in
                                                let uu____969 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels3, uu____969))))
                             | uu____980 ->
                                 let uu____981 =
                                   let uu____982 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg in
                                   Prims.op_Hat "arg not a quant: " uu____982 in
                                 fallback uu____981)) ()
                   with | Not_a_wp_implication msg1 -> fallback msg1)
              | FStar_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels1 arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, sorts,
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStar_SMTEncoding_Term.freevars = uu____999;
                     FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1025 = FStar_Util.prefix sorts in
                  (match uu____1025 with
                   | (sorts', post) ->
                       let new_post_name =
                         let uu____1045 =
                           let uu____1046 = FStar_Ident.next_id () in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1046 in
                         Prims.op_Hat "^^post_condition_" uu____1045 in
                       let names =
                         let uu____1050 =
                           FStar_List.map
                             (fun s ->
                                let uu____1056 =
                                  let uu____1061 =
                                    let uu____1062 =
                                      let uu____1063 = FStar_Ident.next_id () in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1063 in
                                    Prims.op_Hat "^^" uu____1062 in
                                  (uu____1061, s) in
                                FStar_SMTEncoding_Term.mk_fv uu____1056)
                             sorts' in
                         let uu____1064 =
                           let uu____1067 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post) in
                           [uu____1067] in
                         FStar_List.append uu____1050 uu____1064 in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names in
                       let uu____1071 =
                         let uu____1076 =
                           FStar_SMTEncoding_Term.inst instantiation lhs in
                         let uu____1077 =
                           FStar_SMTEncoding_Term.inst instantiation rhs in
                         (uu____1076, uu____1077) in
                       (match uu____1071 with
                        | (lhs1, rhs1) ->
                            let uu____1086 =
                              FStar_Util.fold_map
                                (fun labels2 ->
                                   fun tm ->
                                     match tm.FStar_SMTEncoding_Term.tm with
                                     | FStar_SMTEncoding_Term.Quant
                                         (FStar_SMTEncoding_Term.Forall,
                                          ({
                                             FStar_SMTEncoding_Term.tm =
                                               FStar_SMTEncoding_Term.App
                                               (FStar_SMTEncoding_Term.Var
                                                "Prims.guard_free", p::[]);
                                             FStar_SMTEncoding_Term.freevars
                                               = uu____1124;
                                             FStar_SMTEncoding_Term.rng =
                                               uu____1125;_}::[])::[],
                                          iopt, sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp,
                                               l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1130;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1131;_})
                                         ->
                                         let uu____1172 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1 in
                                         if uu____1172
                                         then
                                           let uu____1179 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels2 l0 in
                                           (match uu____1179 with
                                            | (labels3, l) ->
                                                let uu____1198 =
                                                  let uu____1199 =
                                                    let uu____1200 =
                                                      let uu____1219 =
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1])) in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           Prims.int_zero),
                                                        sorts1, uu____1219) in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1200 in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1199
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels3, uu____1198))
                                         else (labels2, tm)
                                     | uu____1239 -> (labels2, tm)) labels1
                                (conjuncts lhs1) in
                            (match uu____1086 with
                             | (labels2, lhs_conjs) ->
                                 let uu____1258 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels2 rhs1 in
                                 (match uu____1258 with
                                  | (labels3, rhs2) ->
                                      let body =
                                        let uu____1278 =
                                          let uu____1279 =
                                            let uu____1284 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng in
                                            (uu____1284, rhs2) in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1279 rng in
                                        FStar_All.pipe_right uu____1278
                                          (FStar_SMTEncoding_Term.abstr names) in
                                      let q2 =
                                        FStar_SMTEncoding_Term.mk
                                          (FStar_SMTEncoding_Term.Quant
                                             (FStar_SMTEncoding_Term.Forall,
                                               [],
                                               FStar_Pervasives_Native.None,
                                               sorts, body))
                                          q1.FStar_SMTEncoding_Term.rng in
                                      (labels3, q2)))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) ->
                  let uu____1302 =
                    aux default_msg ropt post_name_opt labels1 rhs in
                  (match uu____1302 with
                   | (labels2, rhs1) ->
                       let uu____1321 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels2, uu____1321))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And, conjuncts1) ->
                  let uu____1329 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels1 conjuncts1 in
                  (match uu____1329 with
                   | (labels2, conjuncts2) ->
                       let uu____1356 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____1356))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, hd::q11::q2::[]) ->
                  let uu____1364 =
                    aux default_msg ropt post_name_opt labels1 q11 in
                  (match uu____1364 with
                   | (labels2, q12) ->
                       let uu____1383 =
                         aux default_msg ropt post_name_opt labels2 q2 in
                       (match uu____1383 with
                        | (labels3, q21) ->
                            let uu____1402 =
                              FStar_SMTEncoding_Term.mkITE (hd, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels3, uu____1402)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists, uu____1405, uu____1406,
                   uu____1407, uu____1408)
                  ->
                  let uu____1425 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1425 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff, uu____1440) ->
                  let uu____1445 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1445 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or, uu____1460) ->
                  let uu____1465 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1465 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1480, uu____1481) when
                  is_a_post_condition post_name_opt q1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1488 ->
                  let uu____1495 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1495 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp, uu____1510) ->
                  let uu____1515 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1515 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp, uu____1530) ->
                  let uu____1535 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1535 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not, uu____1550) ->
                  let uu____1555 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1555 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq, uu____1570) ->
                  let uu____1575 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1575 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT, uu____1590) ->
                  let uu____1595 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1595 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE, uu____1610) ->
                  let uu____1615 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1615 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT, uu____1630) ->
                  let uu____1635 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1635 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE, uu____1650) ->
                  let uu____1655 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1655 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt, uu____1670) ->
                  let uu____1675 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1675 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1690, uu____1691) ->
                  let uu____1696 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1696 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv, uu____1711) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add, uu____1722) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub, uu____1733) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div, uu____1744) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul, uu____1755) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus, uu____1766) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod, uu____1777) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd, uu____1788) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor, uu____1799) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr, uu____1810) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd, uu____1821) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub, uu____1832) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl, uu____1843) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr, uu____1854) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv, uu____1865) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod, uu____1876) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul, uu____1887) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1898, uu____1899) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat, uu____1910) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1921, uu____1922) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, uu____1933) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, uu____1944) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) ->
                  let uu____1975 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu____1975 with
                   | (labels2, body1) ->
                       let uu____1994 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____1994))
              | FStar_SMTEncoding_Term.Let (es, body) ->
                  let uu____2011 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu____2011 with
                   | (labels2, body1) ->
                       let uu____2030 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____2030)) in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
let (detail_errors :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      labels ->
        (FStar_SMTEncoding_Term.decl Prims.list ->
           FStar_SMTEncoding_Z3.z3result)
          -> unit)
  =
  fun hint_replay ->
    fun env ->
      fun all_labels ->
        fun askZ3 ->
          let print_banner uu____2069 =
            let msg1 =
              let uu____2071 =
                let uu____2072 = FStar_TypeChecker_Env.get_range env in
                FStar_Range.string_of_range uu____2072 in
              let uu____2073 = FStar_Util.string_of_int (Prims.of_int (5)) in
              let uu____2074 =
                FStar_Util.string_of_int (FStar_List.length all_labels) in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2071
                uu____2073 uu____2074 in
            FStar_Util.print_error msg1 in
          let print_result uu____2091 =
            match uu____2091 with
            | ((uu____2102, msg1, r), success) ->
                if success
                then
                  let uu____2112 = FStar_Range.string_of_range r in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2112
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg1))
                  else
                    (let uu____2115 =
                       let uu____2120 =
                         let uu____2121 = FStar_Range.string_of_range r in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2121 msg1 in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2120) in
                     FStar_Errors.log_issue r uu____2115) in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2167 ->
                    match uu____2167 with
                    | (l, uu____2175, uu____2176) ->
                        let a =
                          let uu____2178 =
                            let uu____2179 =
                              let uu____2184 =
                                FStar_SMTEncoding_Util.mkFreeV l in
                              (uu____2184, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu____2179 in
                          let uu____2185 =
                            let uu____2186 = FStar_SMTEncoding_Term.fv_name l in
                            Prims.op_Hat "@disable_label_" uu____2186 in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2178;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____2185;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          } in
                        FStar_SMTEncoding_Term.Assume a)) in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2247 =
                     FStar_List.map (fun x -> (x, true)) eliminated in
                   let uu____2260 =
                     FStar_List.map (fun x -> (x, false)) errors in
                   FStar_List.append uu____2247 uu____2260 in
                 sort_labels results
             | hd::tl ->
                 ((let uu____2282 =
                     FStar_Util.string_of_int (FStar_List.length active) in
                   FStar_Util.print1 "%s, " uu____2282);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2309 ->
                       linear_check (hd :: eliminated) errors tl
                   | uu____2310 -> linear_check eliminated (hd :: errors) tl))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.of_int (5)));
          (let res = linear_check [] [] all_labels in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2350 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res in
            if uu____2350
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))