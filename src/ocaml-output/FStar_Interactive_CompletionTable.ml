open Prims
let (string_compare : Prims.string -> Prims.string -> Prims.int) =
  fun s1 -> fun s2 -> FStar_String.compare s1 s2
type 'a heap =
  | EmptyHeap 
  | Heap of ('a * 'a heap Prims.list) 
let uu___is_EmptyHeap : 'a . 'a heap -> Prims.bool =
  fun projectee ->
    match projectee with | EmptyHeap -> true | uu____62 -> false
let uu___is_Heap : 'a . 'a heap -> Prims.bool =
  fun projectee -> match projectee with | Heap _0 -> true | uu____88 -> false
let __proj__Heap__item___0 : 'a . 'a heap -> ('a * 'a heap Prims.list) =
  fun projectee -> match projectee with | Heap _0 -> _0
let heap_merge :
  'uuuuuu130 .
    ('uuuuuu130 -> 'uuuuuu130 -> Prims.int) ->
      'uuuuuu130 heap -> 'uuuuuu130 heap -> 'uuuuuu130 heap
  =
  fun cmp ->
    fun h1 ->
      fun h2 ->
        match (h1, h2) with
        | (EmptyHeap, h) -> h
        | (h, EmptyHeap) -> h
        | (Heap (v1, hh1), Heap (v2, hh2)) ->
            let uu____208 =
              let uu____209 = cmp v1 v2 in uu____209 < Prims.int_zero in
            if uu____208
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
let heap_insert :
  'uuuuuu233 .
    ('uuuuuu233 -> 'uuuuuu233 -> Prims.int) ->
      'uuuuuu233 heap -> 'uuuuuu233 -> 'uuuuuu233 heap
  = fun cmp -> fun h -> fun v -> heap_merge cmp (Heap (v, [])) h
let rec heap_merge_pairs :
  'uuuuuu277 .
    ('uuuuuu277 -> 'uuuuuu277 -> Prims.int) ->
      'uuuuuu277 heap Prims.list -> 'uuuuuu277 heap
  =
  fun cmp ->
    fun uu___0_299 ->
      match uu___0_299 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____332 = heap_merge cmp h1 h2 in
          let uu____335 = heap_merge_pairs cmp hh in
          heap_merge cmp uu____332 uu____335
let heap_peek :
  'uuuuuu342 . 'uuuuuu342 heap -> 'uuuuuu342 FStar_Pervasives_Native.option =
  fun uu___1_351 ->
    match uu___1_351 with
    | EmptyHeap -> FStar_Pervasives_Native.None
    | Heap (v, uu____355) -> FStar_Pervasives_Native.Some v
let heap_pop :
  'uuuuuu370 .
    ('uuuuuu370 -> 'uuuuuu370 -> Prims.int) ->
      'uuuuuu370 heap ->
        ('uuuuuu370 * 'uuuuuu370 heap) FStar_Pervasives_Native.option
  =
  fun cmp ->
    fun uu___2_396 ->
      match uu___2_396 with
      | EmptyHeap -> FStar_Pervasives_Native.None
      | Heap (v, hh) ->
          let uu____419 =
            let uu____426 = heap_merge_pairs cmp hh in (v, uu____426) in
          FStar_Pervasives_Native.Some uu____419
let heap_from_list :
  'uuuuuu443 .
    ('uuuuuu443 -> 'uuuuuu443 -> Prims.int) ->
      'uuuuuu443 Prims.list -> 'uuuuuu443 heap
  =
  fun cmp ->
    fun values -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
let push_nodup :
  'uuuuuu480 .
    ('uuuuuu480 -> Prims.string) ->
      'uuuuuu480 -> 'uuuuuu480 Prims.list -> 'uuuuuu480 Prims.list
  =
  fun key_fn ->
    fun x ->
      fun uu___3_502 ->
        match uu___3_502 with
        | [] -> [x]
        | h::t ->
            let uu____511 =
              let uu____512 =
                let uu____513 = key_fn x in
                let uu____514 = key_fn h in
                string_compare uu____513 uu____514 in
              uu____512 = Prims.int_zero in
            if uu____511 then h :: t else x :: h :: t
let rec add_priorities :
  'uuuuuu526 .
    Prims.int ->
      (Prims.int * 'uuuuuu526) Prims.list ->
        'uuuuuu526 Prims.list -> (Prims.int * 'uuuuuu526) Prims.list
  =
  fun n ->
    fun acc ->
      fun uu___4_555 ->
        match uu___4_555 with
        | [] -> acc
        | h::t -> add_priorities (n + Prims.int_one) ((n, h) :: acc) t
let merge_increasing_lists_rev :
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn ->
    fun lists ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____651, []), uu____652) -> failwith "impossible"
        | (uu____673, (uu____674, [])) -> failwith "impossible"
        | ((pr1, h1::uu____697), (pr2, h2::uu____700)) ->
            let cmp_h =
              let uu____722 = key_fn h1 in
              let uu____723 = key_fn h2 in string_compare uu____722 uu____723 in
            if cmp_h <> Prims.int_zero then cmp_h else pr1 - pr2 in
      let rec aux lists1 acc =
        let uu____758 = heap_pop cmp lists1 in
        match uu____758 with
        | FStar_Pervasives_Native.None -> acc
        | FStar_Pervasives_Native.Some ((pr, []), uu____806) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr, v::[]), lists2) ->
            let uu____896 = push_nodup key_fn v acc in aux lists2 uu____896
        | FStar_Pervasives_Native.Some ((pr, v::tl), lists2) ->
            let uu____947 = heap_insert cmp lists2 (pr, tl) in
            let uu____964 = push_nodup key_fn v acc in
            aux uu____947 uu____964 in
      let lists1 = FStar_List.filter (fun x -> x <> []) lists in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____991 ->
          let lists2 = add_priorities Prims.int_zero [] lists1 in
          let uu____1013 = heap_from_list cmp lists2 in aux uu____1013 []
type 'a btree =
  | StrEmpty 
  | StrBranch of (Prims.string * 'a * 'a btree * 'a btree) 
let uu___is_StrEmpty : 'a . 'a btree -> Prims.bool =
  fun projectee ->
    match projectee with | StrEmpty -> true | uu____1067 -> false
let uu___is_StrBranch : 'a . 'a btree -> Prims.bool =
  fun projectee ->
    match projectee with | StrBranch _0 -> true | uu____1097 -> false
let __proj__StrBranch__item___0 :
  'a . 'a btree -> (Prims.string * 'a * 'a btree * 'a btree) =
  fun projectee -> match projectee with | StrBranch _0 -> _0
let rec btree_to_list_rev :
  'uuuuuu1145 .
    'uuuuuu1145 btree ->
      (Prims.string * 'uuuuuu1145) Prims.list ->
        (Prims.string * 'uuuuuu1145) Prims.list
  =
  fun btree1 ->
    fun acc ->
      match btree1 with
      | StrEmpty -> acc
      | StrBranch (key, value, lbt, rbt) ->
          let uu____1190 =
            let uu____1197 = btree_to_list_rev lbt acc in (key, value) ::
              uu____1197 in
          btree_to_list_rev rbt uu____1190
let rec btree_from_list :
  'uuuuuu1214 .
    (Prims.string * 'uuuuuu1214) Prims.list ->
      Prims.int ->
        ('uuuuuu1214 btree * (Prims.string * 'uuuuuu1214) Prims.list)
  =
  fun nodes ->
    fun size ->
      if size = Prims.int_zero
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.of_int (2)) in
         let rbt_size = (size - lbt_size) - Prims.int_one in
         let uu____1260 = btree_from_list nodes lbt_size in
         match uu____1260 with
         | (lbt, nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k, v)::nodes_left1 ->
                  let uu____1344 = btree_from_list nodes_left1 rbt_size in
                  (match uu____1344 with
                   | (rbt, nodes_left2) ->
                       ((StrBranch (k, v, lbt, rbt)), nodes_left2))))
let rec btree_insert_replace :
  'a . 'a btree -> Prims.string -> 'a -> 'a btree =
  fun bt ->
    fun k ->
      fun v ->
        match bt with
        | StrEmpty -> StrBranch (k, v, StrEmpty, StrEmpty)
        | StrBranch (k', v', lbt, rbt) ->
            let cmp = string_compare k k' in
            if cmp < Prims.int_zero
            then
              let uu____1449 =
                let uu____1462 = btree_insert_replace lbt k v in
                (k', v', uu____1462, rbt) in
              StrBranch uu____1449
            else
              if cmp > Prims.int_zero
              then
                (let uu____1472 =
                   let uu____1485 = btree_insert_replace rbt k v in
                   (k', v', lbt, uu____1485) in
                 StrBranch uu____1472)
              else StrBranch (k', v, lbt, rbt)
let rec btree_find_exact :
  'a . 'a btree -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun bt ->
    fun k ->
      match bt with
      | StrEmpty -> FStar_Pervasives_Native.None
      | StrBranch (k', v, lbt, rbt) ->
          let cmp = string_compare k k' in
          if cmp < Prims.int_zero
          then btree_find_exact lbt k
          else
            if cmp > Prims.int_zero
            then btree_find_exact rbt k
            else FStar_Pervasives_Native.Some v
let rec btree_extract_min :
  'a .
    'a btree -> (Prims.string * 'a * 'a btree) FStar_Pervasives_Native.option
  =
  fun bt ->
    match bt with
    | StrEmpty -> FStar_Pervasives_Native.None
    | StrBranch (k, v, StrEmpty, rbt) ->
        FStar_Pervasives_Native.Some (k, v, rbt)
    | StrBranch (uu____1592, uu____1593, lbt, uu____1595) ->
        btree_extract_min lbt
let rec btree_remove : 'a . 'a btree -> Prims.string -> 'a btree =
  fun bt ->
    fun k ->
      match bt with
      | StrEmpty -> StrEmpty
      | StrBranch (k', v, lbt, rbt) ->
          let cmp = string_compare k k' in
          if cmp < Prims.int_zero
          then
            let uu____1643 =
              let uu____1656 = btree_remove lbt k in (k', v, uu____1656, rbt) in
            StrBranch uu____1643
          else
            if cmp > Prims.int_zero
            then
              (let uu____1666 =
                 let uu____1679 = btree_remove rbt k in
                 (k', v, lbt, uu____1679) in
               StrBranch uu____1666)
            else
              (match lbt with
               | StrEmpty -> bt
               | uu____1689 ->
                   let uu____1692 = btree_extract_min rbt in
                   (match uu____1692 with
                    | FStar_Pervasives_Native.None -> lbt
                    | FStar_Pervasives_Native.Some
                        (rbt_min_k, rbt_min_v, rbt') ->
                        StrBranch (rbt_min_k, rbt_min_v, lbt, rbt')))
type prefix_match =
  {
  prefix: Prims.string FStar_Pervasives_Native.option ;
  completion: Prims.string }
let (__proj__Mkprefix_match__item__prefix :
  prefix_match -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { prefix; completion;_} -> prefix
let (__proj__Mkprefix_match__item__completion : prefix_match -> Prims.string)
  =
  fun projectee ->
    match projectee with | { prefix; completion;_} -> completion
type path_elem = {
  imports: Prims.string Prims.list ;
  segment: prefix_match }
let (__proj__Mkpath_elem__item__imports :
  path_elem -> Prims.string Prims.list) =
  fun projectee -> match projectee with | { imports; segment;_} -> imports
let (__proj__Mkpath_elem__item__segment : path_elem -> prefix_match) =
  fun projectee -> match projectee with | { imports; segment;_} -> segment
let (matched_prefix_of_path_elem :
  path_elem -> Prims.string FStar_Pervasives_Native.option) =
  fun elem -> (elem.segment).prefix
let (mk_path_el : Prims.string Prims.list -> prefix_match -> path_elem) =
  fun imports -> fun segment -> { imports; segment }
let btree_find_prefix :
  'a . 'a btree -> Prims.string -> (prefix_match * 'a) Prims.list =
  fun bt ->
    fun prefix ->
      let rec aux bt1 prefix1 acc =
        match bt1 with
        | StrEmpty -> acc
        | StrBranch (k, v, lbt, rbt) ->
            let cmp = string_compare k prefix1 in
            let include_middle = FStar_Util.starts_with k prefix1 in
            let explore_right = (cmp <= Prims.int_zero) || include_middle in
            let explore_left = cmp > Prims.int_zero in
            let matches = if explore_right then aux rbt prefix1 acc else acc in
            let matches1 =
              if include_middle
              then
                ({
                   prefix = (FStar_Pervasives_Native.Some prefix1);
                   completion = k
                 }, v)
                :: matches
              else matches in
            let matches2 =
              if explore_left then aux lbt prefix1 matches1 else matches1 in
            matches2 in
      aux bt prefix []
let rec btree_fold :
  'a 'b . 'a btree -> (Prims.string -> 'a -> 'b -> 'b) -> 'b -> 'b =
  fun bt ->
    fun f ->
      fun acc ->
        match bt with
        | StrEmpty -> acc
        | StrBranch (k, v, lbt, rbt) ->
            let uu____2017 =
              let uu____2018 = btree_fold rbt f acc in f k v uu____2018 in
            btree_fold lbt f uu____2017
type path = path_elem Prims.list
type query = Prims.string Prims.list
let (query_to_string : Prims.string Prims.list -> Prims.string) =
  fun q -> FStar_String.concat "." q
type 'a name_collection =
  | Names of 'a btree 
  | ImportedNames of (Prims.string * 'a name_collection Prims.list) 
let uu___is_Names : 'a . 'a name_collection -> Prims.bool =
  fun projectee ->
    match projectee with | Names _0 -> true | uu____2077 -> false
let __proj__Names__item___0 : 'a . 'a name_collection -> 'a btree =
  fun projectee -> match projectee with | Names _0 -> _0
let uu___is_ImportedNames : 'a . 'a name_collection -> Prims.bool =
  fun projectee ->
    match projectee with | ImportedNames _0 -> true | uu____2122 -> false
let __proj__ImportedNames__item___0 :
  'a . 'a name_collection -> (Prims.string * 'a name_collection Prims.list) =
  fun projectee -> match projectee with | ImportedNames _0 -> _0
type 'a names = 'a name_collection Prims.list
type 'a trie = {
  bindings: 'a names ;
  namespaces: 'a trie names }
let __proj__Mktrie__item__bindings : 'a . 'a trie -> 'a names =
  fun projectee ->
    match projectee with | { bindings; namespaces;_} -> bindings
let __proj__Mktrie__item__namespaces : 'a . 'a trie -> 'a trie names =
  fun projectee ->
    match projectee with | { bindings; namespaces;_} -> namespaces
let trie_empty : 'uuuuuu2237 . unit -> 'uuuuuu2237 trie =
  fun uu____2241 -> { bindings = []; namespaces = [] }
let rec names_find_exact :
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names1 ->
    fun ns ->
      let uu____2272 =
        match names1 with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names2 ->
            let uu____2313 = btree_find_exact bt ns in
            (uu____2313, (FStar_Pervasives_Native.Some names2))
        | (ImportedNames (uu____2324, names2))::more_names ->
            let uu____2341 = names_find_exact names2 ns in
            (uu____2341, (FStar_Pervasives_Native.Some more_names)) in
      match uu____2272 with
      | (result, names2) ->
          (match (result, names2) with
           | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2387 -> result)
let rec trie_descend_exact :
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr ->
    fun query1 ->
      match query1 with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query2 ->
          let uu____2430 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2430
            (fun scope -> trie_descend_exact scope query2)
let rec trie_find_exact :
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr ->
    fun query1 ->
      match query1 with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query2 ->
          let uu____2476 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2476
            (fun scope -> trie_find_exact scope query2)
let names_insert : 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections ->
    fun id ->
      fun v ->
        let uu____2519 =
          match name_collections with
          | (Names bt)::tl -> (bt, tl)
          | uu____2556 -> (StrEmpty, name_collections) in
        match uu____2519 with
        | (bt, name_collections1) ->
            let uu____2581 =
              let uu____2584 = btree_insert_replace bt id v in
              Names uu____2584 in
            uu____2581 :: name_collections1
let rec namespaces_mutate :
  'a .
    'a trie names ->
      Prims.string ->
        query ->
          query ->
            ('a trie ->
               Prims.string -> query -> query -> 'a trie names -> 'a trie)
              -> ('a trie -> query -> 'a trie) -> 'a trie names
  =
  fun namespaces ->
    fun ns ->
      fun q ->
        fun rev_acc ->
          fun mut_node ->
            fun mut_leaf ->
              let trie1 =
                let uu____2778 = names_find_exact namespaces ns in
                FStar_Util.dflt (trie_empty ()) uu____2778 in
              let uu____2787 = trie_mutate trie1 q rev_acc mut_node mut_leaf in
              names_insert namespaces ns uu____2787
and trie_mutate :
  'a .
    'a trie ->
      query ->
        query ->
          ('a trie ->
             Prims.string -> query -> query -> 'a trie names -> 'a trie)
            -> ('a trie -> query -> 'a trie) -> 'a trie
  =
  fun tr ->
    fun q ->
      fun rev_acc ->
        fun mut_node ->
          fun mut_leaf ->
            match q with
            | [] -> mut_leaf tr rev_acc
            | id::q1 ->
                let ns' =
                  namespaces_mutate tr.namespaces id q1 (id :: rev_acc)
                    mut_node mut_leaf in
                mut_node tr id q1 rev_acc ns'
let trie_mutate_leaf :
  'a . 'a trie -> query -> ('a trie -> query -> 'a trie) -> 'a trie =
  fun tr ->
    fun query1 ->
      trie_mutate tr query1 []
        (fun tr1 ->
           fun uu____2879 ->
             fun uu____2880 ->
               fun uu____2881 ->
                 fun namespaces ->
                   let uu___379_2889 = tr1 in
                   { bindings = (uu___379_2889.bindings); namespaces })
let trie_insert : 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr ->
    fun ns_query ->
      fun id ->
        fun v ->
          trie_mutate_leaf tr ns_query
            (fun tr1 ->
               fun uu____2934 ->
                 let uu___388_2937 = tr1 in
                 let uu____2940 = names_insert tr1.bindings id v in
                 {
                   bindings = uu____2940;
                   namespaces = (uu___388_2937.namespaces)
                 })
let trie_import :
  'a .
    'a trie ->
      query ->
        query -> ('a trie -> 'a trie -> Prims.string -> 'a trie) -> 'a trie
  =
  fun tr ->
    fun host_query ->
      fun included_query ->
        fun mutator ->
          let label = query_to_string included_query in
          let included_trie =
            let uu____3011 = trie_descend_exact tr included_query in
            FStar_Util.dflt (trie_empty ()) uu____3011 in
          trie_mutate_leaf tr host_query
            (fun tr1 -> fun uu____3021 -> mutator tr1 included_trie label)
let trie_include : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr ->
    fun host_query ->
      fun included_query ->
        trie_import tr host_query included_query
          (fun tr1 ->
             fun inc ->
               fun label ->
                 let uu___406_3065 = tr1 in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___406_3065.namespaces)
                 })
let trie_open_namespace : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr ->
    fun host_query ->
      fun included_query ->
        trie_import tr host_query included_query
          (fun tr1 ->
             fun inc ->
               fun label ->
                 let uu___415_3115 = tr1 in
                 {
                   bindings = (uu___415_3115.bindings);
                   namespaces = ((ImportedNames (label, (inc.namespaces))) ::
                     (tr1.namespaces))
                 })
let trie_add_alias :
  'a . 'a trie -> Prims.string -> query -> query -> 'a trie =
  fun tr ->
    fun key ->
      fun host_query ->
        fun included_query ->
          trie_import tr host_query included_query
            (fun tr1 ->
               fun inc ->
                 fun label ->
                   trie_mutate_leaf tr1 [key]
                     (fun _ignored_overwritten_trie ->
                        fun uu____3180 ->
                          {
                            bindings =
                              [ImportedNames (label, (inc.bindings))];
                            namespaces = []
                          }))
let names_revmap :
  'a 'b .
    ('a btree -> 'b) -> 'a names -> (Prims.string Prims.list * 'b) Prims.list
  =
  fun fn ->
    fun name_collections ->
      let rec aux acc imports name_collections1 =
        FStar_List.fold_left
          (fun acc1 ->
             fun uu___5_3307 ->
               match uu___5_3307 with
               | Names bt ->
                   let uu____3329 =
                     let uu____3336 = fn bt in (imports, uu____3336) in
                   uu____3329 :: acc1
               | ImportedNames (nm, name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1 in
      aux [] [] name_collections
let btree_find_all :
  'a .
    Prims.string FStar_Pervasives_Native.option ->
      'a btree -> (prefix_match * 'a) Prims.list
  =
  fun prefix ->
    fun bt ->
      btree_fold bt
        (fun k ->
           fun tr -> fun acc -> ({ prefix; completion = k }, tr) :: acc) []
type name_search_term =
  | NSTAll 
  | NSTNone 
  | NSTPrefix of Prims.string 
let (uu___is_NSTAll : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTAll -> true | uu____3428 -> false
let (uu___is_NSTNone : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTNone -> true | uu____3434 -> false
let (uu___is_NSTPrefix : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTPrefix _0 -> true | uu____3441 -> false
let (__proj__NSTPrefix__item___0 : name_search_term -> Prims.string) =
  fun projectee -> match projectee with | NSTPrefix _0 -> _0
let names_find_rev :
  'a . 'a names -> name_search_term -> (path_elem * 'a) Prims.list =
  fun names1 ->
    fun id ->
      let matching_values_per_collection_with_imports =
        match id with
        | NSTNone -> []
        | NSTAll ->
            names_revmap (btree_find_all FStar_Pervasives_Native.None) names1
        | NSTPrefix "" ->
            names_revmap (btree_find_all (FStar_Pervasives_Native.Some ""))
              names1
        | NSTPrefix id1 ->
            names_revmap (fun bt -> btree_find_prefix bt id1) names1 in
      let matching_values_per_collection =
        FStar_List.map
          (fun uu____3569 ->
             match uu____3569 with
             | (imports, matches) ->
                 FStar_List.map
                   (fun uu____3617 ->
                      match uu____3617 with
                      | (segment, v) -> ((mk_path_el imports segment), v))
                   matches) matching_values_per_collection_with_imports in
      merge_increasing_lists_rev
        (fun uu____3635 ->
           match uu____3635 with
           | (path_el, uu____3641) -> (path_el.segment).completion)
        matching_values_per_collection
let rec trie_find_prefix' :
  'a .
    'a trie ->
      path -> query -> (path * 'a) Prims.list -> (path * 'a) Prims.list
  =
  fun tr ->
    fun path_acc ->
      fun query1 ->
        fun acc ->
          let uu____3695 =
            match query1 with
            | [] -> (NSTAll, NSTAll, [])
            | id::[] -> ((NSTPrefix id), (NSTPrefix id), [])
            | ns::query2 -> ((NSTPrefix ns), NSTNone, query2) in
          match uu____3695 with
          | (ns_search_term, bindings_search_term, query2) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1 ->
                     fun uu____3757 ->
                       match uu____3757 with
                       | (path_el, trie1) ->
                           trie_find_prefix' trie1 (path_el :: path_acc)
                             query2 acc1) acc matching_namespaces_rev in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term in
              FStar_List.rev_map_onto
                (fun uu____3802 ->
                   match uu____3802 with
                   | (path_el, v) ->
                       ((FStar_List.rev (path_el :: path_acc)), v))
                matching_bindings_rev acc_with_recursive_bindings
let trie_find_prefix : 'a . 'a trie -> query -> (path * 'a) Prims.list =
  fun tr -> fun query1 -> trie_find_prefix' tr [] query1 []
type ns_info = {
  ns_name: Prims.string ;
  ns_loaded: Prims.bool }
let (__proj__Mkns_info__item__ns_name : ns_info -> Prims.string) =
  fun projectee -> match projectee with | { ns_name; ns_loaded;_} -> ns_name
let (__proj__Mkns_info__item__ns_loaded : ns_info -> Prims.bool) =
  fun projectee ->
    match projectee with | { ns_name; ns_loaded;_} -> ns_loaded
type mod_info =
  {
  mod_name: Prims.string ;
  mod_path: Prims.string ;
  mod_loaded: Prims.bool }
let (__proj__Mkmod_info__item__mod_name : mod_info -> Prims.string) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_name
let (__proj__Mkmod_info__item__mod_path : mod_info -> Prims.string) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_path
let (__proj__Mkmod_info__item__mod_loaded : mod_info -> Prims.bool) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_loaded
let (mod_name : mod_info -> Prims.string) = fun md -> md.mod_name
type mod_symbol =
  | Module of mod_info 
  | Namespace of ns_info 
let (uu___is_Module : mod_symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____3932 -> false
let (__proj__Module__item___0 : mod_symbol -> mod_info) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Namespace : mod_symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Namespace _0 -> true | uu____3945 -> false
let (__proj__Namespace__item___0 : mod_symbol -> ns_info) =
  fun projectee -> match projectee with | Namespace _0 -> _0
type lid_symbol = FStar_Ident.lid
type symbol =
  | ModOrNs of mod_symbol 
  | Lid of lid_symbol 
let (uu___is_ModOrNs : symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | ModOrNs _0 -> true | uu____3968 -> false
let (__proj__ModOrNs__item___0 : symbol -> mod_symbol) =
  fun projectee -> match projectee with | ModOrNs _0 -> _0
let (uu___is_Lid : symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Lid _0 -> true | uu____3981 -> false
let (__proj__Lid__item___0 : symbol -> lid_symbol) =
  fun projectee -> match projectee with | Lid _0 -> _0
type table = {
  tbl_lids: lid_symbol trie ;
  tbl_mods: mod_symbol trie }
let (__proj__Mktable__item__tbl_lids : table -> lid_symbol trie) =
  fun projectee -> match projectee with | { tbl_lids; tbl_mods;_} -> tbl_lids
let (__proj__Mktable__item__tbl_mods : table -> mod_symbol trie) =
  fun projectee -> match projectee with | { tbl_lids; tbl_mods;_} -> tbl_mods
let (empty : table) =
  { tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ()) }
let (insert : table -> query -> Prims.string -> lid_symbol -> table) =
  fun tbl ->
    fun host_query ->
      fun id ->
        fun c ->
          let uu___533_4052 = tbl in
          let uu____4053 = trie_insert tbl.tbl_lids host_query id c in
          { tbl_lids = uu____4053; tbl_mods = (uu___533_4052.tbl_mods) }
let (register_alias : table -> Prims.string -> query -> query -> table) =
  fun tbl ->
    fun key ->
      fun host_query ->
        fun included_query ->
          let uu___543_4076 = tbl in
          let uu____4077 =
            trie_add_alias tbl.tbl_lids key host_query included_query in
          { tbl_lids = uu____4077; tbl_mods = (uu___543_4076.tbl_mods) }
let (register_include : table -> query -> query -> table) =
  fun tbl ->
    fun host_query ->
      fun included_query ->
        let uu___551_4095 = tbl in
        let uu____4096 = trie_include tbl.tbl_lids host_query included_query in
        { tbl_lids = uu____4096; tbl_mods = (uu___551_4095.tbl_mods) }
let (register_open : table -> Prims.bool -> query -> query -> table) =
  fun tbl ->
    fun is_module ->
      fun host_query ->
        fun included_query ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___562_4120 = tbl in
             let uu____4121 =
               trie_open_namespace tbl.tbl_lids host_query included_query in
             { tbl_lids = uu____4121; tbl_mods = (uu___562_4120.tbl_mods) })
let (register_module_path :
  table -> Prims.bool -> Prims.string -> query -> table) =
  fun tbl ->
    fun loaded ->
      fun path1 ->
        fun mod_query ->
          let ins_ns id bindings full_name loaded1 =
            let uu____4171 =
              let uu____4178 = names_find_exact bindings id in
              (uu____4178, loaded1) in
            match uu____4171 with
            | (FStar_Pervasives_Native.None, uu____4185) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____4188; ns_loaded = false;_}), true) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____4191, uu____4192) ->
                bindings in
          let ins_mod id bindings full_name loaded1 =
            names_insert bindings id
              (Module
                 {
                   mod_name = full_name;
                   mod_path = path1;
                   mod_loaded = loaded1
                 }) in
          let name_of_revq query1 =
            FStar_String.concat "." (FStar_List.rev query1) in
          let ins id q revq bindings loaded1 =
            let name = name_of_revq (id :: revq) in
            match q with
            | [] -> ins_mod id bindings name loaded1
            | uu____4275 -> ins_ns id bindings name loaded1 in
          let uu___607_4278 = tbl in
          let uu____4279 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr ->
                 fun id ->
                   fun q ->
                     fun revq ->
                       fun namespaces ->
                         let uu___616_4300 = tr in
                         let uu____4303 = ins id q revq tr.bindings loaded in
                         { bindings = uu____4303; namespaces })
              (fun tr -> fun uu____4309 -> tr) in
          { tbl_lids = (uu___607_4278.tbl_lids); tbl_mods = uu____4279 }
let (string_of_path : path -> Prims.string) =
  fun path1 ->
    let uu____4317 = FStar_List.map (fun el -> (el.segment).completion) path1 in
    FStar_String.concat "." uu____4317
let (match_length_of_path : path -> Prims.int) =
  fun path1 ->
    let uu____4327 =
      FStar_List.fold_left
        (fun acc ->
           fun elem ->
             let uu____4361 = acc in
             match uu____4361 with
             | (acc_len, uu____4379) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion in
                      (((acc_len + Prims.int_one) + completion_len),
                        (prefix, completion_len))
                  | FStar_Pervasives_Native.None -> acc))
        (Prims.int_zero, ("", Prims.int_zero)) path1 in
    match uu____4327 with
    | (length, (last_prefix, last_completion_length)) ->
        ((length - Prims.int_one) - last_completion_length) +
          (FStar_String.length last_prefix)
let (first_import_of_path :
  path -> Prims.string FStar_Pervasives_Native.option) =
  fun path1 ->
    match path1 with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____4423;_}::uu____4424 ->
        FStar_List.last imports
let (alist_of_ns_info :
  ns_info -> (Prims.string * FStar_Util.json) Prims.list) =
  fun ns_info1 ->
    [("name", (FStar_Util.JsonStr (ns_info1.ns_name)));
    ("loaded", (FStar_Util.JsonBool (ns_info1.ns_loaded)))]
let (alist_of_mod_info :
  mod_info -> (Prims.string * FStar_Util.json) Prims.list) =
  fun mod_info1 ->
    [("name", (FStar_Util.JsonStr (mod_info1.mod_name)));
    ("path", (FStar_Util.JsonStr (mod_info1.mod_path)));
    ("loaded", (FStar_Util.JsonBool (mod_info1.mod_loaded)))]
type completion_result =
  {
  completion_match_length: Prims.int ;
  completion_candidate: Prims.string ;
  completion_annotation: Prims.string }
let (__proj__Mkcompletion_result__item__completion_match_length :
  completion_result -> Prims.int) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_match_length
let (__proj__Mkcompletion_result__item__completion_candidate :
  completion_result -> Prims.string) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_candidate
let (__proj__Mkcompletion_result__item__completion_annotation :
  completion_result -> Prims.string) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_annotation
let (json_of_completion_result : completion_result -> FStar_Util.json) =
  fun result ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
let completion_result_of_lid :
  'uuuuuu4527 . (path * 'uuuuuu4527) -> completion_result =
  fun uu____4536 ->
    match uu____4536 with
    | (path1, _lid) ->
        let uu____4543 = match_length_of_path path1 in
        let uu____4544 = string_of_path path1 in
        let uu____4545 =
          let uu____4546 = first_import_of_path path1 in
          FStar_Util.dflt "" uu____4546 in
        {
          completion_match_length = uu____4543;
          completion_candidate = uu____4544;
          completion_annotation = uu____4545
        }
let (completion_result_of_mod :
  Prims.string -> Prims.bool -> path -> completion_result) =
  fun annot ->
    fun loaded ->
      fun path1 ->
        let uu____4564 = match_length_of_path path1 in
        let uu____4565 = string_of_path path1 in
        let uu____4566 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot in
        {
          completion_match_length = uu____4564;
          completion_candidate = uu____4565;
          completion_annotation = uu____4566
        }
let (completion_result_of_ns_or_mod :
  (path * mod_symbol) -> completion_result) =
  fun uu____4576 ->
    match uu____4576 with
    | (path1, symb) ->
        (match symb with
         | Module
             { mod_name = uu____4583; mod_path = uu____4584;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path1
         | Namespace { ns_name = uu____4586; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path1)
let (find_module_or_ns :
  table -> query -> mod_symbol FStar_Pervasives_Native.option) =
  fun tbl -> fun query1 -> trie_find_exact tbl.tbl_mods query1
let (autocomplete_lid : table -> query -> completion_result Prims.list) =
  fun tbl ->
    fun query1 ->
      let uu____4612 = trie_find_prefix tbl.tbl_lids query1 in
      FStar_List.map completion_result_of_lid uu____4612
let (autocomplete_mod_or_ns :
  table ->
    query ->
      ((path * mod_symbol) ->
         (path * mod_symbol) FStar_Pervasives_Native.option)
        -> completion_result Prims.list)
  =
  fun tbl ->
    fun query1 ->
      fun filter ->
        let uu____4665 =
          let uu____4672 = trie_find_prefix tbl.tbl_mods query1 in
          FStar_All.pipe_right uu____4672 (FStar_List.filter_map filter) in
        FStar_All.pipe_right uu____4665
          (FStar_List.map completion_result_of_ns_or_mod)