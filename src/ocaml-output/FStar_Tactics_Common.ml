open Prims
exception NotAListLiteral 
let (uu___is_NotAListLiteral : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotAListLiteral -> true | uu____5 -> false
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | TacticFailure uu____16 -> true | uu____17 -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | TacticFailure uu____23 -> uu____23
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | EExn uu____34 -> true | uu____35 -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu____41 -> uu____41