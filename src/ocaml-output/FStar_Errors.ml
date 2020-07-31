open Prims
exception Invalid_warn_error_setting of Prims.string 
let (uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Invalid_warn_error_setting uu____22 -> true
    | uu____23 -> false
let (__proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Invalid_warn_error_setting uu____29 -> uu____29
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CFatal -> true | uu____35 -> false
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CAlwaysError -> true | uu____41 -> false
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CError -> true | uu____47 -> false
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CWarning -> true | uu____53 -> false
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CSilent -> true | uu____59 -> false
type raw_error =
  | Error_DependencyAnalysisFailed 
  | Error_IDETooManyPops 
  | Error_IDEUnrecognized 
  | Error_InductiveTypeNotSatisfyPositivityCondition 
  | Error_InvalidUniverseVar 
  | Error_MissingFileName 
  | Error_ModuleFileNameMismatch 
  | Error_OpPlusInUniverse 
  | Error_OutOfRange 
  | Error_ProofObligationFailed 
  | Error_TooManyFiles 
  | Error_TypeCheckerFailToProve 
  | Error_TypeError 
  | Error_UncontrainedUnificationVar 
  | Error_UnexpectedGTotComputation 
  | Error_UnexpectedInstance 
  | Error_UnknownFatal_AssertionFailure 
  | Error_Z3InvocationError 
  | Error_IDEAssertionFailure 
  | Error_Z3SolverError 
  | Fatal_AbstractTypeDeclarationInInterface 
  | Fatal_ActionMustHaveFunctionType 
  | Fatal_AlreadyDefinedTopLevelDeclaration 
  | Fatal_ArgumentLengthMismatch 
  | Fatal_AssertionFailure 
  | Fatal_AssignToImmutableValues 
  | Fatal_AssumeValInInterface 
  | Fatal_BadlyInstantiatedSynthByTactic 
  | Fatal_BadSignatureShape 
  | Fatal_BinderAndArgsLengthMismatch 
  | Fatal_BothValAndLetInInterface 
  | Fatal_CardinalityConstraintViolated 
  | Fatal_ComputationNotTotal 
  | Fatal_ComputationTypeNotAllowed 
  | Fatal_ComputedTypeNotMatchAnnotation 
  | Fatal_ConstructorArgLengthMismatch 
  | Fatal_ConstructorFailedCheck 
  | Fatal_ConstructorNotFound 
  | Fatal_ConstsructorBuildWrongType 
  | Fatal_CycleInRecTypeAbbreviation 
  | Fatal_DataContructorNotFound 
  | Fatal_DefaultQualifierNotAllowedOnEffects 
  | Fatal_DefinitionNotFound 
  | Fatal_DisjuctivePatternVarsMismatch 
  | Fatal_DivergentComputationCannotBeIncludedInTotal 
  | Fatal_DuplicateInImplementation 
  | Fatal_DuplicateModuleOrInterface 
  | Fatal_DuplicateTopLevelNames 
  | Fatal_DuplicateTypeAnnotationAndValDecl 
  | Fatal_EffectCannotBeReified 
  | Fatal_EffectConstructorNotFullyApplied 
  | Fatal_EffectfulAndPureComputationMismatch 
  | Fatal_EffectNotFound 
  | Fatal_EffectsCannotBeComposed 
  | Fatal_ErrorInSolveDeferredConstraints 
  | Fatal_ErrorsReported 
  | Fatal_EscapedBoundVar 
  | Fatal_ExpectedArrowAnnotatedType 
  | Fatal_ExpectedGhostExpression 
  | Fatal_ExpectedPureExpression 
  | Fatal_ExpectNormalizedEffect 
  | Fatal_ExpectTermGotFunction 
  | Fatal_ExpectTrivialPreCondition 
  | Fatal_FailToCompileNativeTactic 
  | Fatal_FailToExtractNativeTactic 
  | Fatal_FailToProcessPragma 
  | Fatal_FailToResolveImplicitArgument 
  | Fatal_FailToSolveUniverseInEquality 
  | Fatal_FieldsNotBelongToSameRecordType 
  | Fatal_ForbiddenReferenceToCurrentModule 
  | Fatal_FreeVariables 
  | Fatal_FunctionTypeExpected 
  | Fatal_IdentifierNotFound 
  | Fatal_IllAppliedConstant 
  | Fatal_IllegalCharInByteArray 
  | Fatal_IllegalCharInOperatorName 
  | Fatal_IllTyped 
  | Fatal_ImpossibleAbbrevLidBundle 
  | Fatal_ImpossibleAbbrevRenameBundle 
  | Fatal_ImpossibleInductiveWithAbbrev 
  | Fatal_ImpossiblePrePostAbs 
  | Fatal_ImpossiblePrePostArrow 
  | Fatal_ImpossibleToGenerateDMEffect 
  | Fatal_ImpossibleTypeAbbrevBundle 
  | Fatal_ImpossibleTypeAbbrevSigeltBundle 
  | Fatal_IncludeModuleNotPrepared 
  | Fatal_IncoherentInlineUniverse 
  | Fatal_IncompatibleKinds 
  | Fatal_IncompatibleNumberOfTypes 
  | Fatal_IncompatibleSetOfUniverse 
  | Fatal_IncompatibleUniverse 
  | Fatal_InconsistentImplicitArgumentAnnotation 
  | Fatal_InconsistentImplicitQualifier 
  | Fatal_InconsistentQualifierAnnotation 
  | Fatal_InferredTypeCauseVarEscape 
  | Fatal_InlineRenamedAsUnfold 
  | Fatal_InsufficientPatternArguments 
  | Fatal_InterfaceAlreadyProcessed 
  | Fatal_InterfaceNotImplementedByModule 
  | Fatal_InterfaceWithTypeImplementation 
  | Fatal_InvalidFloatingPointNumber 
  | Fatal_InvalidFSDocKeyword 
  | Fatal_InvalidIdentifier 
  | Fatal_InvalidLemmaArgument 
  | Fatal_InvalidNumericLiteral 
  | Fatal_InvalidRedefinitionOfLexT 
  | Fatal_InvalidUnicodeInStringLiteral 
  | Fatal_InvalidUTF8Encoding 
  | Fatal_InvalidWarnErrorSetting 
  | Fatal_LetBoundMonadicMismatch 
  | Fatal_LetMutableForVariablesOnly 
  | Fatal_LetOpenModuleOnly 
  | Fatal_LetRecArgumentMismatch 
  | Fatal_MalformedActionDeclaration 
  | Fatal_MismatchedPatternType 
  | Fatal_MismatchUniversePolymorphic 
  | Fatal_MissingDataConstructor 
  | Fatal_MissingExposeInterfacesOption 
  | Fatal_MissingFieldInRecord 
  | Fatal_MissingImplementation 
  | Fatal_MissingImplicitArguments 
  | Fatal_MissingInterface 
  | Fatal_MissingNameInBinder 
  | Fatal_MissingPrimsModule 
  | Fatal_MissingQuantifierBinder 
  | Fatal_ModuleExpected 
  | Fatal_ModuleFileNotFound 
  | Fatal_ModuleFirstStatement 
  | Fatal_ModuleNotFound 
  | Fatal_ModuleOrFileNotFound 
  | Fatal_MonadAlreadyDefined 
  | Fatal_MoreThanOneDeclaration 
  | Fatal_MultipleLetBinding 
  | Fatal_NameNotFound 
  | Fatal_NameSpaceNotFound 
  | Fatal_NegativeUniverseConstFatal_NotSupported 
  | Fatal_NoFileProvided 
  | Fatal_NonInductiveInMutuallyDefinedType 
  | Fatal_NonLinearPatternNotPermitted 
  | Fatal_NonLinearPatternVars 
  | Fatal_NonSingletonTopLevel 
  | Fatal_NonSingletonTopLevelModule 
  | Error_NonTopRecFunctionNotFullyEncoded 
  | Fatal_NonTrivialPreConditionInPrims 
  | Fatal_NonVariableInductiveTypeParameter 
  | Fatal_NotApplicationOrFv 
  | Fatal_NotEnoughArgsToEffect 
  | Fatal_NotEnoughArgumentsForEffect 
  | Fatal_NotFunctionType 
  | Fatal_NotSupported 
  | Fatal_NotTopLevelModule 
  | Fatal_NotValidFStarFile 
  | Fatal_NotValidIncludeDirectory 
  | Fatal_OneModulePerFile 
  | Fatal_OpenGoalsInSynthesis 
  | Fatal_OptionsNotCompatible 
  | Fatal_OutOfOrder 
  | Fatal_ParseErrors 
  | Fatal_ParseItError 
  | Fatal_PolyTypeExpected 
  | Fatal_PossibleInfiniteTyp 
  | Fatal_PreModuleMismatch 
  | Fatal_QulifierListNotPermitted 
  | Fatal_RecursiveFunctionLiteral 
  | Fatal_ReflectOnlySupportedOnEffects 
  | Fatal_ReservedPrefix 
  | Fatal_SMTOutputParseError 
  | Fatal_SMTSolverError 
  | Fatal_SyntaxError 
  | Fatal_SynthByTacticError 
  | Fatal_TacticGotStuck 
  | Fatal_TcOneFragmentFailed 
  | Fatal_TermOutsideOfDefLanguage 
  | Fatal_ToManyArgumentToFunction 
  | Fatal_TooManyOrTooFewFileMatch 
  | Fatal_TooManyPatternArguments 
  | Fatal_TooManyUniverse 
  | Fatal_TypeMismatch 
  | Fatal_TypeWithinPatternsAllowedOnVariablesOnly 
  | Fatal_UnableToReadFile 
  | Fatal_UnepxectedOrUnboundOperator 
  | Fatal_UnexpectedBinder 
  | Fatal_UnexpectedBindShape 
  | Fatal_UnexpectedChar 
  | Fatal_UnexpectedComputationTypeForLetRec 
  | Fatal_UnexpectedConstructorType 
  | Fatal_UnexpectedDataConstructor 
  | Fatal_UnexpectedEffect 
  | Fatal_UnexpectedEmptyRecord 
  | Fatal_UnexpectedExpressionType 
  | Fatal_UnexpectedFunctionParameterType 
  | Fatal_UnexpectedGeneralizedUniverse 
  | Fatal_UnexpectedGTotForLetRec 
  | Fatal_UnexpectedGuard 
  | Fatal_UnexpectedIdentifier 
  | Fatal_UnexpectedImplicitArgument 
  | Fatal_UnexpectedImplictArgument 
  | Fatal_UnexpectedInductivetype 
  | Fatal_UnexpectedLetBinding 
  | Fatal_UnexpectedModuleDeclaration 
  | Fatal_UnexpectedNumberOfUniverse 
  | Fatal_UnexpectedNumericLiteral 
  | Fatal_UnexpectedOperatorSymbol 
  | Fatal_UnexpectedPattern 
  | Fatal_UnexpectedPosition 
  | Fatal_UnExpectedPreCondition 
  | Fatal_UnexpectedReturnShape 
  | Fatal_UnexpectedSignatureForMonad 
  | Fatal_UnexpectedTerm 
  | Fatal_UnexpectedTermInUniverse 
  | Fatal_UnexpectedTermType 
  | Fatal_UnexpectedTermVQuote 
  | Fatal_UnexpectedUniversePolymorphicReturn 
  | Fatal_UnexpectedUniverseVariable 
  | Fatal_UnfoldableDeprecated 
  | Fatal_UnificationNotWellFormed 
  | Fatal_Uninstantiated 
  | Error_UninstantiatedUnificationVarInTactic 
  | Fatal_UninstantiatedVarInTactic 
  | Fatal_UniverseMightContainSumOfTwoUnivVars 
  | Fatal_UniversePolymorphicInnerLetBound 
  | Fatal_UnknownAttribute 
  | Fatal_UnknownToolForDep 
  | Fatal_UnrecognizedExtension 
  | Fatal_UnresolvedPatternVar 
  | Fatal_UnsupportedConstant 
  | Fatal_UnsupportedDisjuctivePatterns 
  | Fatal_UnsupportedQualifier 
  | Fatal_UserTacticFailure 
  | Fatal_ValueRestriction 
  | Fatal_VariableNotFound 
  | Fatal_WrongBodyTypeForReturnWP 
  | Fatal_WrongDataAppHeadFormat 
  | Fatal_WrongDefinitionOrder 
  | Fatal_WrongResultTypeAfterConstrutor 
  | Fatal_WrongTerm 
  | Fatal_WhenClauseNotSupported 
  | Unused01 
  | Warning_AddImplicitAssumeNewQualifier 
  | Warning_AdmitWithoutDefinition 
  | Warning_CachedFile 
  | Warning_DefinitionNotTranslated 
  | Warning_DependencyFound 
  | Warning_DeprecatedEqualityOnBinder 
  | Warning_DeprecatedOpaqueQualifier 
  | Warning_DocOverwrite 
  | Warning_FileNotWritten 
  | Warning_Filtered 
  | Warning_FunctionLiteralPrecisionLoss 
  | Warning_FunctionNotExtacted 
  | Warning_HintFailedToReplayProof 
  | Warning_HitReplayFailed 
  | Warning_IDEIgnoreCodeGen 
  | Warning_IllFormedGoal 
  | Warning_InaccessibleArgument 
  | Warning_IncoherentImplicitQualifier 
  | Warning_IrrelevantQualifierOnArgumentToReflect 
  | Warning_IrrelevantQualifierOnArgumentToReify 
  | Warning_MalformedWarnErrorList 
  | Warning_MetaAlienNotATmUnknown 
  | Warning_MultipleAscriptions 
  | Warning_NondependentUserDefinedDataType 
  | Warning_NonListLiteralSMTPattern 
  | Warning_NormalizationFailure 
  | Warning_NotDependentArrow 
  | Warning_NotEmbedded 
  | Warning_PatternMissingBoundVar 
  | Warning_RecursiveDependency 
  | Warning_RedundantExplicitCurrying 
  | Warning_SMTPatTDeprecated 
  | Warning_SMTPatternIllFormed 
  | Warning_TopLevelEffect 
  | Warning_UnboundModuleReference 
  | Warning_UnexpectedFile 
  | Warning_UnexpectedFsTypApp 
  | Warning_UnexpectedZ3Output 
  | Warning_UnprotectedTerm 
  | Warning_UnrecognizedAttribute 
  | Warning_UpperBoundCandidateAlreadyVisited 
  | Warning_UseDefaultEffect 
  | Warning_WrongErrorLocation 
  | Warning_Z3InvocationWarning 
  | Warning_PluginNotImplemented 
  | Warning_MissingInterfaceOrImplementation 
  | Warning_ConstructorBuildsUnexpectedType 
  | Warning_ModuleOrFileNotFoundWarning 
  | Error_NoLetMutable 
  | Error_BadImplicit 
  | Warning_DeprecatedDefinition 
  | Fatal_SMTEncodingArityMismatch 
  | Warning_Defensive 
  | Warning_CantInspect 
  | Warning_NilGivenExplicitArgs 
  | Warning_ConsAppliedExplicitArgs 
  | Warning_UnembedBinderKnot 
  | Fatal_TacticProofRelevantGoal 
  | Warning_TacAdmit 
  | Fatal_IncoherentPatterns 
  | Error_NoSMTButNeeded 
  | Fatal_UnexpectedAntiquotation 
  | Fatal_SplicedUndef 
  | Fatal_SpliceUnembedFail 
  | Warning_ExtractionUnexpectedEffect 
  | Error_DidNotFail 
  | Warning_UnappliedFail 
  | Warning_QuantifierWithoutPattern 
  | Error_EmptyFailErrs 
  | Warning_logicqualifier 
  | Fatal_CyclicDependence 
  | Error_InductiveAnnotNotAType 
  | Fatal_FriendInterface 
  | Error_CannotRedefineConst 
  | Error_BadClassDecl 
  | Error_BadInductiveParam 
  | Error_FieldShadow 
  | Error_UnexpectedDM4FType 
  | Fatal_EffectAbbreviationResultTypeMismatch 
  | Error_AlreadyCachedAssertionFailure 
  | Error_MustEraseMissing 
  | Warning_EffectfulArgumentToErasedFunction 
  | Fatal_EmptySurfaceLet 
  | Warning_UnexpectedCheckedFile 
  | Fatal_ExtractionUnsupported 
  | Warning_SMTErrorReason 
  | Warning_CoercionNotFound 
  | Error_QuakeFailed 
  | Error_IllSMTPat 
  | Error_IllScopedTerm 
  | Warning_UnusedLetRec 
  | Fatal_Effects_Ordering_Coherence 
  | Warning_BleedingEdge_Feature 
  | Warning_IgnoredBinding 
  | Warning_CouldNotReadHints 
  | Fatal_BadUvar 
  | Warning_WarnOnUse 
  | Warning_DeprecatedAttributeSyntax 
  | Warning_DeprecatedGeneric 
  | Error_BadSplice 
let (uu___is_Error_DependencyAnalysisFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_DependencyAnalysisFailed -> true
    | uu____65 -> false
let (uu___is_Error_IDETooManyPops : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDETooManyPops -> true | uu____71 -> false
let (uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDEUnrecognized -> true | uu____77 -> false
let (uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition -> true
    | uu____83 -> false
let (uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InvalidUniverseVar -> true
    | uu____89 -> false
let (uu___is_Error_MissingFileName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_MissingFileName -> true | uu____95 -> false
let (uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ModuleFileNameMismatch -> true
    | uu____101 -> false
let (uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_OpPlusInUniverse -> true
    | uu____107 -> false
let (uu___is_Error_OutOfRange : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_OutOfRange -> true | uu____113 -> false
let (uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ProofObligationFailed -> true
    | uu____119 -> false
let (uu___is_Error_TooManyFiles : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TooManyFiles -> true | uu____125 -> false
let (uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_TypeCheckerFailToProve -> true
    | uu____131 -> false
let (uu___is_Error_TypeError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TypeError -> true | uu____137 -> false
let (uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UncontrainedUnificationVar -> true
    | uu____143 -> false
let (uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedGTotComputation -> true
    | uu____149 -> false
let (uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedInstance -> true
    | uu____155 -> false
let (uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure -> true
    | uu____161 -> false
let (uu___is_Error_Z3InvocationError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_Z3InvocationError -> true
    | uu____167 -> false
let (uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_IDEAssertionFailure -> true
    | uu____173 -> false
let (uu___is_Error_Z3SolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_Z3SolverError -> true | uu____179 -> false
let (uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface -> true
    | uu____185 -> false
let (uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType -> true
    | uu____191 -> false
let (uu___is_Fatal_AlreadyDefinedTopLevelDeclaration :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration -> true
    | uu____197 -> false
let (uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ArgumentLengthMismatch -> true
    | uu____203 -> false
let (uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssertionFailure -> true
    | uu____209 -> false
let (uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssignToImmutableValues -> true
    | uu____215 -> false
let (uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssumeValInInterface -> true
    | uu____221 -> false
let (uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic -> true
    | uu____227 -> false
let (uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BadSignatureShape -> true
    | uu____233 -> false
let (uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch -> true
    | uu____239 -> false
let (uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BothValAndLetInInterface -> true
    | uu____245 -> false
let (uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CardinalityConstraintViolated -> true
    | uu____251 -> false
let (uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationNotTotal -> true
    | uu____257 -> false
let (uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed -> true
    | uu____263 -> false
let (uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation -> true
    | uu____269 -> false
let (uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch -> true
    | uu____275 -> false
let (uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorFailedCheck -> true
    | uu____281 -> false
let (uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorNotFound -> true
    | uu____287 -> false
let (uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType -> true
    | uu____293 -> false
let (uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation -> true
    | uu____299 -> false
let (uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DataContructorNotFound -> true
    | uu____305 -> false
let (uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects -> true
    | uu____311 -> false
let (uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefinitionNotFound -> true
    | uu____317 -> false
let (uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch -> true
    | uu____323 -> false
let (uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal -> true
    | uu____329 -> false
let (uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateInImplementation -> true
    | uu____335 -> false
let (uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface -> true
    | uu____341 -> false
let (uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTopLevelNames -> true
    | uu____347 -> false
let (uu___is_Fatal_DuplicateTypeAnnotationAndValDecl :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl -> true
    | uu____353 -> false
let (uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectCannotBeReified -> true
    | uu____359 -> false
let (uu___is_Fatal_EffectConstructorNotFullyApplied :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied -> true
    | uu____365 -> false
let (uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch -> true
    | uu____371 -> false
let (uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EffectNotFound -> true | uu____377 -> false
let (uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectsCannotBeComposed -> true
    | uu____383 -> false
let (uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints -> true
    | uu____389 -> false
let (uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ErrorsReported -> true | uu____395 -> false
let (uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EscapedBoundVar -> true | uu____401 -> false
let (uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType -> true
    | uu____407 -> false
let (uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedGhostExpression -> true
    | uu____413 -> false
let (uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedPureExpression -> true
    | uu____419 -> false
let (uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectNormalizedEffect -> true
    | uu____425 -> false
let (uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTermGotFunction -> true
    | uu____431 -> false
let (uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition -> true
    | uu____437 -> false
let (uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToCompileNativeTactic -> true
    | uu____443 -> false
let (uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToExtractNativeTactic -> true
    | uu____449 -> false
let (uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToProcessPragma -> true
    | uu____455 -> false
let (uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument -> true
    | uu____461 -> false
let (uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality -> true
    | uu____467 -> false
let (uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType -> true
    | uu____473 -> false
let (uu___is_Fatal_ForbiddenReferenceToCurrentModule :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule -> true
    | uu____479 -> false
let (uu___is_Fatal_FreeVariables : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_FreeVariables -> true | uu____485 -> false
let (uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FunctionTypeExpected -> true
    | uu____491 -> false
let (uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IdentifierNotFound -> true
    | uu____497 -> false
let (uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllAppliedConstant -> true
    | uu____503 -> false
let (uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInByteArray -> true
    | uu____509 -> false
let (uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInOperatorName -> true
    | uu____515 -> false
let (uu___is_Fatal_IllTyped : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_IllTyped -> true | uu____521 -> false
let (uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle -> true
    | uu____527 -> false
let (uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle -> true
    | uu____533 -> false
let (uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev -> true
    | uu____539 -> false
let (uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs -> true
    | uu____545 -> false
let (uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow -> true
    | uu____551 -> false
let (uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect -> true
    | uu____557 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle -> true
    | uu____563 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle -> true
    | uu____569 -> false
let (uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared -> true
    | uu____575 -> false
let (uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentInlineUniverse -> true
    | uu____581 -> false
let (uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleKinds -> true
    | uu____587 -> false
let (uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes -> true
    | uu____593 -> false
let (uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse -> true
    | uu____599 -> false
let (uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleUniverse -> true
    | uu____605 -> false
let (uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation -> true
    | uu____611 -> false
let (uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier -> true
    | uu____617 -> false
let (uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation -> true
    | uu____623 -> false
let (uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape -> true
    | uu____629 -> false
let (uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold -> true
    | uu____635 -> false
let (uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InsufficientPatternArguments -> true
    | uu____641 -> false
let (uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed -> true
    | uu____647 -> false
let (uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule -> true
    | uu____653 -> false
let (uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation -> true
    | uu____659 -> false
let (uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber -> true
    | uu____665 -> false
let (uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFSDocKeyword -> true
    | uu____671 -> false
let (uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidIdentifier -> true
    | uu____677 -> false
let (uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidLemmaArgument -> true
    | uu____683 -> false
let (uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidNumericLiteral -> true
    | uu____689 -> false
let (uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT -> true
    | uu____695 -> false
let (uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral -> true
    | uu____701 -> false
let (uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUTF8Encoding -> true
    | uu____707 -> false
let (uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting -> true
    | uu____713 -> false
let (uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch -> true
    | uu____719 -> false
let (uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly -> true
    | uu____725 -> false
let (uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetOpenModuleOnly -> true
    | uu____731 -> false
let (uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetRecArgumentMismatch -> true
    | uu____737 -> false
let (uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MalformedActionDeclaration -> true
    | uu____743 -> false
let (uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchedPatternType -> true
    | uu____749 -> false
let (uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic -> true
    | uu____755 -> false
let (uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingDataConstructor -> true
    | uu____761 -> false
let (uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption -> true
    | uu____767 -> false
let (uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingFieldInRecord -> true
    | uu____773 -> false
let (uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplementation -> true
    | uu____779 -> false
let (uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplicitArguments -> true
    | uu____785 -> false
let (uu___is_Fatal_MissingInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingInterface -> true
    | uu____791 -> false
let (uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingNameInBinder -> true
    | uu____797 -> false
let (uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingPrimsModule -> true
    | uu____803 -> false
let (uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingQuantifierBinder -> true
    | uu____809 -> false
let (uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleExpected -> true | uu____815 -> false
let (uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFileNotFound -> true
    | uu____821 -> false
let (uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFirstStatement -> true
    | uu____827 -> false
let (uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleNotFound -> true | uu____833 -> false
let (uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleOrFileNotFound -> true
    | uu____839 -> false
let (uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MonadAlreadyDefined -> true
    | uu____845 -> false
let (uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MoreThanOneDeclaration -> true
    | uu____851 -> false
let (uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MultipleLetBinding -> true
    | uu____857 -> false
let (uu___is_Fatal_NameNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NameNotFound -> true | uu____863 -> false
let (uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NameSpaceNotFound -> true
    | uu____869 -> false
let (uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported -> true
    | uu____875 -> false
let (uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NoFileProvided -> true | uu____881 -> false
let (uu___is_Fatal_NonInductiveInMutuallyDefinedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType -> true
    | uu____887 -> false
let (uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted -> true
    | uu____893 -> false
let (uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternVars -> true
    | uu____899 -> false
let (uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevel -> true
    | uu____905 -> false
let (uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule -> true
    | uu____911 -> false
let (uu___is_Error_NonTopRecFunctionNotFullyEncoded :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_NonTopRecFunctionNotFullyEncoded -> true
    | uu____917 -> false
let (uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims -> true
    | uu____923 -> false
let (uu___is_Fatal_NonVariableInductiveTypeParameter :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter -> true
    | uu____929 -> false
let (uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotApplicationOrFv -> true
    | uu____935 -> false
let (uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect -> true
    | uu____941 -> false
let (uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect -> true
    | uu____947 -> false
let (uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotFunctionType -> true | uu____953 -> false
let (uu___is_Fatal_NotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotSupported -> true | uu____959 -> false
let (uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotTopLevelModule -> true
    | uu____965 -> false
let (uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidFStarFile -> true
    | uu____971 -> false
let (uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidIncludeDirectory -> true
    | uu____977 -> false
let (uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OneModulePerFile -> true
    | uu____983 -> false
let (uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis -> true
    | uu____989 -> false
let (uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OptionsNotCompatible -> true
    | uu____995 -> false
let (uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_OutOfOrder -> true | uu____1001 -> false
let (uu___is_Fatal_ParseErrors : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseErrors -> true | uu____1007 -> false
let (uu___is_Fatal_ParseItError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseItError -> true | uu____1013 -> false
let (uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PolyTypeExpected -> true
    | uu____1019 -> false
let (uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PossibleInfiniteTyp -> true
    | uu____1025 -> false
let (uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PreModuleMismatch -> true
    | uu____1031 -> false
let (uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_QulifierListNotPermitted -> true
    | uu____1037 -> false
let (uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral -> true
    | uu____1043 -> false
let (uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects -> true
    | uu____1049 -> false
let (uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ReservedPrefix -> true | uu____1055 -> false
let (uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTOutputParseError -> true
    | uu____1061 -> false
let (uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SMTSolverError -> true | uu____1067 -> false
let (uu___is_Fatal_SyntaxError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SyntaxError -> true | uu____1073 -> false
let (uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SynthByTacticError -> true
    | uu____1079 -> false
let (uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TacticGotStuck -> true | uu____1085 -> false
let (uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TcOneFragmentFailed -> true
    | uu____1091 -> false
let (uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage -> true
    | uu____1097 -> false
let (uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ToManyArgumentToFunction -> true
    | uu____1103 -> false
let (uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch -> true
    | uu____1109 -> false
let (uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyPatternArguments -> true
    | uu____1115 -> false
let (uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyUniverse -> true
    | uu____1121 -> false
let (uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TypeMismatch -> true | uu____1127 -> false
let (uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> true
    | uu____1133 -> false
let (uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnableToReadFile -> true
    | uu____1139 -> false
let (uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator -> true
    | uu____1145 -> false
let (uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBinder -> true
    | uu____1151 -> false
let (uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBindShape -> true
    | uu____1157 -> false
let (uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedChar -> true | uu____1163 -> false
let (uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec -> true
    | uu____1169 -> false
let (uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedConstructorType -> true
    | uu____1175 -> false
let (uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedDataConstructor -> true
    | uu____1181 -> false
let (uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEffect -> true
    | uu____1187 -> false
let (uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord -> true
    | uu____1193 -> false
let (uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedExpressionType -> true
    | uu____1199 -> false
let (uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType -> true
    | uu____1205 -> false
let (uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse -> true
    | uu____1211 -> false
let (uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec -> true
    | uu____1217 -> false
let (uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGuard -> true
    | uu____1223 -> false
let (uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedIdentifier -> true
    | uu____1229 -> false
let (uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument -> true
    | uu____1235 -> false
let (uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplictArgument -> true
    | uu____1241 -> false
let (uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedInductivetype -> true
    | uu____1247 -> false
let (uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedLetBinding -> true
    | uu____1253 -> false
let (uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration -> true
    | uu____1259 -> false
let (uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse -> true
    | uu____1265 -> false
let (uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral -> true
    | uu____1271 -> false
let (uu___is_Fatal_UnexpectedOperatorSymbol : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol -> true
    | uu____1277 -> false
let (uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPattern -> true
    | uu____1283 -> false
let (uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPosition -> true
    | uu____1289 -> false
let (uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnExpectedPreCondition -> true
    | uu____1295 -> false
let (uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedReturnShape -> true
    | uu____1301 -> false
let (uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad -> true
    | uu____1307 -> false
let (uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedTerm -> true | uu____1313 -> false
let (uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse -> true
    | uu____1319 -> false
let (uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermType -> true
    | uu____1325 -> false
let (uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermVQuote -> true
    | uu____1331 -> false
let (uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn -> true
    | uu____1337 -> false
let (uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable -> true
    | uu____1343 -> false
let (uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnfoldableDeprecated -> true
    | uu____1349 -> false
let (uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnificationNotWellFormed -> true
    | uu____1355 -> false
let (uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_Uninstantiated -> true | uu____1361 -> false
let (uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UninstantiatedUnificationVarInTactic -> true
    | uu____1367 -> false
let (uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic -> true
    | uu____1373 -> false
let (uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars -> true
    | uu____1379 -> false
let (uu___is_Fatal_UniversePolymorphicInnerLetBound :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound -> true
    | uu____1385 -> false
let (uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownAttribute -> true
    | uu____1391 -> false
let (uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownToolForDep -> true
    | uu____1397 -> false
let (uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnrecognizedExtension -> true
    | uu____1403 -> false
let (uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnresolvedPatternVar -> true
    | uu____1409 -> false
let (uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedConstant -> true
    | uu____1415 -> false
let (uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns -> true
    | uu____1421 -> false
let (uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedQualifier -> true
    | uu____1427 -> false
let (uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UserTacticFailure -> true
    | uu____1433 -> false
let (uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ValueRestriction -> true
    | uu____1439 -> false
let (uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_VariableNotFound -> true
    | uu____1445 -> false
let (uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP -> true
    | uu____1451 -> false
let (uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat -> true
    | uu____1457 -> false
let (uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDefinitionOrder -> true
    | uu____1463 -> false
let (uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor -> true
    | uu____1469 -> false
let (uu___is_Fatal_WrongTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_WrongTerm -> true | uu____1475 -> false
let (uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WhenClauseNotSupported -> true
    | uu____1481 -> false
let (uu___is_Unused01 : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Unused01 -> true | uu____1487 -> false
let (uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier -> true
    | uu____1493 -> false
let (uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_AdmitWithoutDefinition -> true
    | uu____1499 -> false
let (uu___is_Warning_CachedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CachedFile -> true | uu____1505 -> false
let (uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DefinitionNotTranslated -> true
    | uu____1511 -> false
let (uu___is_Warning_DependencyFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DependencyFound -> true
    | uu____1517 -> false
let (uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder -> true
    | uu____1523 -> false
let (uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier -> true
    | uu____1529 -> false
let (uu___is_Warning_DocOverwrite : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_DocOverwrite -> true | uu____1535 -> false
let (uu___is_Warning_FileNotWritten : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FileNotWritten -> true
    | uu____1541 -> false
let (uu___is_Warning_Filtered : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Filtered -> true | uu____1547 -> false
let (uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss -> true
    | uu____1553 -> false
let (uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FunctionNotExtacted -> true
    | uu____1559 -> false
let (uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HintFailedToReplayProof -> true
    | uu____1565 -> false
let (uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HitReplayFailed -> true
    | uu____1571 -> false
let (uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IDEIgnoreCodeGen -> true
    | uu____1577 -> false
let (uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IllFormedGoal -> true
    | uu____1583 -> false
let (uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_InaccessibleArgument -> true
    | uu____1589 -> false
let (uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IncoherentImplicitQualifier -> true
    | uu____1595 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect -> true
    | uu____1601 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify -> true
    | uu____1607 -> false
let (uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MalformedWarnErrorList -> true
    | uu____1613 -> false
let (uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown -> true
    | uu____1619 -> false
let (uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MultipleAscriptions -> true
    | uu____1625 -> false
let (uu___is_Warning_NondependentUserDefinedDataType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NondependentUserDefinedDataType -> true
    | uu____1631 -> false
let (uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NonListLiteralSMTPattern -> true
    | uu____1637 -> false
let (uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NormalizationFailure -> true
    | uu____1643 -> false
let (uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NotDependentArrow -> true
    | uu____1649 -> false
let (uu___is_Warning_NotEmbedded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_NotEmbedded -> true | uu____1655 -> false
let (uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PatternMissingBoundVar -> true
    | uu____1661 -> false
let (uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RecursiveDependency -> true
    | uu____1667 -> false
let (uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RedundantExplicitCurrying -> true
    | uu____1673 -> false
let (uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatTDeprecated -> true
    | uu____1679 -> false
let (uu___is_Warning_SMTPatternIllFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatternIllFormed -> true
    | uu____1685 -> false
let (uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_TopLevelEffect -> true
    | uu____1691 -> false
let (uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnboundModuleReference -> true
    | uu____1697 -> false
let (uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFile -> true
    | uu____1703 -> false
let (uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFsTypApp -> true
    | uu____1709 -> false
let (uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedZ3Output -> true
    | uu____1715 -> false
let (uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnprotectedTerm -> true
    | uu____1721 -> false
let (uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnrecognizedAttribute -> true
    | uu____1727 -> false
let (uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited -> true
    | uu____1733 -> false
let (uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UseDefaultEffect -> true
    | uu____1739 -> false
let (uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_WrongErrorLocation -> true
    | uu____1745 -> false
let (uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_Z3InvocationWarning -> true
    | uu____1751 -> false
let (uu___is_Warning_PluginNotImplemented : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PluginNotImplemented -> true
    | uu____1757 -> false
let (uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation -> true
    | uu____1763 -> false
let (uu___is_Warning_ConstructorBuildsUnexpectedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType -> true
    | uu____1769 -> false
let (uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning -> true
    | uu____1775 -> false
let (uu___is_Error_NoLetMutable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoLetMutable -> true | uu____1781 -> false
let (uu___is_Error_BadImplicit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadImplicit -> true | uu____1787 -> false
let (uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedDefinition -> true
    | uu____1793 -> false
let (uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTEncodingArityMismatch -> true
    | uu____1799 -> false
let (uu___is_Warning_Defensive : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Defensive -> true | uu____1805 -> false
let (uu___is_Warning_CantInspect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CantInspect -> true | uu____1811 -> false
let (uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NilGivenExplicitArgs -> true
    | uu____1817 -> false
let (uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConsAppliedExplicitArgs -> true
    | uu____1823 -> false
let (uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnembedBinderKnot -> true
    | uu____1829 -> false
let (uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TacticProofRelevantGoal -> true
    | uu____1835 -> false
let (uu___is_Warning_TacAdmit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_TacAdmit -> true | uu____1841 -> false
let (uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentPatterns -> true
    | uu____1847 -> false
let (uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoSMTButNeeded -> true | uu____1853 -> false
let (uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedAntiquotation -> true
    | uu____1859 -> false
let (uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SplicedUndef -> true | uu____1865 -> false
let (uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SpliceUnembedFail -> true
    | uu____1871 -> false
let (uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ExtractionUnexpectedEffect -> true
    | uu____1877 -> false
let (uu___is_Error_DidNotFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_DidNotFail -> true | uu____1883 -> false
let (uu___is_Warning_UnappliedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnappliedFail -> true
    | uu____1889 -> false
let (uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_QuantifierWithoutPattern -> true
    | uu____1895 -> false
let (uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_EmptyFailErrs -> true | uu____1901 -> false
let (uu___is_Warning_logicqualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_logicqualifier -> true
    | uu____1907 -> false
let (uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CyclicDependence -> true
    | uu____1913 -> false
let (uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveAnnotNotAType -> true
    | uu____1919 -> false
let (uu___is_Fatal_FriendInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FriendInterface -> true
    | uu____1925 -> false
let (uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_CannotRedefineConst -> true
    | uu____1931 -> false
let (uu___is_Error_BadClassDecl : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadClassDecl -> true | uu____1937 -> false
let (uu___is_Error_BadInductiveParam : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_BadInductiveParam -> true
    | uu____1943 -> false
let (uu___is_Error_FieldShadow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_FieldShadow -> true | uu____1949 -> false
let (uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedDM4FType -> true
    | uu____1955 -> false
let (uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectAbbreviationResultTypeMismatch -> true
    | uu____1961 -> false
let (uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_AlreadyCachedAssertionFailure -> true
    | uu____1967 -> false
let (uu___is_Error_MustEraseMissing : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_MustEraseMissing -> true
    | uu____1973 -> false
let (uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_EffectfulArgumentToErasedFunction -> true
    | uu____1979 -> false
let (uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EmptySurfaceLet -> true
    | uu____1985 -> false
let (uu___is_Warning_UnexpectedCheckedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedCheckedFile -> true
    | uu____1991 -> false
let (uu___is_Fatal_ExtractionUnsupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExtractionUnsupported -> true
    | uu____1997 -> false
let (uu___is_Warning_SMTErrorReason : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTErrorReason -> true
    | uu____2003 -> false
let (uu___is_Warning_CoercionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CoercionNotFound -> true
    | uu____2009 -> false
let (uu___is_Error_QuakeFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_QuakeFailed -> true | uu____2015 -> false
let (uu___is_Error_IllSMTPat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllSMTPat -> true | uu____2021 -> false
let (uu___is_Error_IllScopedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllScopedTerm -> true | uu____2027 -> false
let (uu___is_Warning_UnusedLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_UnusedLetRec -> true | uu____2033 -> false
let (uu___is_Fatal_Effects_Ordering_Coherence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_Effects_Ordering_Coherence -> true
    | uu____2039 -> false
let (uu___is_Warning_BleedingEdge_Feature : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_BleedingEdge_Feature -> true
    | uu____2045 -> false
let (uu___is_Warning_IgnoredBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IgnoredBinding -> true
    | uu____2051 -> false
let (uu___is_Warning_CouldNotReadHints : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CouldNotReadHints -> true
    | uu____2057 -> false
let (uu___is_Fatal_BadUvar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_BadUvar -> true | uu____2063 -> false
let (uu___is_Warning_WarnOnUse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_WarnOnUse -> true | uu____2069 -> false
let (uu___is_Warning_DeprecatedAttributeSyntax : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedAttributeSyntax -> true
    | uu____2075 -> false
let (uu___is_Warning_DeprecatedGeneric : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedGeneric -> true
    | uu____2081 -> false
let (uu___is_Error_BadSplice : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadSplice -> true | uu____2087 -> false
type flag = error_flag
type error_setting = (raw_error * error_flag * Prims.int)
let (default_settings : error_setting Prims.list) =
  [(Error_DependencyAnalysisFailed, CAlwaysError, Prims.int_zero);
  (Error_IDETooManyPops, CAlwaysError, Prims.int_one);
  (Error_IDEUnrecognized, CAlwaysError, (Prims.of_int (2)));
  (Error_InductiveTypeNotSatisfyPositivityCondition, CAlwaysError,
    (Prims.of_int (3)));
  (Error_InvalidUniverseVar, CAlwaysError, (Prims.of_int (4)));
  (Error_MissingFileName, CAlwaysError, (Prims.of_int (5)));
  (Error_ModuleFileNameMismatch, CAlwaysError, (Prims.of_int (6)));
  (Error_OpPlusInUniverse, CAlwaysError, (Prims.of_int (7)));
  (Error_OutOfRange, CAlwaysError, (Prims.of_int (8)));
  (Error_ProofObligationFailed, CError, (Prims.of_int (9)));
  (Error_TooManyFiles, CAlwaysError, (Prims.of_int (10)));
  (Error_TypeCheckerFailToProve, CAlwaysError, (Prims.of_int (11)));
  (Error_TypeError, CAlwaysError, (Prims.of_int (12)));
  (Error_UncontrainedUnificationVar, CAlwaysError, (Prims.of_int (13)));
  (Error_UnexpectedGTotComputation, CAlwaysError, (Prims.of_int (14)));
  (Error_UnexpectedInstance, CAlwaysError, (Prims.of_int (15)));
  (Error_UnknownFatal_AssertionFailure, CError, (Prims.of_int (16)));
  (Error_Z3InvocationError, CAlwaysError, (Prims.of_int (17)));
  (Error_IDEAssertionFailure, CAlwaysError, (Prims.of_int (18)));
  (Error_Z3SolverError, CError, (Prims.of_int (19)));
  (Fatal_AbstractTypeDeclarationInInterface, CFatal, (Prims.of_int (20)));
  (Fatal_ActionMustHaveFunctionType, CFatal, (Prims.of_int (21)));
  (Fatal_AlreadyDefinedTopLevelDeclaration, CFatal, (Prims.of_int (22)));
  (Fatal_ArgumentLengthMismatch, CFatal, (Prims.of_int (23)));
  (Fatal_AssertionFailure, CFatal, (Prims.of_int (24)));
  (Fatal_AssignToImmutableValues, CFatal, (Prims.of_int (25)));
  (Fatal_AssumeValInInterface, CFatal, (Prims.of_int (26)));
  (Fatal_BadlyInstantiatedSynthByTactic, CFatal, (Prims.of_int (27)));
  (Fatal_BadSignatureShape, CFatal, (Prims.of_int (28)));
  (Fatal_BinderAndArgsLengthMismatch, CFatal, (Prims.of_int (29)));
  (Fatal_BothValAndLetInInterface, CFatal, (Prims.of_int (30)));
  (Fatal_CardinalityConstraintViolated, CFatal, (Prims.of_int (31)));
  (Fatal_ComputationNotTotal, CFatal, (Prims.of_int (32)));
  (Fatal_ComputationTypeNotAllowed, CFatal, (Prims.of_int (33)));
  (Fatal_ComputedTypeNotMatchAnnotation, CFatal, (Prims.of_int (34)));
  (Fatal_ConstructorArgLengthMismatch, CFatal, (Prims.of_int (35)));
  (Fatal_ConstructorFailedCheck, CFatal, (Prims.of_int (36)));
  (Fatal_ConstructorNotFound, CFatal, (Prims.of_int (37)));
  (Fatal_ConstsructorBuildWrongType, CFatal, (Prims.of_int (38)));
  (Fatal_CycleInRecTypeAbbreviation, CFatal, (Prims.of_int (39)));
  (Fatal_DataContructorNotFound, CFatal, (Prims.of_int (40)));
  (Fatal_DefaultQualifierNotAllowedOnEffects, CFatal, (Prims.of_int (41)));
  (Fatal_DefinitionNotFound, CFatal, (Prims.of_int (42)));
  (Fatal_DisjuctivePatternVarsMismatch, CFatal, (Prims.of_int (43)));
  (Fatal_DivergentComputationCannotBeIncludedInTotal, CFatal,
    (Prims.of_int (44)));
  (Fatal_DuplicateInImplementation, CFatal, (Prims.of_int (45)));
  (Fatal_DuplicateModuleOrInterface, CFatal, (Prims.of_int (46)));
  (Fatal_DuplicateTopLevelNames, CFatal, (Prims.of_int (47)));
  (Fatal_DuplicateTypeAnnotationAndValDecl, CFatal, (Prims.of_int (48)));
  (Fatal_EffectCannotBeReified, CFatal, (Prims.of_int (49)));
  (Fatal_EffectConstructorNotFullyApplied, CFatal, (Prims.of_int (50)));
  (Fatal_EffectfulAndPureComputationMismatch, CFatal, (Prims.of_int (51)));
  (Fatal_EffectNotFound, CFatal, (Prims.of_int (52)));
  (Fatal_EffectsCannotBeComposed, CFatal, (Prims.of_int (53)));
  (Fatal_ErrorInSolveDeferredConstraints, CFatal, (Prims.of_int (54)));
  (Fatal_ErrorsReported, CFatal, (Prims.of_int (55)));
  (Fatal_EscapedBoundVar, CFatal, (Prims.of_int (56)));
  (Fatal_ExpectedArrowAnnotatedType, CFatal, (Prims.of_int (57)));
  (Fatal_ExpectedGhostExpression, CFatal, (Prims.of_int (58)));
  (Fatal_ExpectedPureExpression, CFatal, (Prims.of_int (59)));
  (Fatal_ExpectNormalizedEffect, CFatal, (Prims.of_int (60)));
  (Fatal_ExpectTermGotFunction, CFatal, (Prims.of_int (61)));
  (Fatal_ExpectTrivialPreCondition, CFatal, (Prims.of_int (62)));
  (Fatal_FailToExtractNativeTactic, CFatal, (Prims.of_int (63)));
  (Fatal_FailToCompileNativeTactic, CFatal, (Prims.of_int (64)));
  (Fatal_FailToProcessPragma, CFatal, (Prims.of_int (65)));
  (Fatal_FailToResolveImplicitArgument, CFatal, (Prims.of_int (66)));
  (Fatal_FailToSolveUniverseInEquality, CFatal, (Prims.of_int (67)));
  (Fatal_FieldsNotBelongToSameRecordType, CFatal, (Prims.of_int (68)));
  (Fatal_ForbiddenReferenceToCurrentModule, CFatal, (Prims.of_int (69)));
  (Fatal_FreeVariables, CFatal, (Prims.of_int (70)));
  (Fatal_FunctionTypeExpected, CFatal, (Prims.of_int (71)));
  (Fatal_IdentifierNotFound, CFatal, (Prims.of_int (72)));
  (Fatal_IllAppliedConstant, CFatal, (Prims.of_int (73)));
  (Fatal_IllegalCharInByteArray, CFatal, (Prims.of_int (74)));
  (Fatal_IllegalCharInOperatorName, CFatal, (Prims.of_int (75)));
  (Fatal_IllTyped, CFatal, (Prims.of_int (76)));
  (Fatal_ImpossibleAbbrevLidBundle, CFatal, (Prims.of_int (77)));
  (Fatal_ImpossibleAbbrevRenameBundle, CFatal, (Prims.of_int (78)));
  (Fatal_ImpossibleInductiveWithAbbrev, CFatal, (Prims.of_int (79)));
  (Fatal_ImpossiblePrePostAbs, CFatal, (Prims.of_int (80)));
  (Fatal_ImpossiblePrePostArrow, CFatal, (Prims.of_int (81)));
  (Fatal_ImpossibleToGenerateDMEffect, CFatal, (Prims.of_int (82)));
  (Fatal_ImpossibleTypeAbbrevBundle, CFatal, (Prims.of_int (83)));
  (Fatal_ImpossibleTypeAbbrevSigeltBundle, CFatal, (Prims.of_int (84)));
  (Fatal_IncludeModuleNotPrepared, CFatal, (Prims.of_int (85)));
  (Fatal_IncoherentInlineUniverse, CFatal, (Prims.of_int (86)));
  (Fatal_IncompatibleKinds, CFatal, (Prims.of_int (87)));
  (Fatal_IncompatibleNumberOfTypes, CFatal, (Prims.of_int (88)));
  (Fatal_IncompatibleSetOfUniverse, CFatal, (Prims.of_int (89)));
  (Fatal_IncompatibleUniverse, CFatal, (Prims.of_int (90)));
  (Fatal_InconsistentImplicitArgumentAnnotation, CFatal, (Prims.of_int (91)));
  (Fatal_InconsistentImplicitQualifier, CFatal, (Prims.of_int (92)));
  (Fatal_InconsistentQualifierAnnotation, CFatal, (Prims.of_int (93)));
  (Fatal_InferredTypeCauseVarEscape, CFatal, (Prims.of_int (94)));
  (Fatal_InlineRenamedAsUnfold, CFatal, (Prims.of_int (95)));
  (Fatal_InsufficientPatternArguments, CFatal, (Prims.of_int (96)));
  (Fatal_InterfaceAlreadyProcessed, CFatal, (Prims.of_int (97)));
  (Fatal_InterfaceNotImplementedByModule, CFatal, (Prims.of_int (98)));
  (Fatal_InterfaceWithTypeImplementation, CFatal, (Prims.of_int (99)));
  (Fatal_InvalidFloatingPointNumber, CFatal, (Prims.of_int (100)));
  (Fatal_InvalidFSDocKeyword, CFatal, (Prims.of_int (101)));
  (Fatal_InvalidIdentifier, CFatal, (Prims.of_int (102)));
  (Fatal_InvalidLemmaArgument, CFatal, (Prims.of_int (103)));
  (Fatal_InvalidNumericLiteral, CFatal, (Prims.of_int (104)));
  (Fatal_InvalidRedefinitionOfLexT, CFatal, (Prims.of_int (105)));
  (Fatal_InvalidUnicodeInStringLiteral, CFatal, (Prims.of_int (106)));
  (Fatal_InvalidUTF8Encoding, CFatal, (Prims.of_int (107)));
  (Fatal_InvalidWarnErrorSetting, CFatal, (Prims.of_int (108)));
  (Fatal_LetBoundMonadicMismatch, CFatal, (Prims.of_int (109)));
  (Fatal_LetMutableForVariablesOnly, CFatal, (Prims.of_int (110)));
  (Fatal_LetOpenModuleOnly, CFatal, (Prims.of_int (111)));
  (Fatal_LetRecArgumentMismatch, CFatal, (Prims.of_int (112)));
  (Fatal_MalformedActionDeclaration, CFatal, (Prims.of_int (113)));
  (Fatal_MismatchedPatternType, CFatal, (Prims.of_int (114)));
  (Fatal_MismatchUniversePolymorphic, CFatal, (Prims.of_int (115)));
  (Fatal_MissingDataConstructor, CFatal, (Prims.of_int (116)));
  (Fatal_MissingExposeInterfacesOption, CFatal, (Prims.of_int (117)));
  (Fatal_MissingFieldInRecord, CFatal, (Prims.of_int (118)));
  (Fatal_MissingImplementation, CFatal, (Prims.of_int (119)));
  (Fatal_MissingImplicitArguments, CFatal, (Prims.of_int (120)));
  (Fatal_MissingInterface, CFatal, (Prims.of_int (121)));
  (Fatal_MissingNameInBinder, CFatal, (Prims.of_int (122)));
  (Fatal_MissingPrimsModule, CFatal, (Prims.of_int (123)));
  (Fatal_MissingQuantifierBinder, CFatal, (Prims.of_int (124)));
  (Fatal_ModuleExpected, CFatal, (Prims.of_int (125)));
  (Fatal_ModuleFileNotFound, CFatal, (Prims.of_int (126)));
  (Fatal_ModuleFirstStatement, CFatal, (Prims.of_int (127)));
  (Fatal_ModuleNotFound, CFatal, (Prims.of_int (128)));
  (Fatal_ModuleOrFileNotFound, CFatal, (Prims.of_int (129)));
  (Fatal_MonadAlreadyDefined, CFatal, (Prims.of_int (130)));
  (Fatal_MoreThanOneDeclaration, CFatal, (Prims.of_int (131)));
  (Fatal_MultipleLetBinding, CFatal, (Prims.of_int (132)));
  (Fatal_NameNotFound, CFatal, (Prims.of_int (133)));
  (Fatal_NameSpaceNotFound, CFatal, (Prims.of_int (134)));
  (Fatal_NegativeUniverseConstFatal_NotSupported, CFatal,
    (Prims.of_int (135)));
  (Fatal_NoFileProvided, CFatal, (Prims.of_int (136)));
  (Fatal_NonInductiveInMutuallyDefinedType, CFatal, (Prims.of_int (137)));
  (Fatal_NonLinearPatternNotPermitted, CFatal, (Prims.of_int (138)));
  (Fatal_NonLinearPatternVars, CFatal, (Prims.of_int (139)));
  (Fatal_NonSingletonTopLevel, CFatal, (Prims.of_int (140)));
  (Fatal_NonSingletonTopLevelModule, CFatal, (Prims.of_int (141)));
  (Error_NonTopRecFunctionNotFullyEncoded, CError, (Prims.of_int (142)));
  (Fatal_NonTrivialPreConditionInPrims, CFatal, (Prims.of_int (143)));
  (Fatal_NonVariableInductiveTypeParameter, CFatal, (Prims.of_int (144)));
  (Fatal_NotApplicationOrFv, CFatal, (Prims.of_int (145)));
  (Fatal_NotEnoughArgsToEffect, CFatal, (Prims.of_int (146)));
  (Fatal_NotEnoughArgumentsForEffect, CFatal, (Prims.of_int (147)));
  (Fatal_NotFunctionType, CFatal, (Prims.of_int (148)));
  (Fatal_NotSupported, CFatal, (Prims.of_int (149)));
  (Fatal_NotTopLevelModule, CFatal, (Prims.of_int (150)));
  (Fatal_NotValidFStarFile, CFatal, (Prims.of_int (151)));
  (Fatal_NotValidIncludeDirectory, CFatal, (Prims.of_int (152)));
  (Fatal_OneModulePerFile, CFatal, (Prims.of_int (153)));
  (Fatal_OpenGoalsInSynthesis, CFatal, (Prims.of_int (154)));
  (Fatal_OptionsNotCompatible, CFatal, (Prims.of_int (155)));
  (Fatal_OutOfOrder, CFatal, (Prims.of_int (156)));
  (Fatal_ParseErrors, CFatal, (Prims.of_int (157)));
  (Fatal_ParseItError, CFatal, (Prims.of_int (158)));
  (Fatal_PolyTypeExpected, CFatal, (Prims.of_int (159)));
  (Fatal_PossibleInfiniteTyp, CFatal, (Prims.of_int (160)));
  (Fatal_PreModuleMismatch, CFatal, (Prims.of_int (161)));
  (Fatal_QulifierListNotPermitted, CFatal, (Prims.of_int (162)));
  (Fatal_RecursiveFunctionLiteral, CFatal, (Prims.of_int (163)));
  (Fatal_ReflectOnlySupportedOnEffects, CFatal, (Prims.of_int (164)));
  (Fatal_ReservedPrefix, CFatal, (Prims.of_int (165)));
  (Fatal_SMTOutputParseError, CFatal, (Prims.of_int (166)));
  (Fatal_SMTSolverError, CFatal, (Prims.of_int (167)));
  (Fatal_SyntaxError, CFatal, (Prims.of_int (168)));
  (Fatal_SynthByTacticError, CFatal, (Prims.of_int (169)));
  (Fatal_TacticGotStuck, CFatal, (Prims.of_int (170)));
  (Fatal_TcOneFragmentFailed, CFatal, (Prims.of_int (171)));
  (Fatal_TermOutsideOfDefLanguage, CFatal, (Prims.of_int (172)));
  (Fatal_ToManyArgumentToFunction, CFatal, (Prims.of_int (173)));
  (Fatal_TooManyOrTooFewFileMatch, CFatal, (Prims.of_int (174)));
  (Fatal_TooManyPatternArguments, CFatal, (Prims.of_int (175)));
  (Fatal_TooManyUniverse, CFatal, (Prims.of_int (176)));
  (Fatal_TypeMismatch, CFatal, (Prims.of_int (177)));
  (Fatal_TypeWithinPatternsAllowedOnVariablesOnly, CFatal,
    (Prims.of_int (178)));
  (Fatal_UnableToReadFile, CFatal, (Prims.of_int (179)));
  (Fatal_UnepxectedOrUnboundOperator, CFatal, (Prims.of_int (180)));
  (Fatal_UnexpectedBinder, CFatal, (Prims.of_int (181)));
  (Fatal_UnexpectedBindShape, CFatal, (Prims.of_int (182)));
  (Fatal_UnexpectedChar, CFatal, (Prims.of_int (183)));
  (Fatal_UnexpectedComputationTypeForLetRec, CFatal, (Prims.of_int (184)));
  (Fatal_UnexpectedConstructorType, CFatal, (Prims.of_int (185)));
  (Fatal_UnexpectedDataConstructor, CFatal, (Prims.of_int (186)));
  (Fatal_UnexpectedEffect, CFatal, (Prims.of_int (187)));
  (Fatal_UnexpectedEmptyRecord, CFatal, (Prims.of_int (188)));
  (Fatal_UnexpectedExpressionType, CFatal, (Prims.of_int (189)));
  (Fatal_UnexpectedFunctionParameterType, CFatal, (Prims.of_int (190)));
  (Fatal_UnexpectedGeneralizedUniverse, CFatal, (Prims.of_int (191)));
  (Fatal_UnexpectedGTotForLetRec, CFatal, (Prims.of_int (192)));
  (Fatal_UnexpectedGuard, CFatal, (Prims.of_int (193)));
  (Fatal_UnexpectedIdentifier, CFatal, (Prims.of_int (194)));
  (Fatal_UnexpectedImplicitArgument, CFatal, (Prims.of_int (195)));
  (Fatal_UnexpectedImplictArgument, CFatal, (Prims.of_int (196)));
  (Fatal_UnexpectedInductivetype, CFatal, (Prims.of_int (197)));
  (Fatal_UnexpectedLetBinding, CFatal, (Prims.of_int (198)));
  (Fatal_UnexpectedModuleDeclaration, CFatal, (Prims.of_int (199)));
  (Fatal_UnexpectedNumberOfUniverse, CFatal, (Prims.of_int (200)));
  (Fatal_UnexpectedNumericLiteral, CFatal, (Prims.of_int (201)));
  (Fatal_UnexpectedOperatorSymbol, CFatal, (Prims.of_int (202)));
  (Fatal_UnexpectedPattern, CFatal, (Prims.of_int (203)));
  (Fatal_UnexpectedPosition, CFatal, (Prims.of_int (204)));
  (Fatal_UnExpectedPreCondition, CFatal, (Prims.of_int (205)));
  (Fatal_UnexpectedReturnShape, CFatal, (Prims.of_int (206)));
  (Fatal_UnexpectedSignatureForMonad, CFatal, (Prims.of_int (207)));
  (Fatal_UnexpectedTerm, CFatal, (Prims.of_int (208)));
  (Fatal_UnexpectedTermInUniverse, CFatal, (Prims.of_int (209)));
  (Fatal_UnexpectedTermType, CFatal, (Prims.of_int (210)));
  (Fatal_UnexpectedTermVQuote, CFatal, (Prims.of_int (211)));
  (Fatal_UnexpectedUniversePolymorphicReturn, CFatal, (Prims.of_int (212)));
  (Fatal_UnexpectedUniverseVariable, CFatal, (Prims.of_int (213)));
  (Fatal_UnfoldableDeprecated, CFatal, (Prims.of_int (214)));
  (Fatal_UnificationNotWellFormed, CFatal, (Prims.of_int (215)));
  (Fatal_Uninstantiated, CFatal, (Prims.of_int (216)));
  (Error_UninstantiatedUnificationVarInTactic, CError, (Prims.of_int (217)));
  (Fatal_UninstantiatedVarInTactic, CFatal, (Prims.of_int (218)));
  (Fatal_UniverseMightContainSumOfTwoUnivVars, CFatal, (Prims.of_int (219)));
  (Fatal_UniversePolymorphicInnerLetBound, CFatal, (Prims.of_int (220)));
  (Fatal_UnknownAttribute, CFatal, (Prims.of_int (221)));
  (Fatal_UnknownToolForDep, CFatal, (Prims.of_int (222)));
  (Fatal_UnrecognizedExtension, CFatal, (Prims.of_int (223)));
  (Fatal_UnresolvedPatternVar, CFatal, (Prims.of_int (224)));
  (Fatal_UnsupportedConstant, CFatal, (Prims.of_int (225)));
  (Fatal_UnsupportedDisjuctivePatterns, CFatal, (Prims.of_int (226)));
  (Fatal_UnsupportedQualifier, CFatal, (Prims.of_int (227)));
  (Fatal_UserTacticFailure, CFatal, (Prims.of_int (228)));
  (Fatal_ValueRestriction, CFatal, (Prims.of_int (229)));
  (Fatal_VariableNotFound, CFatal, (Prims.of_int (230)));
  (Fatal_WrongBodyTypeForReturnWP, CFatal, (Prims.of_int (231)));
  (Fatal_WrongDataAppHeadFormat, CFatal, (Prims.of_int (232)));
  (Fatal_WrongDefinitionOrder, CFatal, (Prims.of_int (233)));
  (Fatal_WrongResultTypeAfterConstrutor, CFatal, (Prims.of_int (234)));
  (Fatal_WrongTerm, CFatal, (Prims.of_int (235)));
  (Fatal_WhenClauseNotSupported, CFatal, (Prims.of_int (236)));
  (Unused01, CFatal, (Prims.of_int (237)));
  (Warning_PluginNotImplemented, CError, (Prims.of_int (238)));
  (Warning_AddImplicitAssumeNewQualifier, CWarning, (Prims.of_int (239)));
  (Warning_AdmitWithoutDefinition, CWarning, (Prims.of_int (240)));
  (Warning_CachedFile, CWarning, (Prims.of_int (241)));
  (Warning_DefinitionNotTranslated, CWarning, (Prims.of_int (242)));
  (Warning_DependencyFound, CWarning, (Prims.of_int (243)));
  (Warning_DeprecatedEqualityOnBinder, CWarning, (Prims.of_int (244)));
  (Warning_DeprecatedOpaqueQualifier, CWarning, (Prims.of_int (245)));
  (Warning_DocOverwrite, CWarning, (Prims.of_int (246)));
  (Warning_FileNotWritten, CWarning, (Prims.of_int (247)));
  (Warning_Filtered, CWarning, (Prims.of_int (248)));
  (Warning_FunctionLiteralPrecisionLoss, CWarning, (Prims.of_int (249)));
  (Warning_FunctionNotExtacted, CWarning, (Prims.of_int (250)));
  (Warning_HintFailedToReplayProof, CWarning, (Prims.of_int (251)));
  (Warning_HitReplayFailed, CWarning, (Prims.of_int (252)));
  (Warning_IDEIgnoreCodeGen, CWarning, (Prims.of_int (253)));
  (Warning_IllFormedGoal, CWarning, (Prims.of_int (254)));
  (Warning_InaccessibleArgument, CWarning, (Prims.of_int (255)));
  (Warning_IncoherentImplicitQualifier, CWarning, (Prims.of_int (256)));
  (Warning_IrrelevantQualifierOnArgumentToReflect, CWarning,
    (Prims.of_int (257)));
  (Warning_IrrelevantQualifierOnArgumentToReify, CWarning,
    (Prims.of_int (258)));
  (Warning_MalformedWarnErrorList, CWarning, (Prims.of_int (259)));
  (Warning_MetaAlienNotATmUnknown, CWarning, (Prims.of_int (260)));
  (Warning_MultipleAscriptions, CWarning, (Prims.of_int (261)));
  (Warning_NondependentUserDefinedDataType, CWarning, (Prims.of_int (262)));
  (Warning_NonListLiteralSMTPattern, CWarning, (Prims.of_int (263)));
  (Warning_NormalizationFailure, CWarning, (Prims.of_int (264)));
  (Warning_NotDependentArrow, CWarning, (Prims.of_int (265)));
  (Warning_NotEmbedded, CWarning, (Prims.of_int (266)));
  (Warning_PatternMissingBoundVar, CWarning, (Prims.of_int (267)));
  (Warning_RecursiveDependency, CWarning, (Prims.of_int (268)));
  (Warning_RedundantExplicitCurrying, CWarning, (Prims.of_int (269)));
  (Warning_SMTPatTDeprecated, CWarning, (Prims.of_int (270)));
  (Warning_SMTPatternIllFormed, CWarning, (Prims.of_int (271)));
  (Warning_TopLevelEffect, CWarning, (Prims.of_int (272)));
  (Warning_UnboundModuleReference, CWarning, (Prims.of_int (273)));
  (Warning_UnexpectedFile, CWarning, (Prims.of_int (274)));
  (Warning_UnexpectedFsTypApp, CWarning, (Prims.of_int (275)));
  (Warning_UnexpectedZ3Output, CError, (Prims.of_int (276)));
  (Warning_UnprotectedTerm, CWarning, (Prims.of_int (277)));
  (Warning_UnrecognizedAttribute, CWarning, (Prims.of_int (278)));
  (Warning_UpperBoundCandidateAlreadyVisited, CWarning, (Prims.of_int (279)));
  (Warning_UseDefaultEffect, CWarning, (Prims.of_int (280)));
  (Warning_WrongErrorLocation, CWarning, (Prims.of_int (281)));
  (Warning_Z3InvocationWarning, CWarning, (Prims.of_int (282)));
  (Warning_MissingInterfaceOrImplementation, CWarning, (Prims.of_int (283)));
  (Warning_ConstructorBuildsUnexpectedType, CWarning, (Prims.of_int (284)));
  (Warning_ModuleOrFileNotFoundWarning, CWarning, (Prims.of_int (285)));
  (Error_NoLetMutable, CAlwaysError, (Prims.of_int (286)));
  (Error_BadImplicit, CAlwaysError, (Prims.of_int (287)));
  (Warning_DeprecatedDefinition, CWarning, (Prims.of_int (288)));
  (Fatal_SMTEncodingArityMismatch, CFatal, (Prims.of_int (289)));
  (Warning_Defensive, CWarning, (Prims.of_int (290)));
  (Warning_CantInspect, CWarning, (Prims.of_int (291)));
  (Warning_NilGivenExplicitArgs, CWarning, (Prims.of_int (292)));
  (Warning_ConsAppliedExplicitArgs, CWarning, (Prims.of_int (293)));
  (Warning_UnembedBinderKnot, CWarning, (Prims.of_int (294)));
  (Fatal_TacticProofRelevantGoal, CFatal, (Prims.of_int (295)));
  (Warning_TacAdmit, CWarning, (Prims.of_int (296)));
  (Fatal_IncoherentPatterns, CFatal, (Prims.of_int (297)));
  (Error_NoSMTButNeeded, CAlwaysError, (Prims.of_int (298)));
  (Fatal_UnexpectedAntiquotation, CFatal, (Prims.of_int (299)));
  (Fatal_SplicedUndef, CFatal, (Prims.of_int (300)));
  (Fatal_SpliceUnembedFail, CFatal, (Prims.of_int (301)));
  (Warning_ExtractionUnexpectedEffect, CWarning, (Prims.of_int (302)));
  (Error_DidNotFail, CAlwaysError, (Prims.of_int (303)));
  (Warning_UnappliedFail, CWarning, (Prims.of_int (304)));
  (Warning_QuantifierWithoutPattern, CSilent, (Prims.of_int (305)));
  (Error_EmptyFailErrs, CAlwaysError, (Prims.of_int (306)));
  (Warning_logicqualifier, CWarning, (Prims.of_int (307)));
  (Fatal_CyclicDependence, CFatal, (Prims.of_int (308)));
  (Error_InductiveAnnotNotAType, CError, (Prims.of_int (309)));
  (Fatal_FriendInterface, CFatal, (Prims.of_int (310)));
  (Error_CannotRedefineConst, CError, (Prims.of_int (311)));
  (Error_BadClassDecl, CError, (Prims.of_int (312)));
  (Error_BadInductiveParam, CFatal, (Prims.of_int (313)));
  (Error_FieldShadow, CFatal, (Prims.of_int (314)));
  (Error_UnexpectedDM4FType, CFatal, (Prims.of_int (315)));
  (Fatal_EffectAbbreviationResultTypeMismatch, CFatal, (Prims.of_int (316)));
  (Error_AlreadyCachedAssertionFailure, CFatal, (Prims.of_int (317)));
  (Error_MustEraseMissing, CWarning, (Prims.of_int (318)));
  (Warning_EffectfulArgumentToErasedFunction, CWarning, (Prims.of_int (319)));
  (Fatal_EmptySurfaceLet, CFatal, (Prims.of_int (320)));
  (Warning_UnexpectedCheckedFile, CWarning, (Prims.of_int (321)));
  (Fatal_ExtractionUnsupported, CFatal, (Prims.of_int (322)));
  (Warning_SMTErrorReason, CWarning, (Prims.of_int (323)));
  (Warning_CoercionNotFound, CWarning, (Prims.of_int (324)));
  (Error_QuakeFailed, CError, (Prims.of_int (325)));
  (Error_IllSMTPat, CError, (Prims.of_int (326)));
  (Error_IllScopedTerm, CError, (Prims.of_int (327)));
  (Warning_UnusedLetRec, CWarning, (Prims.of_int (328)));
  (Fatal_Effects_Ordering_Coherence, CError, (Prims.of_int (329)));
  (Warning_BleedingEdge_Feature, CWarning, (Prims.of_int (330)));
  (Warning_IgnoredBinding, CWarning, (Prims.of_int (331)));
  (Warning_CouldNotReadHints, CWarning, (Prims.of_int (333)));
  (Fatal_BadUvar, CFatal, (Prims.of_int (334)));
  (Warning_WarnOnUse, CSilent, (Prims.of_int (335)));
  (Warning_DeprecatedAttributeSyntax, CSilent, (Prims.of_int (336)));
  (Warning_DeprecatedGeneric, CWarning, (Prims.of_int (337)));
  (Error_BadSplice, CError, (Prims.of_int (338)))]
let lookup_error :
  'uuuuuu2106 'uuuuuu2107 'uuuuuu2108 .
    ('uuuuuu2106 * 'uuuuuu2107 * 'uuuuuu2108) Prims.list ->
      'uuuuuu2106 -> ('uuuuuu2106 * 'uuuuuu2107 * 'uuuuuu2108)
  =
  fun settings ->
    fun e ->
      let uu____2141 =
        FStar_Util.try_find
          (fun uu____2160 ->
             match uu____2160 with | (v, uu____2168, i) -> e = v) settings in
      match uu____2141 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          failwith "Impossible: unrecognized error"
let lookup_error_range :
  'uuuuuu2209 'uuuuuu2210 .
    ('uuuuuu2209 * 'uuuuuu2210 * Prims.int) Prims.list ->
      (Prims.int * Prims.int) ->
        ('uuuuuu2209 * 'uuuuuu2210 * Prims.int) Prims.list
  =
  fun settings ->
    fun uu____2240 ->
      match uu____2240 with
      | (l, h) ->
          let uu____2255 =
            FStar_List.partition
              (fun uu____2286 ->
                 match uu____2286 with
                 | (uu____2293, uu____2294, i) -> (l <= i) && (i <= h))
              settings in
          (match uu____2255 with | (matches, uu____2305) -> matches)
let error_number :
  'uuuuuu2346 'uuuuuu2347 'uuuuuu2348 .
    ('uuuuuu2346 * 'uuuuuu2347 * 'uuuuuu2348) -> 'uuuuuu2348
  =
  fun uu____2359 -> match uu____2359 with | (uu____2366, uu____2367, i) -> i
let (warn_on_use_errno : Prims.int) =
  let uu____2369 = lookup_error default_settings Warning_WarnOnUse in
  error_number uu____2369
let (defensive_errno : Prims.int) =
  let uu____2376 = lookup_error default_settings Warning_Defensive in
  error_number uu____2376
let (update_flags :
  (error_flag * Prims.string) Prims.list -> error_setting Prims.list) =
  fun l ->
    let set_one_flag i flag1 default_flag =
      match (flag1, default_flag) with
      | (CWarning, CAlwaysError) ->
          let uu____2420 =
            let uu____2421 =
              let uu____2422 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2422 in
            Invalid_warn_error_setting uu____2421 in
          FStar_Exn.raise uu____2420
      | (CError, CAlwaysError) ->
          let uu____2423 =
            let uu____2424 =
              let uu____2425 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2425 in
            Invalid_warn_error_setting uu____2424 in
          FStar_Exn.raise uu____2423
      | (CSilent, CAlwaysError) ->
          let uu____2426 =
            let uu____2427 =
              let uu____2428 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot silence error %s" uu____2428 in
            Invalid_warn_error_setting uu____2427 in
          FStar_Exn.raise uu____2426
      | (uu____2429, CFatal) ->
          let uu____2430 =
            let uu____2431 =
              let uu____2432 = FStar_Util.string_of_int i in
              FStar_Util.format1
                "cannot change the error level of fatal error %s" uu____2432 in
            Invalid_warn_error_setting uu____2431 in
          FStar_Exn.raise uu____2430
      | uu____2433 -> flag1 in
    let set_flag_for_range uu____2459 =
      match uu____2459 with
      | (flag1, range) ->
          let errs = lookup_error_range default_settings range in
          FStar_List.map
            (fun uu____2512 ->
               match uu____2512 with
               | (v, default_flag, i) ->
                   let uu____2528 = set_one_flag i flag1 default_flag in
                   (v, uu____2528, i)) errs in
    let compute_range uu____2546 =
      match uu____2546 with
      | (flag1, s) ->
          let r = FStar_Util.split s ".." in
          let uu____2564 =
            match r with
            | r1::r2::[] ->
                let uu____2575 = FStar_Util.int_of_string r1 in
                let uu____2576 = FStar_Util.int_of_string r2 in
                (uu____2575, uu____2576)
            | uu____2577 ->
                let uu____2580 =
                  let uu____2581 =
                    FStar_Util.format1 "Malformed warn-error range %s" s in
                  Invalid_warn_error_setting uu____2581 in
                FStar_Exn.raise uu____2580 in
          (match uu____2564 with | (l1, h) -> (flag1, (l1, h))) in
    let error_range_settings = FStar_List.map compute_range l in
    let uu____2623 =
      FStar_List.collect set_flag_for_range error_range_settings in
    FStar_List.append uu____2623 default_settings
type error =
  (raw_error * Prims.string * FStar_Range.range * Prims.string Prims.list)
exception Err of (raw_error * Prims.string * Prims.string Prims.list) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Err uu____2679 -> true | uu____2688 -> false
let (__proj__Err__item__uu___ :
  Prims.exn -> (raw_error * Prims.string * Prims.string Prims.list)) =
  fun projectee -> match projectee with | Err uu____2710 -> uu____2710
exception Error of error 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Error uu____2728 -> true | uu____2729 -> false
let (__proj__Error__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Error uu____2735 -> uu____2735
exception Warning of error 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning uu____2745 -> true | uu____2746 -> false
let (__proj__Warning__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Warning uu____2752 -> uu____2752
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Stop -> true | uu____2758 -> false
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Empty_frag -> true | uu____2764 -> false
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | ENotImplemented -> true | uu____2770 -> false
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EInfo -> true | uu____2776 -> false
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EWarning -> true | uu____2782 -> false
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EError -> true | uu____2788 -> false
type issue =
  {
  issue_msg: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option ;
  issue_number: Prims.int FStar_Pervasives_Native.option ;
  issue_ctx: Prims.string Prims.list }
let (__proj__Mkissue__item__issue_msg : issue -> Prims.string) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_msg
let (__proj__Mkissue__item__issue_level : issue -> issue_level) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_level1
let (__proj__Mkissue__item__issue_range :
  issue -> FStar_Range.range FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_range
let (__proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_number
let (__proj__Mkissue__item__issue_ctx : issue -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_ctx
type error_handler =
  {
  eh_add_one: issue -> unit ;
  eh_count_errors: unit -> Prims.int ;
  eh_report: unit -> issue Prims.list ;
  eh_clear: unit -> unit }
let (__proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> unit) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_add_one
let (__proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> unit -> Prims.int) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_count_errors
let (__proj__Mkerror_handler__item__eh_report :
  error_handler -> unit -> issue Prims.list) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_report
let (__proj__Mkerror_handler__item__eh_clear : error_handler -> unit -> unit)
  =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_clear
let (issue_message : issue -> Prims.string) =
  fun i ->
    let ctx_string =
      let uu____3084 =
        FStar_All.pipe_right i.issue_ctx
          (FStar_List.map (fun s -> FStar_String.op_Hat "\n> " s)) in
      FStar_All.pipe_right uu____3084 (FStar_String.concat "") in
    FStar_String.op_Hat i.issue_msg ctx_string
let (format_issue : issue -> Prims.string) =
  fun issue1 ->
    let level_header =
      match issue1.issue_level with
      | EInfo -> "Info"
      | EWarning -> "Warning"
      | EError -> "Error"
      | ENotImplemented -> "Feature not yet implemented: " in
    let uu____3101 =
      match issue1.issue_range with
      | FStar_Pervasives_Native.None -> ("", "")
      | FStar_Pervasives_Native.Some r when r = FStar_Range.dummyRange ->
          let uu____3111 =
            let uu____3112 =
              let uu____3113 = FStar_Range.def_range r in
              let uu____3114 = FStar_Range.def_range FStar_Range.dummyRange in
              uu____3113 = uu____3114 in
            if uu____3112
            then ""
            else
              (let uu____3116 = FStar_Range.string_of_range r in
               FStar_Util.format1 "\n  (see also %s)" uu____3116) in
          ("", uu____3111)
      | FStar_Pervasives_Native.Some r ->
          let uu____3118 =
            let uu____3119 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____3119 in
          let uu____3120 =
            let uu____3121 =
              (let uu____3126 = FStar_Range.use_range r in
               let uu____3127 = FStar_Range.def_range r in
               uu____3126 = uu____3127) ||
                (let uu____3130 = FStar_Range.def_range r in
                 let uu____3131 =
                   FStar_Range.def_range FStar_Range.dummyRange in
                 uu____3130 = uu____3131) in
            if uu____3121
            then ""
            else
              (let uu____3133 = FStar_Range.string_of_range r in
               FStar_Util.format1 "\n  (see also %s)" uu____3133) in
          (uu____3118, uu____3120) in
    match uu____3101 with
    | (range_str, see_also_str) ->
        let issue_number =
          match issue1.issue_number with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some n ->
              let uu____3138 = FStar_Util.string_of_int n in
              FStar_Util.format1 " %s" uu____3138 in
        let uu____3139 = issue_message issue1 in
        FStar_Util.format5 "%s(%s%s) %s%s" range_str level_header
          issue_number uu____3139 see_also_str
let (print_issue : issue -> unit) =
  fun issue1 ->
    let printer =
      match issue1.issue_level with
      | EInfo -> FStar_Util.print_string
      | EWarning -> FStar_Util.print_warning
      | EError -> FStar_Util.print_error
      | ENotImplemented -> FStar_Util.print_error in
    let uu____3153 =
      let uu____3154 = format_issue issue1 in
      FStar_String.op_Hat uu____3154 "\n" in
    printer uu____3153
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1 ->
    fun i2 ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          Prims.int_zero
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
         uu____3173) -> ~- Prims.int_one
      | (FStar_Pervasives_Native.Some uu____3178,
         FStar_Pervasives_Native.None) -> Prims.int_one
      | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print ->
    let issues = FStar_Util.mk_ref [] in
    let add_one e =
      (let uu____3208 =
         (FStar_Options.defensive_abort ()) &&
           (e.issue_number = (FStar_Pervasives_Native.Some defensive_errno)) in
       if uu____3208
       then failwith "Aborting due to --defensive abort"
       else ());
      (match e.issue_level with
       | EInfo -> print_issue e
       | uu____3212 ->
           let uu____3213 =
             let uu____3216 = FStar_ST.op_Bang issues in e :: uu____3216 in
           FStar_ST.op_Colon_Equals issues uu____3213) in
    let count_errors uu____3244 =
      let uu____3245 = FStar_ST.op_Bang issues in
      FStar_List.fold_left
        (fun n ->
           fun i ->
             match i.issue_level with
             | EError -> n + Prims.int_one
             | uu____3262 -> n) Prims.int_zero uu____3245 in
    let report uu____3270 =
      let unique_issues =
        let uu____3274 = FStar_ST.op_Bang issues in
        FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu____3274 in
      let sorted_unique_issues =
        FStar_List.sortWith compare_issues unique_issues in
      if print then FStar_List.iter print_issue sorted_unique_issues else ();
      sorted_unique_issues in
    let clear uu____3301 = FStar_ST.op_Colon_Equals issues [] in
    {
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear
    }
let (default_handler : error_handler) = mk_default_handler true
let (current_handler : error_handler FStar_ST.ref) =
  FStar_Util.mk_ref default_handler
let (mk_issue :
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option ->
      Prims.string ->
        Prims.int FStar_Pervasives_Native.option ->
          Prims.string Prims.list -> issue)
  =
  fun level ->
    fun range ->
      fun msg ->
        fun n ->
          fun ctx ->
            {
              issue_msg = msg;
              issue_level = level;
              issue_range = range;
              issue_number = n;
              issue_ctx = ctx
            }
let (get_err_count : unit -> Prims.int) =
  fun uu____3355 ->
    let uu____3356 =
      let uu____3361 = FStar_ST.op_Bang current_handler in
      uu____3361.eh_count_errors in
    uu____3356 ()
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h ->
    fun issue1 ->
      h.eh_add_one issue1;
      if issue1.issue_level <> EInfo
      then
        ((let uu____3380 =
            let uu____3381 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3381 - Prims.int_one in
          FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____3380);
         (let uu____3394 =
            let uu____3395 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3395 = Prims.int_zero in
          if uu____3394 then failwith "Aborting due to --abort_on" else ()))
      else ()
let (add_one : issue -> unit) =
  fun issue1 ->
    FStar_Util.atomically
      (fun uu____3411 ->
         let uu____3412 = FStar_ST.op_Bang current_handler in
         wrapped_eh_add_one uu____3412 issue1)
let (add_many : issue Prims.list -> unit) =
  fun issues ->
    FStar_Util.atomically
      (fun uu____3430 ->
         let uu____3431 =
           let uu____3436 = FStar_ST.op_Bang current_handler in
           wrapped_eh_add_one uu____3436 in
         FStar_List.iter uu____3431 issues)
let (report_all : unit -> issue Prims.list) =
  fun uu____3449 ->
    let uu____3450 =
      let uu____3457 = FStar_ST.op_Bang current_handler in
      uu____3457.eh_report in
    uu____3450 ()
let (clear : unit -> unit) =
  fun uu____3468 ->
    let uu____3469 =
      let uu____3474 = FStar_ST.op_Bang current_handler in
      uu____3474.eh_clear in
    uu____3469 ()
let (set_handler : error_handler -> unit) =
  fun handler ->
    let issues = report_all () in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
type error_context_t =
  {
  push: Prims.string -> unit ;
  pop: unit -> Prims.string ;
  clear: unit -> unit ;
  get: unit -> Prims.string Prims.list }
let (__proj__Mkerror_context_t__item__push :
  error_context_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get;_} -> push
let (__proj__Mkerror_context_t__item__pop :
  error_context_t -> unit -> Prims.string) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get;_} -> pop
let (__proj__Mkerror_context_t__item__clear :
  error_context_t -> unit -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get;_} -> clear1
let (__proj__Mkerror_context_t__item__get :
  error_context_t -> unit -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get;_} -> get
let (error_context : error_context_t) =
  let ctxs = FStar_Util.mk_ref [] in
  let push s =
    let uu____3676 =
      let uu____3679 = FStar_ST.op_Bang ctxs in s :: uu____3679 in
    FStar_ST.op_Colon_Equals ctxs uu____3676 in
  let pop s =
    let uu____3708 = FStar_ST.op_Bang ctxs in
    match uu____3708 with
    | h::t -> (FStar_ST.op_Colon_Equals ctxs t; h)
    | uu____3736 -> failwith "cannot pop error prefix..." in
  let clear1 uu____3744 = FStar_ST.op_Colon_Equals ctxs [] in
  let get uu____3762 = FStar_ST.op_Bang ctxs in
  { push; pop; clear = clear1; get }
let (diag : FStar_Range.range -> Prims.string -> unit) =
  fun r ->
    fun msg ->
      let uu____3783 = FStar_Options.debug_any () in
      if uu____3783
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None [])
      else ()
let (warn_unsafe_options :
  FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> unit) =
  fun rng_opt ->
    fun msg ->
      let uu____3799 = FStar_Options.report_assumes () in
      match uu____3799 with
      | FStar_Pervasives_Native.Some "warn" ->
          let uu____3802 =
            let uu____3803 =
              FStar_String.op_Hat
                "Every use of this option triggers a warning: " msg in
            mk_issue EWarning rng_opt uu____3803
              (FStar_Pervasives_Native.Some warn_on_use_errno) [] in
          add_one uu____3802
      | FStar_Pervasives_Native.Some "error" ->
          let uu____3804 =
            let uu____3805 =
              FStar_String.op_Hat
                "Every use of this option triggers an error: " msg in
            mk_issue EError rng_opt uu____3805
              (FStar_Pervasives_Native.Some warn_on_use_errno) [] in
          add_one uu____3804
      | uu____3806 -> ()
let (set_option_warning_callback_range :
  FStar_Range.range FStar_Pervasives_Native.option -> unit) =
  fun ropt ->
    FStar_Options.set_option_warning_callback (warn_unsafe_options ropt)
let (uu___226 :
  (((Prims.string -> error_setting Prims.list) -> unit) *
    (unit -> error_setting Prims.list)))
  =
  let parser_callback = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let error_flags = FStar_Util.smap_create (Prims.of_int (10)) in
  let set_error_flags uu____3873 =
    let parse s =
      let uu____3882 = FStar_ST.op_Bang parser_callback in
      match uu____3882 with
      | FStar_Pervasives_Native.None ->
          failwith "Callback for parsing warn_error strings is not set"
      | FStar_Pervasives_Native.Some f -> f s in
    let we = FStar_Options.warn_error () in
    try
      (fun uu___238_3934 ->
         match () with
         | () ->
             let r = parse we in
             (FStar_Util.smap_add error_flags we
                (FStar_Pervasives_Native.Some r);
              FStar_Getopt.Success)) ()
    with
    | Invalid_warn_error_setting msg ->
        (FStar_Util.smap_add error_flags we FStar_Pervasives_Native.None;
         (let uu____3958 =
            FStar_String.op_Hat "Invalid --warn_error setting: " msg in
          FStar_Getopt.Error uu____3958)) in
  let get_error_flags uu____3966 =
    let we = FStar_Options.warn_error () in
    let uu____3968 = FStar_Util.smap_try_find error_flags we in
    match uu____3968 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some w) -> w
    | uu____3990 -> default_settings in
  let set_callbacks f =
    FStar_ST.op_Colon_Equals parser_callback (FStar_Pervasives_Native.Some f);
    FStar_Options.set_error_flags_callback set_error_flags;
    FStar_Options.set_option_warning_callback
      (warn_unsafe_options FStar_Pervasives_Native.None) in
  (set_callbacks, get_error_flags)
let (set_parse_warn_error :
  (Prims.string -> error_setting Prims.list) -> unit) =
  match uu___226 with
  | (set_parse_warn_error, error_flags) -> set_parse_warn_error
let (error_flags : unit -> error_setting Prims.list) =
  match uu___226 with | (set_parse_warn_error1, error_flags) -> error_flags
let (lookup : raw_error -> (raw_error * error_flag * Prims.int)) =
  fun err ->
    let flags = error_flags () in
    let uu____4150 = lookup_error flags err in
    match uu____4150 with
    | (v, level, i) ->
        let with_level level1 = (v, level1, i) in
        (match v with
         | Warning_Defensive when
             (FStar_Options.defensive_error ()) ||
               (FStar_Options.defensive_abort ())
             -> with_level CAlwaysError
         | Warning_WarnOnUse ->
             let level' =
               let uu____4185 = FStar_Options.report_assumes () in
               match uu____4185 with
               | FStar_Pervasives_Native.None -> level
               | FStar_Pervasives_Native.Some "warn" ->
                   (match level with
                    | CSilent -> CWarning
                    | uu____4188 -> level)
               | FStar_Pervasives_Native.Some "error" ->
                   (match level with
                    | CWarning -> CError
                    | CSilent -> CError
                    | uu____4189 -> level)
               | FStar_Pervasives_Native.Some uu____4190 -> level in
             with_level level'
         | uu____4191 -> with_level level)
let (log_issue_ctx :
  FStar_Range.range ->
    (raw_error * Prims.string) -> Prims.string Prims.list -> unit)
  =
  fun r ->
    fun uu____4211 ->
      fun ctx ->
        match uu____4211 with
        | (e, msg) ->
            let uu____4221 = lookup e in
            (match uu____4221 with
             | (uu____4228, CAlwaysError, errno) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno) ctx)
             | (uu____4230, CError, errno) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno) ctx)
             | (uu____4232, CWarning, errno) ->
                 add_one
                   (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno) ctx)
             | (uu____4234, CSilent, uu____4235) -> ()
             | (uu____4236, CFatal, errno) ->
                 let i =
                   mk_issue EError (FStar_Pervasives_Native.Some r) msg
                     (FStar_Pervasives_Native.Some errno) ctx in
                 let uu____4239 = FStar_Options.ide () in
                 if uu____4239
                 then add_one i
                 else
                   (let uu____4241 =
                      let uu____4242 = format_issue i in
                      FStar_String.op_Hat
                        "don't use log_issue to report fatal error, should use raise_error: "
                        uu____4242 in
                    failwith uu____4241))
let (log_issue : FStar_Range.range -> (raw_error * Prims.string) -> unit) =
  fun r ->
    fun uu____4256 ->
      match uu____4256 with
      | (e, msg) ->
          let ctx = error_context.get () in log_issue_ctx r (e, msg) ctx
let (add_errors : error Prims.list -> unit) =
  fun errs ->
    FStar_Util.atomically
      (fun uu____4276 ->
         FStar_List.iter
           (fun uu____4292 ->
              match uu____4292 with
              | (e, msg, r, ctx) -> log_issue_ctx r (e, msg) ctx) errs)
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun e ->
    match e with
    | Error (e1, msg, r, ctx) ->
        let errno = let uu____4329 = lookup e1 in error_number uu____4329 in
        FStar_Pervasives_Native.Some
          (mk_issue EError (FStar_Pervasives_Native.Some r) msg
             (FStar_Pervasives_Native.Some errno) ctx)
    | Err (e1, msg, ctx) ->
        let errno = let uu____4344 = lookup e1 in error_number uu____4344 in
        FStar_Pervasives_Native.Some
          (mk_issue EError FStar_Pervasives_Native.None msg
             (FStar_Pervasives_Native.Some errno) ctx)
    | uu____4351 -> FStar_Pervasives_Native.None
let (err_exn : Prims.exn -> unit) =
  fun exn ->
    if exn = Stop
    then ()
    else
      (let uu____4358 = issue_of_exn exn in
       match uu____4358 with
       | FStar_Pervasives_Native.Some issue1 -> add_one issue1
       | FStar_Pervasives_Native.None -> FStar_Exn.raise exn)
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___0_4366 ->
    match uu___0_4366 with
    | Error uu____4367 -> true
    | Stop -> true
    | Err uu____4368 -> true
    | uu____4377 -> false
let (stop_if_err : unit -> unit) =
  fun uu____4382 ->
    let uu____4383 =
      let uu____4384 = get_err_count () in uu____4384 > Prims.int_zero in
    if uu____4383 then FStar_Exn.raise Stop else ()
let raise_error :
  'uuuuuu4392 .
    (raw_error * Prims.string) -> FStar_Range.range -> 'uuuuuu4392
  =
  fun uu____4405 ->
    fun r ->
      match uu____4405 with
      | (e, msg) ->
          let uu____4413 =
            let uu____4414 =
              let uu____4415 = error_context.get () in
              (e, msg, r, uu____4415) in
            Error uu____4414 in
          FStar_Exn.raise uu____4413
let raise_err : 'uuuuuu4424 . (raw_error * Prims.string) -> 'uuuuuu4424 =
  fun uu____4433 ->
    match uu____4433 with
    | (e, msg) ->
        let uu____4440 =
          let uu____4441 =
            let uu____4450 = error_context.get () in (e, msg, uu____4450) in
          Err uu____4441 in
        FStar_Exn.raise uu____4440
let with_ctx : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      let uu____4477 = FStar_Options.trace_error () in
      if uu____4477
      then f ()
      else
        (error_context.push s;
         (let r =
            try
              (fun uu___368_4491 ->
                 match () with | () -> let r = f () in FStar_Util.Inr r) ()
            with | uu___367_4498 -> FStar_Util.Inl uu___367_4498 in
          (let uu____4504 = error_context.pop () in ());
          (match r with
           | FStar_Util.Inr r1 -> r1
           | FStar_Util.Inl e -> FStar_Exn.raise e)))
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f ->
    let newh = mk_default_handler false in
    let old = FStar_ST.op_Bang current_handler in
    FStar_ST.op_Colon_Equals current_handler newh;
    (let r =
       try
         (fun uu___386_4552 ->
            match () with
            | () -> let r = f () in FStar_Pervasives_Native.Some r) ()
       with
       | uu___385_4558 ->
           (err_exn uu___385_4558; FStar_Pervasives_Native.None) in
     let all_issues = newh.eh_report () in
     FStar_ST.op_Colon_Equals current_handler old;
     (let uu____4572 =
        FStar_List.partition (fun i -> i.issue_level = EError) all_issues in
      match uu____4572 with
      | (errs, rest) -> (FStar_List.iter old.eh_add_one rest; (errs, r))))
let (find_multiset_discrepancy :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1 ->
    fun l2 ->
      let sort = FStar_List.sortWith (fun x -> fun y -> x - y) in
      let rec collect l =
        match l with
        | [] -> []
        | hd::tl ->
            let uu____4682 = collect tl in
            (match uu____4682 with
             | [] -> [(hd, Prims.int_one)]
             | (h, n)::t ->
                 if h = hd
                 then (h, (n + Prims.int_one)) :: t
                 else (hd, Prims.int_one) :: (h, n) :: t) in
      let summ l = collect l in
      let l11 = let uu____4762 = sort l1 in summ uu____4762 in
      let l21 = let uu____4772 = sort l2 in summ uu____4772 in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], []) -> FStar_Pervasives_Native.None
        | ((e, n)::uu____4866, []) ->
            FStar_Pervasives_Native.Some (e, n, Prims.int_zero)
        | ([], (e, n)::uu____4901) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n)
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2 in
      aux l11 l21