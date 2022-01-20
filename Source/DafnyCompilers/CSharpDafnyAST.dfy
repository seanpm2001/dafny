include "CSharpCompat.dfy"

module {:extern "CSharpDafnyAST"} CSharpDafnyAST {
  import opened CSharpGenerics
  import opened CSharpSystem
  import opened Boogie
  import opened Dafny

  datatype {:extern "Attributes.MatchingValueOption"} Attributes_MatchingValueOption =
    | Empty
    | Bool
    | Int
    | String
    | Expression

  datatype {:extern "Type.NumericPersuasion"} Type_NumericPersuasion =
    | Int
    | Real

  datatype {:extern "Type.AutoInitInfo"} Type_AutoInitInfo =
    | MaybeEmpty
    | Nonempty
    | CompilableValue

  datatype {:extern "TypeProxy.Family"} TypeProxy_Family =
    | Unknown
    | Bool
    | Char
    | IntLike
    | RealLike
    | Ordinal
    | BitVector
    | ValueType
    | Ref
    | Opaque

  datatype {:extern "TypeParameter.TPVarianceSyntax"} TypeParameter_TPVarianceSyntax =
    | NonVariant_Strict
    | NonVariant_Permissive
    | Covariant_Strict
    | Covariant_Permissive
    | Contravariance

  datatype {:extern "TypeParameter.TPVariance"} TypeParameter_TPVariance =
    | Co
    | Non
    | Contra

  datatype {:extern "TypeParameter.EqualitySupportValue"} TypeParameter_EqualitySupportValue =
    | Required
    | InferredRequired
    | Unspecified

  datatype {:extern "IndDatatypeDecl.ES"} IndDatatypeDecl_ES =
    | NotYetComputed
    | Never
    | ConsultTypeArguments

  datatype {:extern "SpecialField.ID"} SpecialField_ID =
    | UseIdParam
    | ArrayLength
    | ArrayLengthInt
    | Floor
    | IsLimit
    | IsSucc
    | Offset
    | IsNat
    | Keys
    | Values
    | Items
    | Reads
    | Modifies
    | New

  datatype {:extern "NativeType.Selection"} NativeType_Selection =
    | Byte
    | SByte
    | UShort
    | Short
    | UInt
    | Int
    | Number
    | ULong
    | Long

  datatype {:extern "SubsetTypeDecl.WKind"} SubsetTypeDecl_WKind =
    | CompiledZero
    | Compiled
    | Ghost
    | OptOut
    | Special

  datatype {:extern "Function.TailStatus"} Function_TailStatus =
    | TriviallyTailRecursive
    | TailRecursive
    | NotTailRecursive
    | Accumulate_Add
    | AccumulateRight_Sub
    | Accumulate_Mul
    | Accumulate_SetUnion
    | AccumulateRight_SetDifference
    | Accumulate_MultiSetUnion
    | AccumulateRight_MultiSetDifference
    | AccumulateLeft_Concat
    | AccumulateRight_Concat

  datatype {:extern "Function.CoCallClusterInvolvement"} Function_CoCallClusterInvolvement =
    | None
    | IsMutuallyRecursiveTarget
    | CoRecursiveTargetAllTheWay

  datatype {:extern "Predicate.BodyOriginKind"} Predicate_BodyOriginKind =
    | OriginalOrInherited
    | DelayedDefinition
    | Extension

  datatype {:extern "ExtremePredicate.KType"} ExtremePredicate_KType =
    | Unspecified
    | Nat
    | {:extern "ORDINAL"} CSharp_ORDINAL

  datatype {:extern "AssignStmt.NonGhostKind"} AssignStmt_NonGhostKind =
    | IsGhost
    | Variable
    | Field
    | ArrayElement

  datatype {:extern "ForallStmt.BodyKind"} ForallStmt_BodyKind =
    | Assign
    | Call
    | Proof

  datatype {:extern "FunctionCallExpr.CoCallResolution"} FunctionCallExpr_CoCallResolution =
    | No
    | Yes
    | NoBecauseFunctionHasSideEffects
    | NoBecauseFunctionHasPostcondition
    | NoBecauseRecursiveCallsAreNotAllowedInThisContext
    | NoBecauseIsNotGuarded
    | NoBecauseRecursiveCallsInDestructiveContext

  datatype {:extern "UnaryOpExpr.UnOpcode"} UnaryOpExpr_UnOpcode =
    | Not
    | Cardinality
    | Fresh
    | Allocated
    | Lit

  datatype {:extern "BinaryExpr.BinOpcode"} BinaryExpr_BinOpcode =
    | Iff
    | Imp
    | Exp
    | And
    | Or
    | Eq
    | Neq
    | Lt
    | Le
    | Ge
    | Gt
    | Disjoint
    | In
    | NotIn
    | LeftShift
    | RightShift
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | BitwiseAnd
    | BitwiseOr
    | BitwiseXor

  datatype {:extern "BinaryExpr.ResolvedOpcode"} BinaryExpr_ResolvedOpcode =
    | YetUndetermined
    | Iff
    | Imp
    | And
    | Or
    | EqCommon
    | NeqCommon
    | Lt
    | LessThanLimit
    | Le
    | Ge
    | Gt
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | LeftShift
    | RightShift
    | BitwiseAnd
    | BitwiseOr
    | BitwiseXor
    | LtChar
    | LeChar
    | GeChar
    | GtChar
    | SetEq
    | SetNeq
    | ProperSubset
    | Subset
    | Superset
    | ProperSuperset
    | Disjoint
    | InSet
    | NotInSet
    | Union
    | Intersection
    | SetDifference
    | MultiSetEq
    | MultiSetNeq
    | MultiSubset
    | MultiSuperset
    | ProperMultiSubset
    | ProperMultiSuperset
    | MultiSetDisjoint
    | InMultiSet
    | NotInMultiSet
    | MultiSetUnion
    | MultiSetIntersection
    | MultiSetDifference
    | SeqEq
    | SeqNeq
    | ProperPrefix
    | Prefix
    | Concat
    | InSeq
    | NotInSeq
    | MapEq
    | MapNeq
    | InMap
    | NotInMap
    | MapMerge
    | MapSubtraction
    | RankLt
    | RankGt

  datatype {:extern "BinaryExpr.AccumulationOperand"} BinaryExpr_AccumulationOperand =
    | None
    | Left
    | Right

  datatype {:extern "TernaryExpr.TerOpcode"} TernaryExpr_TerOpcode =
    | PrefixEqOp
    | PrefixNeqOp

  datatype {:extern "BoundedPool.PoolVirtues"} BoundedPool_PoolVirtues =
    | None
    | Finite
    | Enumerable
    | IndependentOfAlloc
    | IndependentOfAlloc_or_ExplicitAlloc

  trait {:compile false} {:extern} Program {
    var FullName: string
    var ModuleSigs: Dictionary<ModuleDefinition, ModuleSignature>
    var CompileModules: List<ModuleDefinition>
    var MainMethod: Method
    var DefaultModule: ModuleDecl
    var DefaultModuleDef: ModuleDefinition
    var BuiltIns: BuiltIns
    var reporter: ErrorReporter
  }

  trait {:compile false} {:extern} Include extends IComparable {
    var tok: IToken
    var includerFilename: string
    var includedFilename: string
    var canonicalPath: string
    var ErrorReported: bool
  }

  trait {:compile false} {:extern} BuiltIns {
    var SystemModule: ModuleDefinition
    var arrayTypeDecls: Dictionary<int, ClassDecl>
    var ArrowTypeDecls: Dictionary<int, ArrowTypeDecl>
    var PartialArrowTypeDecls: Dictionary<int, SubsetTypeDecl>
    var TotalArrowTypeDecls: Dictionary<int, SubsetTypeDecl>
    var tupleTypeDecls: Dictionary<List<bool>, TupleTypeDecl>
    var Bitwidths: ISet<int>
    var ORDINAL_Offset: SpecialField
    var NatDecl: SubsetTypeDecl
    var ObjectDecl: TraitDecl
    var TupleTypeCtorNamePrefix: string
  }

  trait {:compile false} {:extern} IBoundVarsBearingExpression extends IRegion {
  }

  trait {:compile false} {:extern} IAttributeBearingDeclaration {
  }

  trait {:compile false} {:extern} Attributes {
    var Name: string
    var Args: List<Expression>
    var Prev: Attributes
  }

  trait {:compile false} {:extern} AttributesExtensions {
  }

  trait {:compile false} {:extern} UserSuppliedAttributes extends Attributes {
    var tok: IToken
    var OpenBrace: IToken
    var CloseBrace: IToken
    var Recognized: bool
  }

  trait {:compile false} {:extern} Type {
    var Bool: BoolType
    var Char: CharType
    var Int: IntType
    var Real: RealType
    var BigOrdinal: BigOrdinalType
    var scopes: List<VisibilityScope>
    var scopesEnabled: bool
    var TypeArgs: List<Type>
  }

  trait {:compile false} {:extern} ArtificialType extends Type {
  }

  trait {:compile false} {:extern} IntVarietiesSupertype extends ArtificialType {
  }

  trait {:compile false} {:extern} RealVarietiesSupertype extends ArtificialType {
  }

  trait {:compile false} {:extern} NonProxyType extends Type {
  }

  trait {:compile false} {:extern} BasicType extends NonProxyType {
  }

  trait {:compile false} {:extern} BoolType extends BasicType {
  }

  trait {:compile false} {:extern} CharType extends BasicType {
    var DefaultValue: char
    var DefaultValueAsString: string
  }

  trait {:compile false} {:extern} IntType extends BasicType {
  }

  trait {:compile false} {:extern} RealType extends BasicType {
  }

  trait {:compile false} {:extern} BigOrdinalType extends BasicType {
  }

  trait {:compile false} {:extern} BitvectorType extends BasicType {
    var Width: int
    var NativeType: NativeType
  }

  trait {:compile false} {:extern} SelfType extends NonProxyType {
    var TypeArg: TypeParameter
    var ResolvedType: Type
  }

  trait {:compile false} {:extern} ArrowType extends UserDefinedType {
    var Arrow_FullCompileName: string
    var ANY_ARROW: string
    var PARTIAL_ARROW: string
    var TOTAL_ARROW: string
  }

  trait {:compile false} {:extern} CollectionType extends NonProxyType {
    var arg: Type
  }

  trait {:compile false} {:extern} SetType extends CollectionType {
    var finite: bool
  }

  trait {:compile false} {:extern} MultiSetType extends CollectionType {
  }

  trait {:compile false} {:extern} SeqType extends CollectionType {
  }

  trait {:compile false} {:extern} MapType extends CollectionType {
    var finite: bool
    var range: Type
  }

  trait {:compile false} {:extern} UserDefinedType extends NonProxyType {
    var NamePath: Expression
    var tok: IToken
    var Name: string
    var compileName: string
    var ResolvedClass: TopLevelDecl
  }

  trait {:compile false} {:extern} TypeProxy extends Type {
    var T: Type
    var SupertypeConstraints: List<Resolver_TypeConstraint>
    var SubtypeConstraints: List<Resolver_TypeConstraint>
    var family: Family
    var {:extern "_id"} CSharp__id: int
    var id: int
  }

  trait {:compile false} {:extern} InferredTypeProxy extends TypeProxy {
    var KeepConstraints: bool
  }

  trait {:compile false} {:extern} ParamTypeProxy extends TypeProxy {
    var orig: TypeParameter
  }

  trait {:compile false} {:extern} IRegion {
  }

  trait {:compile false} {:extern} INamedRegion extends IRegion {
  }

  trait {:compile false} {:extern} Declaration extends INamedRegion, IAttributeBearingDeclaration {
    var tok: IToken
    var BodyStartTok: IToken
    var BodyEndTok: IToken
    var Name: string
    var IsRefining: bool
    var compileName: string
    var opaqueScope: VisibilityScope
    var revealScope: VisibilityScope
    var scopeIsInherited: bool
    var Attributes: Attributes
    var IdGenerator: FreshIdGenerator
  }

  trait {:compile false} {:extern} TypeParameter extends TopLevelDecl {
    var parent: ParentType
    var VarianceSyntax: TPVarianceSyntax
    var Characteristics: TypeParameterCharacteristics
    var NecessaryForEqualitySupportOfSurroundingInductiveDatatype: bool
    var PositionalIndex: int
  }

  trait {:compile false} {:extern} {:extern "TypeParameter.ParentType"} TypeParameter_ParentType {
  }

  trait {:compile false} {:extern} {:extern "TypeParameter.TypeParameterCharacteristics"} TypeParameter_TypeParameterCharacteristics {
    var EqualitySupport: EqualitySupportValue
    var AutoInit: Type_AutoInitInfo
    var ContainsNoReferenceTypes: bool
  }

  trait {:compile false} {:extern} ModuleDecl extends TopLevelDecl {
    var Signature: ModuleSignature
    var Height: int
    var Opened: bool
  }

  trait {:compile false} {:extern} LiteralModuleDecl extends ModuleDecl {
    var ModuleDef: ModuleDefinition
    var DefaultExport: ModuleSignature
    var emptySignature: ModuleSignature
  }

  trait {:compile false} {:extern} AliasModuleDecl extends ModuleDecl {
    var TargetQId: ModuleQualifiedId
    var Exports: List<IToken>
    var ShadowsLiteralModule: bool
  }

  trait {:compile false} {:extern} AbstractModuleDecl extends ModuleDecl {
    var QId: ModuleQualifiedId
    var Exports: List<IToken>
    var CompileRoot: ModuleDecl
    var OriginalSignature: ModuleSignature
  }

  trait {:compile false} {:extern} ModuleExportDecl extends ModuleDecl {
    var IsDefault: bool
    var Exports: List<ExportSignature>
    var Extends: List<IToken>
    var ExtendDecls: List<ModuleExportDecl>
    var ExportDecls: HashSet<Tuple2<Declaration, bool>>
    var RevealAll: bool
    var ProvideAll: bool
    var ThisScope: VisibilityScope
  }

  trait {:compile false} {:extern} ExportSignature {
    var Tok: IToken
    var ClassIdTok: IToken
    var Opaque: bool
    var ClassId: string
    var Id: string
    var Decl: Declaration
  }

  trait {:compile false} {:extern} ModuleSignature {
    var VisibilityScope: VisibilityScope
    var TopLevels: Dictionary<string, TopLevelDecl>
    var ExportSets: Dictionary<string, ModuleExportDecl>
    var Ctors: Dictionary<string, Tuple2<DatatypeCtor, bool>>
    var StaticMembers: Dictionary<string, MemberDecl>
    var ModuleDef: ModuleDefinition
    var CompileSignature: ModuleSignature
    var Refines: ModuleSignature
    var IsAbstract: bool
  }

  trait {:compile false} {:extern} ModuleQualifiedId {
    var Path: List<IToken>
    var Root: ModuleDecl
    var Decl: ModuleDecl
    var Def: ModuleDefinition
    var Sig: ModuleSignature
  }

  trait {:compile false} {:extern} ModuleDefinition extends INamedRegion, IAttributeBearingDeclaration {
    var tok: IToken
    var BodyStartTok: IToken
    var BodyEndTok: IToken
    var DafnyName: string
    var Name: string
    var PrefixIds: List<IToken>
    var EnclosingModule: ModuleDefinition
    var Attributes: Attributes
    var RefinementQId: ModuleQualifiedId
    var SuccessfullyResolved: bool
    var Includes: List<Include>
    var TopLevelDecls: List<TopLevelDecl>
    var PrefixNamedModules: List<Tuple2<List<IToken>, LiteralModuleDecl>>
    var CallGraph: Graph<ICallable>
    var Height: int
    var IsAbstract: bool
    var IsFacade: bool
    var IsBuiltinName: bool
    var IsToBeVerified: bool
    var IsToBeCompiled: bool
    var visibilityScope: VisibilityScope
    var compileName: string
  }

  trait {:compile false} {:extern} DefaultModuleDecl extends ModuleDefinition {
  }

  trait {:compile false} {:extern} TopLevelDecl extends Declaration, TypeParameter_ParentType {
    var EnclosingModuleDefinition: ModuleDefinition
    var TypeArgs: List<TypeParameter>
  }

  trait {:compile false} {:extern} TopLevelDeclWithMembers extends TopLevelDecl {
    var Members: List<MemberDecl>
    var InheritedMembers: List<MemberDecl>
    var ParentTraits: List<Type>
    var ParentFormalTypeParametersToActuals: Dictionary<TypeParameter, Type>
    var ParentTraitHeads: List<TraitDecl>
    var ParentTypeInformation: InheritanceInformationClass
  }

  trait {:compile false} {:extern} {:extern "TopLevelDeclWithMembers.InheritanceInformationClass"} TopLevelDeclWithMembers_InheritanceInformationClass {
    var info: Dictionary<TraitDecl, List<(Type, List<TraitDecl> /*via this parent path*/)>>
  }

  trait {:compile false} {:extern} TraitDecl extends ClassDecl {
  }

  trait {:compile false} {:extern} ClassDecl extends TopLevelDeclWithMembers, RevealableTypeDecl {
    var HasConstructor: bool
    var NonNullTypeDecl: NonNullTypeDecl
  }

  trait {:compile false} {:extern} DefaultClassDecl extends ClassDecl {
  }

  trait {:compile false} {:extern} ArrayClassDecl extends ClassDecl {
    var Dims: int
  }

  trait {:compile false} {:extern} ArrowTypeDecl extends ClassDecl {
    var Arity: int
    var Requires: Function
    var Reads: Function
  }

  trait {:compile false} {:extern} DatatypeDecl extends TopLevelDeclWithMembers, RevealableTypeDecl, ICallable {
    var Ctors: List<DatatypeCtor>
  }

  trait {:compile false} {:extern} IndDatatypeDecl extends DatatypeDecl, RevealableTypeDecl {
    var GroundingCtor: DatatypeCtor
    var TypeParametersUsedInConstructionByGroundingCtor: array<bool>
    var EqualitySupport: ES
  }

  trait {:compile false} {:extern} TupleTypeDecl extends IndDatatypeDecl {
    var ArgumentGhostness: List<bool>
  }

  trait {:compile false} {:extern} CoDatatypeDecl extends DatatypeDecl {
    var SscRepr: CoDatatypeDecl
  }

  trait {:compile false} {:extern} ValuetypeDecl extends TopLevelDecl {
    var Members: Dictionary<string, MemberDecl>
    var typeTester: Func<Type, bool>
    var typeCreator: Func<List<Type>, Type>
  }

  trait {:compile false} {:extern} DatatypeCtor extends Declaration, TypeParameter_ParentType {
    var Formals: List<Formal>
    var EnclosingDatatype: DatatypeDecl
    var QueryField: SpecialField
    var Destructors: List<DatatypeDestructor>
  }

  trait {:compile false} {:extern} ICodeContext {
  }

  trait {:compile false} {:extern} CodeContextWrapper extends ICodeContext {
    var inner: ICodeContext
    var isGhostContext: bool
  }

  trait {:compile false} {:extern} ICallable extends ICodeContext {
  }

  trait {:compile false} {:extern} CallableWrapper extends CodeContextWrapper, ICallable {
  }

  trait {:compile false} {:extern} DontUseICallable extends ICallable {
  }

  trait {:compile false} {:extern} IMethodCodeContext extends ICallable {
  }

  trait {:compile false} {:extern} NoContext extends ICodeContext {
    var Module: ModuleDefinition
  }

  trait {:compile false} {:extern} IteratorDecl extends ClassDecl, IMethodCodeContext {
    var Ins: List<Formal>
    var Outs: List<Formal>
    var Reads: Specification<FrameExpression>
    var Modifies: Specification<FrameExpression>
    var Decreases: Specification<Expression>
    var Requires: List<AttributedExpression>
    var Ensures: List<AttributedExpression>
    var YieldRequires: List<AttributedExpression>
    var YieldEnsures: List<AttributedExpression>
    var Body: BlockStmt
    var SignatureEllipsis: IToken
    var OutsFields: List<Field>
    var OutsHistoryFields: List<Field>
    var DecreasesFields: List<Field>
    var Member_Modifies: SpecialField
    var Member_Reads: SpecialField
    var Member_New: SpecialField
    var Member_Init: Constructor
    var Member_Valid: Predicate
    var Member_MoveNext: Method
    var YieldCountVariable: LocalVariable
    var {:extern "_inferredDecr"} CSharp__inferredDecr: bool
  }

  trait {:compile false} {:extern} {:extern "IteratorDecl.EverIncreasingType"} IteratorDecl_EverIncreasingType extends BasicType {
  }

  trait {:compile false} {:extern} MemberDecl extends Declaration {
    var HasStaticKeyword: bool
    var isGhost: bool
    var EnclosingClass: TopLevelDecl
    var RefinementBase: MemberDecl
    var OverriddenMember: MemberDecl
  }

  trait {:compile false} {:extern} Field extends MemberDecl {
    var IsMutable: bool
    var IsUserMutable: bool
    var Type: Type
  }

  trait {:compile false} {:extern} SpecialFunction extends Function, ICodeContext, ICallable {
    var Module: ModuleDefinition
  }

  trait {:compile false} {:extern} SpecialField extends Field {
    var SpecialId: ID
    var IdParam: object
  }

  trait {:compile false} {:extern} DatatypeDestructor extends SpecialField {
    var EnclosingCtors: List<DatatypeCtor>
    var CorrespondingFormals: List<Formal>
  }

  trait {:compile false} {:extern} ConstantField extends SpecialField, ICallable {
    var Rhs: Expression
  }

  trait {:compile false} {:extern} OpaqueTypeDecl extends TopLevelDeclWithMembers, TypeParameter_ParentType, RevealableTypeDecl {
    var Characteristics: TypeParameter_TypeParameterCharacteristics
  }

  trait {:compile false} {:extern} RedirectingTypeDecl extends ICallable {
  }

  trait {:compile false} {:extern} NativeType {
    var Name: string
    var LowerBound: int
    var UpperBound: int
    var Bitwidth: int
    var Sel: Selection
  }

  trait {:compile false} {:extern} RevealableTypeDeclHelper {
    var tsdMap: Dictionary<TopLevelDecl, InternalTypeSynonymDecl>
  }

  trait {:compile false} {:extern} RevealableTypeDecl {
  }

  trait {:compile false} {:extern} NewtypeDecl extends TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl {
    var BaseType: Type
    var Var: BoundVar
    var Constraint: Expression
    var WitnessKind: SubsetTypeDecl_WKind
    var Witness: Expression
    var NativeType: NativeType
  }

  trait {:compile false} {:extern} TypeSynonymDeclBase extends TopLevelDecl, RedirectingTypeDecl {
    var Characteristics: TypeParameter_TypeParameterCharacteristics
    var Rhs: Type
  }

  trait {:compile false} {:extern} TypeSynonymDecl extends TypeSynonymDeclBase, RedirectingTypeDecl, RevealableTypeDecl {
  }

  trait {:compile false} {:extern} InternalTypeSynonymDecl extends TypeSynonymDeclBase, RedirectingTypeDecl {
  }

  trait {:compile false} {:extern} SubsetTypeDecl extends TypeSynonymDecl, RedirectingTypeDecl {
    var Var: BoundVar
    var Constraint: Expression
    var WitnessKind: SubsetTypeDecl_WKind
    var Witness: Expression
    var ConstraintIsCompilable: bool
    var CheckedIfConstraintIsCompilable: bool
  }

  trait {:compile false} {:extern} NonNullTypeDecl extends SubsetTypeDecl {
    var Class: ClassDecl
  }

  trait {:compile false} {:extern} IVariable {
    var CompileNameIdGenerator: FreshIdGenerator
  }

  trait {:compile false} {:extern} IVariableContracts extends IVariable {
  }

  trait {:compile false} {:extern} NonglobalVariable extends IVariable {
    var tok: IToken
    var name: string
    var uniqueName: string
    var specialChars: array<char>
    var compileName: string
    var {:extern "type"} CSharp_type: Type
    var isGhost: bool
  }

  trait {:compile false} {:extern} Formal extends NonglobalVariable {
    var InParam: bool
    var IsOld: bool
    var DefaultValue: Expression
    var IsNameOnly: bool
    var NameForCompilation: string
  }

  trait {:compile false} {:extern} ImplicitFormal extends Formal {
  }

  trait {:compile false} {:extern} ThisSurrogate extends ImplicitFormal {
  }

  trait {:compile false} {:extern} BoundVar extends NonglobalVariable {
  }

  trait {:compile false} {:extern} ActualBinding {
    var FormalParameterName: IToken
    var Actual: Expression
    var IsGhost: bool
  }

  trait {:compile false} {:extern} ActualBindings {
    var ArgumentBindings: List<ActualBinding>
    var arguments: List<Expression>
  }

  trait {:compile false} {:extern} Function extends MemberDecl, TypeParameter_ParentType, ICallable {
    var IsRecursive: bool
    var TailRecursion: TailStatus
    var IsFueled: bool
    var TypeArgs: List<TypeParameter>
    var Formals: List<Formal>
    var Result: Formal
    var ResultType: Type
    var Req: List<AttributedExpression>
    var Reads: List<FrameExpression>
    var Ens: List<AttributedExpression>
    var Decreases: Specification<Expression>
    var Body: Expression
    var ByMethodTok: IToken
    var ByMethodBody: BlockStmt
    var ByMethodDecl: Method
    var SignatureEllipsis: IToken
    var OverriddenFunction: Function
    var containsQuantifier: bool
    var AllCalls: List<FunctionCallExpr>
    var CoClusterTarget: CoCallClusterInvolvement
    var {:extern "_inferredDecr"} CSharp__inferredDecr: bool
  }

  trait {:compile false} {:extern} Predicate extends Function {
    var BodyOrigin: BodyOriginKind
  }

  trait {:compile false} {:extern} PrefixPredicate extends Function {
    var K: Formal
    var ExtremePred: ExtremePredicate
  }

  trait {:compile false} {:extern} ExtremePredicate extends Function {
    var TypeOfK: KType
    var Uses: List<FunctionCallExpr>
    var PrefixPredicate: PrefixPredicate
  }

  trait {:compile false} {:extern} LeastPredicate extends ExtremePredicate {
  }

  trait {:compile false} {:extern} GreatestPredicate extends ExtremePredicate {
  }

  trait {:compile false} {:extern} TwoStateFunction extends Function {
  }

  trait {:compile false} {:extern} TwoStatePredicate extends TwoStateFunction {
  }

  trait {:compile false} {:extern} Method extends MemberDecl, TypeParameter_ParentType, IMethodCodeContext {
    var SignatureEllipsis: IToken
    var IsByMethod: bool
    var MustReverify: bool
    var IsEntryPoint: bool
    var TypeArgs: List<TypeParameter>
    var Ins: List<Formal>
    var Outs: List<Formal>
    var Req: List<AttributedExpression>
    var Mod: Specification<FrameExpression>
    var Ens: List<AttributedExpression>
    var Decreases: Specification<Expression>
    var methodBody: BlockStmt
    var IsRecursive: bool
    var IsTailRecursive: bool
    var AssignedAssumptionVariables: ISet<IVariable>
    var OverriddenMethod: Method
    var emptyBody: BlockStmt
    var {:extern "_inferredDecr"} CSharp__inferredDecr: bool
  }

  trait {:compile false} {:extern} Lemma extends Method {
  }

  trait {:compile false} {:extern} TwoStateLemma extends Method {
  }

  trait {:compile false} {:extern} Constructor extends Method {
  }

  trait {:compile false} {:extern} PrefixLemma extends Method {
    var K: Formal
    var ExtremeLemma: ExtremeLemma
  }

  trait {:compile false} {:extern} ExtremeLemma extends Method {
    var TypeOfK: ExtremePredicate_KType
    var PrefixLemma: PrefixLemma
  }

  trait {:compile false} {:extern} LeastLemma extends ExtremeLemma {
  }

  trait {:compile false} {:extern} GreatestLemma extends ExtremeLemma {
  }

  trait {:compile false} {:extern} Statement extends IAttributeBearingDeclaration {
    var Tok: IToken
    var EndTok: IToken
    var Labels: LList<Label>
    var attributes: Attributes
    var IsGhost: bool
  }

  trait {:compile false} {:extern} LList<T> {
    var Data: T
    var Next: LList<T>
    var Empty: LList<T>
  }

  trait {:compile false} {:extern} Label {
    var Tok: IToken
    var Name: string
    var uniqueId: string
  }

  trait {:compile false} {:extern} AssertLabel extends Label {
    var E: Boogie.Expr
  }

  trait {:compile false} {:extern} PredicateStmt extends Statement {
    var Expr: Expression
  }

  trait {:compile false} {:extern} AssertStmt extends PredicateStmt {
    var Proof: BlockStmt
    var Label: AssertLabel
  }

  trait {:compile false} {:extern} ExpectStmt extends PredicateStmt {
    var Message: Expression
  }

  trait {:compile false} {:extern} AssumeStmt extends PredicateStmt {
  }

  trait {:compile false} {:extern} PrintStmt extends Statement {
    var Args: List<Expression>
  }

  trait {:compile false} {:extern} RevealStmt extends Statement {
    var Exprs: List<Expression>
    var LabeledAsserts: List<AssertLabel>
    var ResolvedStatements: List<Statement>
  }

  trait {:compile false} {:extern} BreakStmt extends Statement {
    var TargetLabel: IToken
    var BreakCount: int
    var TargetStmt: Statement
  }

  trait {:compile false} {:extern} ProduceStmt extends Statement {
    var rhss: List<AssignmentRhs>
    var hiddenUpdate: UpdateStmt
  }

  trait {:compile false} {:extern} ReturnStmt extends ProduceStmt {
    var ReverifyPost: bool
  }

  trait {:compile false} {:extern} YieldStmt extends ProduceStmt {
  }

  trait {:compile false} {:extern} AssignmentRhs {
    var Tok: IToken
    var attributes: Attributes
  }

  trait {:compile false} {:extern} ExprRhs extends AssignmentRhs {
    var Expr: Expression
  }

  trait {:compile false} {:extern} TypeRhs extends AssignmentRhs {
    var EType: Type
    var ArrayDimensions: List<Expression>
    var ElementInit: Expression
    var InitDisplay: List<Expression>
    var Bindings: ActualBindings
    var Path: Type
    var InitCall: CallStmt
    var Type: Type
  }

  trait {:compile false} {:extern} HavocRhs extends AssignmentRhs {
  }

  trait {:compile false} {:extern} VarDeclStmt extends Statement {
    var Locals: List<LocalVariable>
    var Update: ConcreteUpdateStatement
  }

  trait {:compile false} {:extern} VarDeclPattern extends Statement {
    var LHS: CasePattern<LocalVariable>
    var RHS: Expression
    var HasGhostModifier: bool
  }

  trait {:compile false} {:extern} ConcreteUpdateStatement extends Statement {
    var Lhss: List<Expression>
  }

  trait {:compile false} {:extern} AssignSuchThatStmt extends ConcreteUpdateStatement {
    var Expr: Expression
    var AssumeToken: IToken
    var Bounds: List<ComprehensionExpr_BoundedPool>
    var MissingBounds: List<IVariable>
  }

  trait {:compile false} {:extern} {:extern "AssignSuchThatStmt.WiggleWaggleBound"} AssignSuchThatStmt_WiggleWaggleBound extends ComprehensionExpr_BoundedPool {
  }

  trait {:compile false} {:extern} UpdateStmt extends ConcreteUpdateStatement {
    var Rhss: List<AssignmentRhs>
    var CanMutateKnownState: bool
    var OriginalInitialLhs: Expression
    var ResolvedStatements: List<Statement>
  }

  trait {:compile false} {:extern} AssignOrReturnStmt extends ConcreteUpdateStatement {
    var Rhs: Expression
    var Rhss: List<AssignmentRhs>
    var KeywordToken: IToken
    var ResolvedStatements: List<Statement>
  }

  trait {:compile false} {:extern} AssignStmt extends Statement {
    var Lhs: Expression
    var Rhs: AssignmentRhs
  }

  trait {:compile false} {:extern} LocalVariable extends IVariable, IAttributeBearingDeclaration {
    var Tok: IToken
    var EndTok: IToken
    var name: string
    var Attributes: Attributes
    var IsGhost: bool
    var uniqueName: string
    var compileName: string
    var OptionalType: Type
    var {:extern "type"} CSharp_type: Type
  }

  trait {:compile false} {:extern} CallStmt extends Statement {
    var Lhs: List<Expression>
    var MethodSelect: MemberSelectExpr
    var Bindings: ActualBindings
    var OriginalInitialLhs: Expression
  }

  trait {:compile false} {:extern} BlockStmt extends Statement, IRegion {
    var Body: List<Statement>
  }

  trait {:compile false} {:extern} DividedBlockStmt extends BlockStmt {
    var BodyInit: List<Statement>
    var SeparatorTok: IToken
    var BodyProper: List<Statement>
  }

  trait {:compile false} {:extern} IfStmt extends Statement {
    var IsBindingGuard: bool
    var Guard: Expression
    var Thn: BlockStmt
    var Els: Statement
  }

  trait {:compile false} {:extern} GuardedAlternative {
    var Tok: IToken
    var IsBindingGuard: bool
    var Guard: Expression
    var Body: List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} AlternativeStmt extends Statement {
    var UsesOptionalBraces: bool
    var Alternatives: List<GuardedAlternative>
  }

  trait {:compile false} {:extern} LoopStmt extends Statement {
    var Invariants: List<AttributedExpression>
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var Mod: Specification<FrameExpression>
  }

  trait {:compile false} {:extern} OneBodyLoopStmt extends LoopStmt {
    var Body: BlockStmt
    var BodySurrogate: WhileStmt_LoopBodySurrogate/*?*/
  }

  trait {:compile false} {:extern} WhileStmt extends OneBodyLoopStmt {
    var Guard: Expression
  }

  trait {:compile false} {:extern} {:extern "WhileStmt.LoopBodySurrogate"} WhileStmt_LoopBodySurrogate {
    var LocalLoopTargets: List<IVariable>
    var UsesHeap: bool
  }

  trait {:compile false} {:extern} RefinedWhileStmt extends WhileStmt {
  }

  trait {:compile false} {:extern} ForLoopStmt extends OneBodyLoopStmt {
    var LoopIndex: BoundVar
    var Start: Expression
    var End: Expression
    var GoingUp: bool
  }

  trait {:compile false} {:extern} AlternativeLoopStmt extends LoopStmt {
    var UsesOptionalBraces: bool
    var Alternatives: List<GuardedAlternative>
  }

  trait {:compile false} {:extern} ForallStmt extends Statement {
    var BoundVars: List<BoundVar>
    var Range: Expression
    var Ens: List<AttributedExpression>
    var Body: Statement
    var ForallExpressions: List<Expression>
    var CanConvert: bool
    var Bounds: List<ComprehensionExpr_BoundedPool>
    var Kind: BodyKind
  }

  trait {:compile false} {:extern} ModifyStmt extends Statement {
    var Mod: Specification<FrameExpression>
    var Body: BlockStmt
  }

  trait {:compile false} {:extern} CalcStmt extends Statement {
    var Lines: List<Expression>
    var Hints: List<BlockStmt>
    var UserSuppliedOp: CalcOp
    var Op: CalcOp
    var StepOps: List<CalcOp>
    var Steps: List<Expression>
    var Result: Expression
    var DefaultOp: CalcOp
  }

  trait {:compile false} {:extern} {:extern "CalcStmt.CalcOp"} CalcStmt_CalcOp {
  }

  trait {:compile false} {:extern} {:extern "CalcStmt.BinaryCalcOp"} CalcStmt_BinaryCalcOp extends CalcOp {
    var Op: BinaryExpr_BinOpcode
  }

  trait {:compile false} {:extern} {:extern "CalcStmt.TernaryCalcOp"} CalcStmt_TernaryCalcOp extends CalcOp {
    var Index: Expression
  }

  trait {:compile false} {:extern} MatchStmt extends Statement {
    var source: Expression
    var cases: List<MatchCaseStmt>
    var Context: MatchingContext
    var MissingCases: List<DatatypeCtor>
    var UsesOptionalBraces: bool
    var OrigUnresolved: MatchStmt
  }

  trait {:compile false} {:extern} MatchCaseStmt extends MatchCase {
    var body: List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} SkeletonStatement extends Statement {
    var S: Statement
    var ConditionEllipsis: IToken
    var BodyEllipsis: IToken
  }

  trait {:compile false} {:extern} TokenWrapper extends IToken {
    var WrappedToken: IToken
  }

  trait {:compile false} {:extern} NestedToken extends TokenWrapper {
    var Inner: IToken
    var Message: string
  }

  trait {:compile false} {:extern} IncludeToken extends TokenWrapper {
    var Include: Include
  }

  trait {:compile false} {:extern} Expression {
    var tok: IToken
    var {:extern "type"} CSharp_type: Type
  }

  trait {:compile false} {:extern} StaticReceiverExpr extends LiteralExpr {
    var UnresolvedType: Type
    var Implicit: bool
    var OriginalResolved: Expression
  }

  trait {:compile false} {:extern} LiteralExpr extends Expression {
    var Value: object
  }

  trait {:compile false} {:extern} CharLiteralExpr extends LiteralExpr {
  }

  trait {:compile false} {:extern} StringLiteralExpr extends LiteralExpr {
    var IsVerbatim: bool
  }

  trait {:compile false} {:extern} DatatypeValue extends Expression {
    var DatatypeName: string
    var MemberName: string
    var Bindings: ActualBindings
    var Ctor: DatatypeCtor
    var InferredTypeArgs: List<Type>
    var IsCoCall: bool
  }

  trait {:compile false} {:extern} ThisExpr extends Expression {
  }

  trait {:compile false} {:extern} ExpressionPair {
    var A: Expression
    var B: Expression
  }

  trait {:compile false} {:extern} ImplicitThisExpr extends ThisExpr {
  }

  trait {:compile false} {:extern} ImplicitThisExpr_ConstructorCall extends ImplicitThisExpr {
  }

  trait {:compile false} {:extern} IdentifierExpr extends Expression {
    var Name: string
    var Var: IVariable
  }

  trait {:compile false} {:extern} AutoGhostIdentifierExpr extends IdentifierExpr {
  }

  trait {:compile false} {:extern} Resolver_IdentifierExpr extends Expression {
    var Decl: TopLevelDecl
    var TypeArgs: List<Type>
  }

  trait {:compile false} {:extern} {:extern "Resolver_IdentifierExpr.ResolverType"} Resolver_IdentifierExpr_ResolverType extends Type {
  }

  trait {:compile false} {:extern} {:extern "Resolver_IdentifierExpr.ResolverType_Module"} Resolver_IdentifierExpr_ResolverType_Module extends ResolverType {
  }

  trait {:compile false} {:extern} {:extern "Resolver_IdentifierExpr.ResolverType_Type"} Resolver_IdentifierExpr_ResolverType_Type extends ResolverType {
  }

  trait {:compile false} {:extern} DisplayExpression extends Expression {
    var Elements: List<Expression>
  }

  trait {:compile false} {:extern} SetDisplayExpr extends DisplayExpression {
    var Finite: bool
  }

  trait {:compile false} {:extern} MultiSetDisplayExpr extends DisplayExpression {
  }

  trait {:compile false} {:extern} MapDisplayExpr extends Expression {
    var Finite: bool
    var Elements: List<ExpressionPair>
  }

  trait {:compile false} {:extern} SeqDisplayExpr extends DisplayExpression {
  }

  trait {:compile false} {:extern} MemberSelectExpr extends Expression {
    var Obj: Expression
    var MemberName: string
    var Member: MemberDecl
    var AtLabel: Label
    var TypeApplication_AtEnclosingClass: List<Type>
    var TypeApplication_JustMember: List<Type>
    var ResolvedOutparameterTypes: List<Type>
  }

  trait {:compile false} {:extern} SeqSelectExpr extends Expression {
    var SelectOne: bool
    var Seq: Expression
    var E0: Expression
    var E1: Expression
  }

  trait {:compile false} {:extern} MultiSelectExpr extends Expression {
    var Array: Expression
    var Indices: List<Expression>
  }

  trait {:compile false} {:extern} SeqUpdateExpr extends Expression {
    var Seq: Expression
    var Index: Expression
    var Value: Expression
    var ResolvedUpdateExpr: Expression
  }

  trait {:compile false} {:extern} ApplyExpr extends Expression {
    var Function: Expression
    var Args: List<Expression>
  }

  trait {:compile false} {:extern} FunctionCallExpr extends Expression {
    var Name: string
    var Receiver: Expression
    var OpenParen: IToken
    var AtLabel: Label
    var Bindings: ActualBindings
    var TypeApplication_AtEnclosingClass: List<Type>
    var TypeApplication_JustFunction: List<Type>
    var IsByMethodCall: bool
    var CoCall: CoCallResolution
    var CoCallHint: string
    var Function: Function
  }

  trait {:compile false} {:extern} SeqConstructionExpr extends Expression {
    var ExplicitElementType: Type
    var N: Expression
    var Initializer: Expression
  }

  trait {:compile false} {:extern} MultiSetFormingExpr extends Expression {
    var E: Expression
  }

  trait {:compile false} {:extern} OldExpr extends Expression {
    var E: Expression
    var At: string/*?*/
    var AtLabel: Label
  }

  trait {:compile false} {:extern} UnchangedExpr extends Expression {
    var Frame: List<FrameExpression>
    var At: string/*?*/
    var AtLabel: Label
  }

  trait {:compile false} {:extern} UnaryExpr extends Expression {
    var E: Expression
  }

  trait {:compile false} {:extern} UnaryOpExpr extends UnaryExpr {
    var Op: UnOpcode
  }

  trait {:compile false} {:extern} FreshExpr extends UnaryOpExpr {
    var At: string/*?*/
    var AtLabel: Label
  }

  trait {:compile false} {:extern} TypeUnaryExpr extends UnaryExpr {
    var ToType: Type
  }

  trait {:compile false} {:extern} ConversionExpr extends TypeUnaryExpr {
  }

  trait {:compile false} {:extern} TypeTestExpr extends TypeUnaryExpr {
  }

  trait {:compile false} {:extern} BinaryExpr extends Expression {
    var Op: BinOpcode
    var {:extern "_theResolvedOp"} CSharp__theResolvedOp: ResolvedOpcode
    var E0: Expression
    var E1: Expression
    var AccumulatesForTailRecursion: AccumulationOperand
  }

  trait {:compile false} {:extern} TernaryExpr extends Expression {
    var Op: TerOpcode
    var E0: Expression
    var E1: Expression
    var E2: Expression
    var PrefixEqUsesNat: bool
  }

  trait {:compile false} {:extern} LetExpr extends Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression {
    var LHSs: List<CasePattern<BoundVar>>
    var RHSs: List<Expression>
    var Body: Expression
    var Exact: bool
    var Attributes: Attributes
    var Constraint_Bounds: List<ComprehensionExpr_BoundedPool>
    var translationDesugaring: Expression
    var lastTranslatorUsed: Translator
    var BodyStartTok: IToken
    var BodyEndTok: IToken
  }

  trait {:compile false} {:extern} LetOrFailExpr extends ConcreteSyntaxExpression {
    var Lhs: CasePattern<BoundVar>
    var Rhs: Expression
    var Body: Expression
  }

  trait {:compile false} {:extern} ComprehensionExpr extends Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression {
    var BoundVars: List<BoundVar>
    var Range: Expression
    var term: Expression
    var BodyStartTok: IToken
    var BodyEndTok: IToken
    var Attributes: Attributes
    var Bounds: List<BoundedPool>
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.BoundedPool"} ComprehensionExpr_BoundedPool {
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.ExactBoundedPool"} ComprehensionExpr_ExactBoundedPool extends BoundedPool {
    var E: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.BoolBoundedPool"} ComprehensionExpr_BoolBoundedPool extends BoundedPool {
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.CharBoundedPool"} ComprehensionExpr_CharBoundedPool extends BoundedPool {
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.AllocFreeBoundedPool"} ComprehensionExpr_AllocFreeBoundedPool extends BoundedPool {
    var Type: Type
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.ExplicitAllocatedBoundedPool"} ComprehensionExpr_ExplicitAllocatedBoundedPool extends BoundedPool {
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool"} ComprehensionExpr_SpecialAllocIndependenceAllocatedBoundedPool extends BoundedPool {
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.IntBoundedPool"} ComprehensionExpr_IntBoundedPool extends BoundedPool {
    var LowerBound: Expression
    var UpperBound: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.CollectionBoundedPool"} ComprehensionExpr_CollectionBoundedPool extends BoundedPool {
    var BoundVariableType: Type
    var CollectionElementType: Type
    var IsFiniteCollection: bool
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.SetBoundedPool"} ComprehensionExpr_SetBoundedPool extends CollectionBoundedPool {
    var Set: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.SubSetBoundedPool"} ComprehensionExpr_SubSetBoundedPool extends BoundedPool {
    var UpperBound: Expression
    var IsFiniteCollection: bool
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.SuperSetBoundedPool"} ComprehensionExpr_SuperSetBoundedPool extends BoundedPool {
    var LowerBound: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.MultiSetBoundedPool"} ComprehensionExpr_MultiSetBoundedPool extends CollectionBoundedPool {
    var MultiSet: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.MapBoundedPool"} ComprehensionExpr_MapBoundedPool extends CollectionBoundedPool {
    var Map: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.SeqBoundedPool"} ComprehensionExpr_SeqBoundedPool extends CollectionBoundedPool {
    var Seq: Expression
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.DatatypeBoundedPool"} ComprehensionExpr_DatatypeBoundedPool extends BoundedPool {
    var Decl: DatatypeDecl
  }

  trait {:compile false} {:extern} {:extern "ComprehensionExpr.DatatypeInclusionBoundedPool"} ComprehensionExpr_DatatypeInclusionBoundedPool extends BoundedPool {
    var IsIndDatatype: bool
  }

  trait {:compile false} {:extern} QuantifierExpr extends ComprehensionExpr, TypeParameter_ParentType {
    var UniqueId: int
    var TypeArgs: List<TypeParameter>
    var currentQuantId: int
    var {:extern "_SplitQuantifier"} CSharp__SplitQuantifier: List<Expression>
  }

  trait {:compile false} {:extern} ForallExpr extends QuantifierExpr {
  }

  trait {:compile false} {:extern} ExistsExpr extends QuantifierExpr {
  }

  trait {:compile false} {:extern} SetComprehension extends ComprehensionExpr {
    var Finite: bool
    var TermIsImplicit: bool
  }

  trait {:compile false} {:extern} MapComprehension extends ComprehensionExpr {
    var Finite: bool
    var TermLeft: Expression
    var ProjectionFunctions: List<Boogie.Function>
  }

  trait {:compile false} {:extern} LambdaExpr extends ComprehensionExpr {
    var Reads: List<FrameExpression>
  }

  trait {:compile false} {:extern} WildcardExpr extends Expression {
  }

  trait {:compile false} {:extern} StmtExpr extends Expression {
    var S: Statement
    var E: Expression
  }

  trait {:compile false} {:extern} ITEExpr extends Expression {
    var IsBindingGuard: bool
    var Test: Expression
    var Thn: Expression
    var Els: Expression
  }

  trait {:compile false} {:extern} MatchExpr extends Expression {
    var source: Expression
    var cases: List<MatchCaseExpr>
    var Context: MatchingContext
    var MissingCases: List<DatatypeCtor>
    var UsesOptionalBraces: bool
    var OrigUnresolved: MatchExpr
  }

  trait {:compile false} {:extern} CasePattern<VT> {
    var tok: IToken
    var Id: string
    var Ctor: DatatypeCtor
    var Var: VT
    var Arguments: List<CasePattern<VT>>
    var Expr: Expression
  }

  trait {:compile false} {:extern} MatchCase {
    var tok: IToken
    var Ctor: DatatypeCtor
    var Arguments: List<BoundVar>
  }

  trait {:compile false} {:extern} MatchCaseExpr extends MatchCase {
    var body: Expression
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} MatchingContext {
  }

  trait {:compile false} {:extern} LitCtx extends MatchingContext {
    var Lit: LiteralExpr
  }

  trait {:compile false} {:extern} HoleCtx extends MatchingContext {
  }

  trait {:compile false} {:extern} ForallCtx extends MatchingContext {
  }

  trait {:compile false} {:extern} IdCtx extends MatchingContext {
    var Id: String
    var Arguments: List<MatchingContext>
  }

  trait {:compile false} {:extern} ExtendedPattern {
    var Tok: IToken
    var IsGhost: bool
  }

  trait {:compile false} {:extern} LitPattern extends ExtendedPattern {
    var OrigLit: Expression
  }

  trait {:compile false} {:extern} IdPattern extends ExtendedPattern {
    var Id: String
    var Type: Type
    var Arguments: List<ExtendedPattern>
    var ResolvedLit: LiteralExpr
  }

  trait {:compile false} {:extern} NestedMatchCase {
    var Tok: IToken
    var Pat: ExtendedPattern
  }

  trait {:compile false} {:extern} NestedMatchCaseExpr extends NestedMatchCase {
    var Body: Expression
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} NestedMatchCaseStmt extends NestedMatchCase {
    var Body: List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} NestedMatchStmt extends ConcreteSyntaxStatement {
    var Source: Expression
    var Cases: List<NestedMatchCaseStmt>
    var UsesOptionalBraces: bool
  }

  trait {:compile false} {:extern} NestedMatchExpr extends ConcreteSyntaxExpression {
    var Source: Expression
    var Cases: List<NestedMatchCaseExpr>
    var UsesOptionalBraces: bool
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} BoxingCastExpr extends Expression {
    var E: Expression
    var FromType: Type
    var ToType: Type
  }

  trait {:compile false} {:extern} UnboxingCastExpr extends Expression {
    var E: Expression
    var FromType: Type
    var ToType: Type
  }

  trait {:compile false} {:extern} AttributedExpression {
    var E: Expression
    var Label: AssertLabel
    var attributes: Attributes
  }

  trait {:compile false} {:extern} FrameExpression {
    var tok: IToken
    var E: Expression
    var FieldName: string
    var Field: Field
  }

  trait {:compile false} {:extern} ConcreteSyntaxExpression extends Expression {
    var ResolvedExpression: Expression
  }

  trait {:compile false} {:extern} ConcreteSyntaxStatement extends Statement {
    var ResolvedStatement: Statement
  }

  trait {:compile false} {:extern} ParensExpression extends ConcreteSyntaxExpression {
    var E: Expression
  }

  trait {:compile false} {:extern} TypeExpr extends ParensExpression {
    var T: Type
  }

  trait {:compile false} {:extern} DatatypeUpdateExpr extends ConcreteSyntaxExpression {
    var Root: Expression
    var Updates: List<Tuple3<IToken, string, Expression>>
    var LegalSourceConstructors: List<DatatypeCtor>
  }

  trait {:compile false} {:extern} AutoGeneratedExpression extends ParensExpression {
  }

  trait {:compile false} {:extern} DefaultValueExpression extends ConcreteSyntaxExpression {
    var Formal: Formal
    var Receiver: Expression
    var SubstMap: Dictionary<IVariable, Expression>
    var TypeMap: Dictionary<TypeParameter, Type>
  }

  trait {:compile false} {:extern} NegationExpression extends ConcreteSyntaxExpression {
    var E: Expression
  }

  trait {:compile false} {:extern} ChainingExpression extends ConcreteSyntaxExpression {
    var Operands: List<Expression>
    var Operators: List<BinaryExpr_BinOpcode>
    var OperatorLocs: List<IToken>
    var PrefixLimits: List<Expression>
    var E: Expression
  }

  trait {:compile false} {:extern} SuffixExpr extends ConcreteSyntaxExpression {
    var Lhs: Expression
  }

  trait {:compile false} {:extern} NameSegment extends ConcreteSyntaxExpression {
    var Name: string
    var OptTypeArguments: List<Type>
  }

  trait {:compile false} {:extern} ExprDotName extends SuffixExpr {
    var SuffixName: string
    var OptTypeArguments: List<Type>
  }

  trait {:compile false} {:extern} ApplySuffix extends SuffixExpr {
    var AtTok: IToken
    var Bindings: ActualBindings
  }

  trait {:compile false} {:extern} Specification<T> {
    var Expressions: List<T>
    var attributes: Attributes
  }

  trait {:compile false} {:extern} BottomUpVisitor {
  }

  trait {:compile false} {:extern} TopDownVisitor<State> {
  }
}
