include "CSharpCompat.dfy"
include "DafnyCompat.dfy"

module {:extern "__AUTOGEN__Microsoft.Dafny"} CSharpDafnyAST {
  import System
  import Microsoft
  import CSharpUtils
  import opened Microsoft.Dafny

  class {:extern "Attributes.MatchingValueOption"} Attributes__MatchingValueOption {
    static const {:extern} Empty: Attributes__MatchingValueOption
    static const {:extern} Bool: Attributes__MatchingValueOption
    static const {:extern} Int: Attributes__MatchingValueOption
    static const {:extern} String: Attributes__MatchingValueOption
    static const {:extern} Expression: Attributes__MatchingValueOption
    function method {:extern} Equals(other: Attributes__MatchingValueOption): bool
  }

  class {:extern "Type.NumericPersuasion"} Type__NumericPersuasion {
    static const {:extern} Int: Type__NumericPersuasion
    static const {:extern} Real: Type__NumericPersuasion
    function method {:extern} Equals(other: Type__NumericPersuasion): bool
  }

  class {:extern "Type.AutoInitInfo"} Type__AutoInitInfo {
    static const {:extern} MaybeEmpty: Type__AutoInitInfo
    static const {:extern} Nonempty: Type__AutoInitInfo
    static const {:extern} CompilableValue: Type__AutoInitInfo
    function method {:extern} Equals(other: Type__AutoInitInfo): bool
  }

  class {:extern "TypeProxy.Family"} TypeProxy__Family {
    static const {:extern} Unknown: TypeProxy__Family
    static const {:extern} Bool: TypeProxy__Family
    static const {:extern} Char: TypeProxy__Family
    static const {:extern} IntLike: TypeProxy__Family
    static const {:extern} RealLike: TypeProxy__Family
    static const {:extern} Ordinal: TypeProxy__Family
    static const {:extern} BitVector: TypeProxy__Family
    static const {:extern} ValueType: TypeProxy__Family
    static const {:extern} Ref: TypeProxy__Family
    static const {:extern} Opaque: TypeProxy__Family
    function method {:extern} Equals(other: TypeProxy__Family): bool
  }

  class {:extern "TypeParameter.TPVarianceSyntax"} TypeParameter__TPVarianceSyntax {
    static const {:extern} NonVariant_Strict: TypeParameter__TPVarianceSyntax
    static const {:extern} NonVariant_Permissive: TypeParameter__TPVarianceSyntax
    static const {:extern} Covariant_Strict: TypeParameter__TPVarianceSyntax
    static const {:extern} Covariant_Permissive: TypeParameter__TPVarianceSyntax
    static const {:extern} Contravariance: TypeParameter__TPVarianceSyntax
    function method {:extern} Equals(other: TypeParameter__TPVarianceSyntax): bool
  }

  class {:extern "TypeParameter.TPVariance"} TypeParameter__TPVariance {
    static const {:extern} Co: TypeParameter__TPVariance
    static const {:extern} Non: TypeParameter__TPVariance
    static const {:extern} Contra: TypeParameter__TPVariance
    function method {:extern} Equals(other: TypeParameter__TPVariance): bool
  }

  class {:extern "TypeParameter.EqualitySupportValue"} TypeParameter__EqualitySupportValue {
    static const {:extern} Required: TypeParameter__EqualitySupportValue
    static const {:extern} InferredRequired: TypeParameter__EqualitySupportValue
    static const {:extern} Unspecified: TypeParameter__EqualitySupportValue
    function method {:extern} Equals(other: TypeParameter__EqualitySupportValue): bool
  }

  class {:extern "IndDatatypeDecl.ES"} IndDatatypeDecl__ES {
    static const {:extern} NotYetComputed: IndDatatypeDecl__ES
    static const {:extern} Never: IndDatatypeDecl__ES
    static const {:extern} ConsultTypeArguments: IndDatatypeDecl__ES
    function method {:extern} Equals(other: IndDatatypeDecl__ES): bool
  }

  class {:extern "SpecialField.ID"} SpecialField__ID {
    static const {:extern} UseIdParam: SpecialField__ID
    static const {:extern} ArrayLength: SpecialField__ID
    static const {:extern} ArrayLengthInt: SpecialField__ID
    static const {:extern} Floor: SpecialField__ID
    static const {:extern "IsLimit"} CSharp_IsLimit: SpecialField__ID
    static const {:extern "IsSucc"} CSharp_IsSucc: SpecialField__ID
    static const {:extern "Offset"} CSharp_Offset: SpecialField__ID
    static const {:extern "IsNat"} CSharp_IsNat: SpecialField__ID
    static const {:extern "Keys"} CSharp_Keys: SpecialField__ID
    static const {:extern "Values"} CSharp_Values: SpecialField__ID
    static const {:extern "Items"} CSharp_Items: SpecialField__ID
    static const {:extern} Reads: SpecialField__ID
    static const {:extern} Modifies: SpecialField__ID
    static const {:extern} New: SpecialField__ID
    function method {:extern} Equals(other: SpecialField__ID): bool
  }

  class {:extern "NativeType.Selection"} NativeType__Selection {
    static const {:extern} Byte: NativeType__Selection
    static const {:extern} SByte: NativeType__Selection
    static const {:extern} UShort: NativeType__Selection
    static const {:extern} Short: NativeType__Selection
    static const {:extern} UInt: NativeType__Selection
    static const {:extern} Int: NativeType__Selection
    static const {:extern} Number: NativeType__Selection
    static const {:extern} ULong: NativeType__Selection
    static const {:extern} Long: NativeType__Selection
    function method {:extern} Equals(other: NativeType__Selection): bool
  }

  class {:extern "SubsetTypeDecl.WKind"} SubsetTypeDecl__WKind {
    static const {:extern} CompiledZero: SubsetTypeDecl__WKind
    static const {:extern} Compiled: SubsetTypeDecl__WKind
    static const {:extern} Ghost: SubsetTypeDecl__WKind
    static const {:extern} OptOut: SubsetTypeDecl__WKind
    static const {:extern} Special: SubsetTypeDecl__WKind
    function method {:extern} Equals(other: SubsetTypeDecl__WKind): bool
  }

  class {:extern "Function.TailStatus"} Function__TailStatus {
    static const {:extern} TriviallyTailRecursive: Function__TailStatus
    static const {:extern} TailRecursive: Function__TailStatus
    static const {:extern} NotTailRecursive: Function__TailStatus
    static const {:extern} Accumulate_Add: Function__TailStatus
    static const {:extern} AccumulateRight_Sub: Function__TailStatus
    static const {:extern} Accumulate_Mul: Function__TailStatus
    static const {:extern} Accumulate_SetUnion: Function__TailStatus
    static const {:extern} AccumulateRight_SetDifference: Function__TailStatus
    static const {:extern} Accumulate_MultiSetUnion: Function__TailStatus
    static const {:extern} AccumulateRight_MultiSetDifference: Function__TailStatus
    static const {:extern} AccumulateLeft_Concat: Function__TailStatus
    static const {:extern} AccumulateRight_Concat: Function__TailStatus
    function method {:extern} Equals(other: Function__TailStatus): bool
  }

  class {:extern "Function.CoCallClusterInvolvement"} Function__CoCallClusterInvolvement {
    static const {:extern} None: Function__CoCallClusterInvolvement
    static const {:extern} IsMutuallyRecursiveTarget: Function__CoCallClusterInvolvement
    static const {:extern} CoRecursiveTargetAllTheWay: Function__CoCallClusterInvolvement
    function method {:extern} Equals(other: Function__CoCallClusterInvolvement): bool
  }

  class {:extern "Predicate.BodyOriginKind"} Predicate__BodyOriginKind {
    static const {:extern} OriginalOrInherited: Predicate__BodyOriginKind
    static const {:extern} DelayedDefinition: Predicate__BodyOriginKind
    static const {:extern} Extension: Predicate__BodyOriginKind
    function method {:extern} Equals(other: Predicate__BodyOriginKind): bool
  }

  class {:extern "ExtremePredicate.KType"} ExtremePredicate__KType {
    static const {:extern} Unspecified: ExtremePredicate__KType
    static const {:extern} Nat: ExtremePredicate__KType
    static const {:extern "ORDINAL"} CSharp_ORDINAL: ExtremePredicate__KType
    function method {:extern} Equals(other: ExtremePredicate__KType): bool
  }

  class {:extern "AssignStmt.NonGhostKind"} AssignStmt__NonGhostKind {
    static const {:extern} IsGhost: AssignStmt__NonGhostKind
    static const {:extern} Variable: AssignStmt__NonGhostKind
    static const {:extern} Field: AssignStmt__NonGhostKind
    static const {:extern} ArrayElement: AssignStmt__NonGhostKind
    function method {:extern} Equals(other: AssignStmt__NonGhostKind): bool
  }

  class {:extern "ForallStmt.BodyKind"} ForallStmt__BodyKind {
    static const {:extern} Assign: ForallStmt__BodyKind
    static const {:extern} Call: ForallStmt__BodyKind
    static const {:extern} Proof: ForallStmt__BodyKind
    function method {:extern} Equals(other: ForallStmt__BodyKind): bool
  }

  class {:extern "FunctionCallExpr.CoCallResolution"} FunctionCallExpr__CoCallResolution {
    static const {:extern} No: FunctionCallExpr__CoCallResolution
    static const {:extern} Yes: FunctionCallExpr__CoCallResolution
    static const {:extern} NoBecauseFunctionHasSideEffects: FunctionCallExpr__CoCallResolution
    static const {:extern} NoBecauseFunctionHasPostcondition: FunctionCallExpr__CoCallResolution
    static const {:extern} NoBecauseRecursiveCallsAreNotAllowedInThisContext: FunctionCallExpr__CoCallResolution
    static const {:extern} NoBecauseIsNotGuarded: FunctionCallExpr__CoCallResolution
    static const {:extern} NoBecauseRecursiveCallsInDestructiveContext: FunctionCallExpr__CoCallResolution
    function method {:extern} Equals(other: FunctionCallExpr__CoCallResolution): bool
  }

  class {:extern "UnaryOpExpr.Opcode"} UnaryOpExpr__Opcode {
    static const {:extern} Not: UnaryOpExpr__Opcode
    static const {:extern} Cardinality: UnaryOpExpr__Opcode
    static const {:extern} Fresh: UnaryOpExpr__Opcode
    static const {:extern} Allocated: UnaryOpExpr__Opcode
    static const {:extern} Lit: UnaryOpExpr__Opcode
    function method {:extern} Equals(other: UnaryOpExpr__Opcode): bool
  }

  class {:extern "BinaryExpr.Opcode"} BinaryExpr__Opcode {
    static const {:extern} Iff: BinaryExpr__Opcode
    static const {:extern} Imp: BinaryExpr__Opcode
    static const {:extern} Exp: BinaryExpr__Opcode
    static const {:extern} And: BinaryExpr__Opcode
    static const {:extern} Or: BinaryExpr__Opcode
    static const {:extern} Eq: BinaryExpr__Opcode
    static const {:extern} Neq: BinaryExpr__Opcode
    static const {:extern} Lt: BinaryExpr__Opcode
    static const {:extern} Le: BinaryExpr__Opcode
    static const {:extern} Ge: BinaryExpr__Opcode
    static const {:extern} Gt: BinaryExpr__Opcode
    static const {:extern} Disjoint: BinaryExpr__Opcode
    static const {:extern} In: BinaryExpr__Opcode
    static const {:extern} NotIn: BinaryExpr__Opcode
    static const {:extern} LeftShift: BinaryExpr__Opcode
    static const {:extern} RightShift: BinaryExpr__Opcode
    static const {:extern} Add: BinaryExpr__Opcode
    static const {:extern} Sub: BinaryExpr__Opcode
    static const {:extern} Mul: BinaryExpr__Opcode
    static const {:extern} Div: BinaryExpr__Opcode
    static const {:extern} Mod: BinaryExpr__Opcode
    static const {:extern} BitwiseAnd: BinaryExpr__Opcode
    static const {:extern} BitwiseOr: BinaryExpr__Opcode
    static const {:extern} BitwiseXor: BinaryExpr__Opcode
    function method {:extern} Equals(other: BinaryExpr__Opcode): bool
  }

  class {:extern "BinaryExpr.ResolvedOpcode"} BinaryExpr__ResolvedOpcode {
    static const {:extern} YetUndetermined: BinaryExpr__ResolvedOpcode
    static const {:extern} Iff: BinaryExpr__ResolvedOpcode
    static const {:extern} Imp: BinaryExpr__ResolvedOpcode
    static const {:extern} And: BinaryExpr__ResolvedOpcode
    static const {:extern} Or: BinaryExpr__ResolvedOpcode
    static const {:extern} EqCommon: BinaryExpr__ResolvedOpcode
    static const {:extern} NeqCommon: BinaryExpr__ResolvedOpcode
    static const {:extern} Lt: BinaryExpr__ResolvedOpcode
    static const {:extern} LessThanLimit: BinaryExpr__ResolvedOpcode
    static const {:extern} Le: BinaryExpr__ResolvedOpcode
    static const {:extern} Ge: BinaryExpr__ResolvedOpcode
    static const {:extern} Gt: BinaryExpr__ResolvedOpcode
    static const {:extern} Add: BinaryExpr__ResolvedOpcode
    static const {:extern} Sub: BinaryExpr__ResolvedOpcode
    static const {:extern} Mul: BinaryExpr__ResolvedOpcode
    static const {:extern} Div: BinaryExpr__ResolvedOpcode
    static const {:extern} Mod: BinaryExpr__ResolvedOpcode
    static const {:extern} LeftShift: BinaryExpr__ResolvedOpcode
    static const {:extern} RightShift: BinaryExpr__ResolvedOpcode
    static const {:extern} BitwiseAnd: BinaryExpr__ResolvedOpcode
    static const {:extern} BitwiseOr: BinaryExpr__ResolvedOpcode
    static const {:extern} BitwiseXor: BinaryExpr__ResolvedOpcode
    static const {:extern} LtChar: BinaryExpr__ResolvedOpcode
    static const {:extern} LeChar: BinaryExpr__ResolvedOpcode
    static const {:extern} GeChar: BinaryExpr__ResolvedOpcode
    static const {:extern} GtChar: BinaryExpr__ResolvedOpcode
    static const {:extern} SetEq: BinaryExpr__ResolvedOpcode
    static const {:extern} SetNeq: BinaryExpr__ResolvedOpcode
    static const {:extern} ProperSubset: BinaryExpr__ResolvedOpcode
    static const {:extern} Subset: BinaryExpr__ResolvedOpcode
    static const {:extern} Superset: BinaryExpr__ResolvedOpcode
    static const {:extern} ProperSuperset: BinaryExpr__ResolvedOpcode
    static const {:extern} Disjoint: BinaryExpr__ResolvedOpcode
    static const {:extern} InSet: BinaryExpr__ResolvedOpcode
    static const {:extern} NotInSet: BinaryExpr__ResolvedOpcode
    static const {:extern} Union: BinaryExpr__ResolvedOpcode
    static const {:extern} Intersection: BinaryExpr__ResolvedOpcode
    static const {:extern} SetDifference: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetEq: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetNeq: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSubset: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSuperset: BinaryExpr__ResolvedOpcode
    static const {:extern} ProperMultiSubset: BinaryExpr__ResolvedOpcode
    static const {:extern} ProperMultiSuperset: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetDisjoint: BinaryExpr__ResolvedOpcode
    static const {:extern} InMultiSet: BinaryExpr__ResolvedOpcode
    static const {:extern} NotInMultiSet: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetUnion: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetIntersection: BinaryExpr__ResolvedOpcode
    static const {:extern} MultiSetDifference: BinaryExpr__ResolvedOpcode
    static const {:extern} SeqEq: BinaryExpr__ResolvedOpcode
    static const {:extern} SeqNeq: BinaryExpr__ResolvedOpcode
    static const {:extern} ProperPrefix: BinaryExpr__ResolvedOpcode
    static const {:extern} Prefix: BinaryExpr__ResolvedOpcode
    static const {:extern} Concat: BinaryExpr__ResolvedOpcode
    static const {:extern} InSeq: BinaryExpr__ResolvedOpcode
    static const {:extern} NotInSeq: BinaryExpr__ResolvedOpcode
    static const {:extern} MapEq: BinaryExpr__ResolvedOpcode
    static const {:extern} MapNeq: BinaryExpr__ResolvedOpcode
    static const {:extern} InMap: BinaryExpr__ResolvedOpcode
    static const {:extern} NotInMap: BinaryExpr__ResolvedOpcode
    static const {:extern} MapMerge: BinaryExpr__ResolvedOpcode
    static const {:extern} MapSubtraction: BinaryExpr__ResolvedOpcode
    static const {:extern} RankLt: BinaryExpr__ResolvedOpcode
    static const {:extern} RankGt: BinaryExpr__ResolvedOpcode
    function method {:extern} Equals(other: BinaryExpr__ResolvedOpcode): bool
  }

  class {:extern "BinaryExpr.AccumulationOperand"} BinaryExpr__AccumulationOperand {
    static const {:extern} None: BinaryExpr__AccumulationOperand
    static const {:extern} Left: BinaryExpr__AccumulationOperand
    static const {:extern} Right: BinaryExpr__AccumulationOperand
    function method {:extern} Equals(other: BinaryExpr__AccumulationOperand): bool
  }

  class {:extern "TernaryExpr.Opcode"} TernaryExpr__Opcode {
    static const {:extern} PrefixEqOp: TernaryExpr__Opcode
    static const {:extern} PrefixNeqOp: TernaryExpr__Opcode
    function method {:extern} Equals(other: TernaryExpr__Opcode): bool
  }

  class {:extern "ComprehensionExpr.BoundedPool.PoolVirtues"} ComprehensionExpr__BoundedPool__PoolVirtues {
    static const {:extern} None: ComprehensionExpr__BoundedPool__PoolVirtues
    static const {:extern} Finite: ComprehensionExpr__BoundedPool__PoolVirtues
    static const {:extern} Enumerable: ComprehensionExpr__BoundedPool__PoolVirtues
    static const {:extern} IndependentOfAlloc: ComprehensionExpr__BoundedPool__PoolVirtues
    static const {:extern} IndependentOfAlloc_or_ExplicitAlloc: ComprehensionExpr__BoundedPool__PoolVirtues
    function method {:extern} Equals(other: ComprehensionExpr__BoundedPool__PoolVirtues): bool
  }

  trait {:compile false} {:extern} Program {
    var FullName: string
    var ModuleSigs: System.Collections.Generic.Dictionary<ModuleDefinition, ModuleSignature>
    var CompileModules: System.Collections.Generic.List<ModuleDefinition>
    var MainMethod: Method
    var DefaultModule: ModuleDecl
    var DefaultModuleDef: ModuleDefinition
    var BuiltIns: BuiltIns
    var reporter: ErrorReporter
  }

  trait {:compile false} {:extern} Include extends System.IComparable {
    var tok: Microsoft.Boogie.IToken
    var includerFilename: string
    var includedFilename: string
    var canonicalPath: string
    var ErrorReported: bool
  }

  trait {:compile false} {:extern} BuiltIns {
    var SystemModule: ModuleDefinition
    var arrayTypeDecls: System.Collections.Generic.Dictionary<int, ClassDecl>
    var ArrowTypeDecls: System.Collections.Generic.Dictionary<int, ArrowTypeDecl>
    var PartialArrowTypeDecls: System.Collections.Generic.Dictionary<int, SubsetTypeDecl>
    var TotalArrowTypeDecls: System.Collections.Generic.Dictionary<int, SubsetTypeDecl>
    var tupleTypeDecls: System.Collections.Generic.Dictionary<System.Collections.Generic.List<bool>, TupleTypeDecl>
    var Bitwidths: System.Collections.Generic.ISet<int>
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
    var Args: System.Collections.Generic.List<Expression>
    var Prev: Attributes
  }

  trait {:compile false} {:extern} AttributesExtensions {
  }

  trait {:compile false} {:extern} UserSuppliedAttributes extends Attributes {
    var tok: Microsoft.Boogie.IToken
    var OpenBrace: Microsoft.Boogie.IToken
    var CloseBrace: Microsoft.Boogie.IToken
    var Recognized: bool
  }

  trait {:compile false} {:extern} Type {
    var Bool: BoolType
    var Char: CharType
    var Int: IntType
    var Real: RealType
    var BigOrdinal: BigOrdinalType
    var scopes: System.Collections.Generic.List<VisibilityScope>
    var scopesEnabled: bool
    var TypeArgs: System.Collections.Generic.List<Type>
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
    var tok: Microsoft.Boogie.IToken
    var Name: string
    var compileName: string
    var ResolvedClass: TopLevelDecl
  }

  trait {:compile false} {:extern} TypeProxy extends Type {
    var T: Type
    var SupertypeConstraints: System.Collections.Generic.List<Resolver__TypeConstraint>
    var SubtypeConstraints: System.Collections.Generic.List<Resolver__TypeConstraint>
    var family: TypeProxy__Family
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
    var tok: Microsoft.Boogie.IToken
    var BodyStartTok: Microsoft.Boogie.IToken
    var BodyEndTok: Microsoft.Boogie.IToken
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
    var parent: TypeParameter__ParentType
    var VarianceSyntax: TypeParameter__TPVarianceSyntax
    var Characteristics: TypeParameter__TypeParameterCharacteristics
    var NecessaryForEqualitySupportOfSurroundingInductiveDatatype: bool
    var PositionalIndex: int
  }

  trait {:compile false} {:extern "TypeParameter.ParentType"} TypeParameter__ParentType {
  }

  trait {:compile false} {:extern "TypeParameter.TypeParameterCharacteristics"} TypeParameter__TypeParameterCharacteristics {
    var EqualitySupport: TypeParameter__EqualitySupportValue
    var AutoInit: Type__AutoInitInfo
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
    var Exports: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var ShadowsLiteralModule: bool
  }

  trait {:compile false} {:extern} AbstractModuleDecl extends ModuleDecl {
    var QId: ModuleQualifiedId
    var Exports: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var CompileRoot: ModuleDecl
    var OriginalSignature: ModuleSignature
  }

  trait {:compile false} {:extern} ModuleExportDecl extends ModuleDecl {
    var IsDefault: bool
    var Exports: System.Collections.Generic.List<ExportSignature>
    var Extends: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var ExtendDecls: System.Collections.Generic.List<ModuleExportDecl>
    var ExportDecls: System.Collections.Generic.HashSet<CSharpUtils.Tuple2<Declaration, bool>>
    var RevealAll: bool
    var ProvideAll: bool
    var ThisScope: VisibilityScope
  }

  trait {:compile false} {:extern} ExportSignature {
    var Tok: Microsoft.Boogie.IToken
    var ClassIdTok: Microsoft.Boogie.IToken
    var Opaque: bool
    var ClassId: string
    var Id: string
    var Decl: Declaration
  }

  trait {:compile false} {:extern} ModuleSignature {
    var VisibilityScope: VisibilityScope
    var TopLevels: System.Collections.Generic.Dictionary<string, TopLevelDecl>
    var ExportSets: System.Collections.Generic.Dictionary<string, ModuleExportDecl>
    var Ctors: System.Collections.Generic.Dictionary<string, CSharpUtils.Tuple2<DatatypeCtor, bool>>
    var StaticMembers: System.Collections.Generic.Dictionary<string, MemberDecl>
    var ModuleDef: ModuleDefinition
    var CompileSignature: ModuleSignature
    var Refines: ModuleSignature
    var IsAbstract: bool
  }

  trait {:compile false} {:extern} ModuleQualifiedId {
    var Path: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var Root: ModuleDecl
    var Decl: ModuleDecl
    var Def: ModuleDefinition
    var Sig: ModuleSignature
  }

  trait {:compile false} {:extern} ModuleDefinition extends INamedRegion, IAttributeBearingDeclaration {
    var tok: Microsoft.Boogie.IToken
    var BodyStartTok: Microsoft.Boogie.IToken
    var BodyEndTok: Microsoft.Boogie.IToken
    var DafnyName: string
    var Name: string
    var PrefixIds: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var EnclosingModule: ModuleDefinition
    var Attributes: Attributes
    var RefinementQId: ModuleQualifiedId
    var SuccessfullyResolved: bool
    var Includes: System.Collections.Generic.List<Include>
    var TopLevelDecls: System.Collections.Generic.List<TopLevelDecl>
    var PrefixNamedModules: System.Collections.Generic.List<CSharpUtils.Tuple2<System.Collections.Generic.List<Microsoft.Boogie.IToken>, LiteralModuleDecl>>
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

  trait {:compile false} {:extern} TopLevelDecl extends Declaration, TypeParameter__ParentType {
    var EnclosingModuleDefinition: ModuleDefinition
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
  }

  trait {:compile false} {:extern} TopLevelDeclWithMembers extends TopLevelDecl {
    var Members: System.Collections.Generic.List<MemberDecl>
    var InheritedMembers: System.Collections.Generic.List<MemberDecl>
    var ParentTraits: System.Collections.Generic.List<Type>
    var ParentFormalTypeParametersToActuals: System.Collections.Generic.Dictionary<TypeParameter, Type>
    var ParentTraitHeads: System.Collections.Generic.List<TraitDecl>
    var ParentTypeInformation: TopLevelDeclWithMembers__InheritanceInformationClass
  }

  trait {:compile false} {:extern "TopLevelDeclWithMembers.InheritanceInformationClass"} TopLevelDeclWithMembers__InheritanceInformationClass {
    var info: System.Collections.Generic.Dictionary<TraitDecl, System.Collections.Generic.List<System.ValueTuple>>
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
    var Ctors: System.Collections.Generic.List<DatatypeCtor>
  }

  trait {:compile false} {:extern} IndDatatypeDecl extends DatatypeDecl, RevealableTypeDecl {
    var GroundingCtor: DatatypeCtor
    var TypeParametersUsedInConstructionByGroundingCtor: array<bool>
    var EqualitySupport: IndDatatypeDecl__ES
  }

  trait {:compile false} {:extern} TupleTypeDecl extends IndDatatypeDecl {
    var ArgumentGhostness: System.Collections.Generic.List<bool>
  }

  trait {:compile false} {:extern} CoDatatypeDecl extends DatatypeDecl {
    var SscRepr: CoDatatypeDecl
  }

  trait {:compile false} {:extern} ValuetypeDecl extends TopLevelDecl {
    var Members: System.Collections.Generic.Dictionary<string, MemberDecl>
    var typeTester: System.Func<Type, bool>
    var typeCreator: System.Func<System.Collections.Generic.List<Type>, Type>
  }

  trait {:compile false} {:extern} DatatypeCtor extends Declaration, TypeParameter__ParentType {
    var Formals: System.Collections.Generic.List<Formal>
    var EnclosingDatatype: DatatypeDecl
    var QueryField: SpecialField
    var Destructors: System.Collections.Generic.List<DatatypeDestructor>
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
    var Ins: System.Collections.Generic.List<Formal>
    var Outs: System.Collections.Generic.List<Formal>
    var Reads: Specification<FrameExpression>
    var Modifies: Specification<FrameExpression>
    var Decreases: Specification<Expression>
    var Requires: System.Collections.Generic.List<AttributedExpression>
    var Ensures: System.Collections.Generic.List<AttributedExpression>
    var YieldRequires: System.Collections.Generic.List<AttributedExpression>
    var YieldEnsures: System.Collections.Generic.List<AttributedExpression>
    var Body: BlockStmt
    var SignatureEllipsis: Microsoft.Boogie.IToken
    var OutsFields: System.Collections.Generic.List<Field>
    var OutsHistoryFields: System.Collections.Generic.List<Field>
    var DecreasesFields: System.Collections.Generic.List<Field>
    var Member_Modifies: SpecialField
    var Member_Reads: SpecialField
    var Member_New: SpecialField
    var Member_Init: Constructor
    var Member_Valid: Predicate
    var Member_MoveNext: Method
    var YieldCountVariable: LocalVariable
    var {:extern "_inferredDecr"} CSharp__inferredDecr: bool
  }

  trait {:compile false} {:extern "IteratorDecl.EverIncreasingType"} IteratorDecl__EverIncreasingType extends BasicType {
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
    var SpecialId: SpecialField__ID
    var IdParam: object
  }

  trait {:compile false} {:extern} DatatypeDestructor extends SpecialField {
    var EnclosingCtors: System.Collections.Generic.List<DatatypeCtor>
    var CorrespondingFormals: System.Collections.Generic.List<Formal>
  }

  trait {:compile false} {:extern} ConstantField extends SpecialField, ICallable {
    var Rhs: Expression
  }

  trait {:compile false} {:extern} OpaqueTypeDecl extends TopLevelDeclWithMembers, TypeParameter__ParentType, RevealableTypeDecl {
    var Characteristics: TypeParameter__TypeParameterCharacteristics
  }

  trait {:compile false} {:extern} RedirectingTypeDecl extends ICallable {
  }

  trait {:compile false} {:extern} NativeType {
    var Name: string
    var LowerBound: int
    var UpperBound: int
    var Bitwidth: int
    var Sel: NativeType__Selection
  }

  trait {:compile false} {:extern} RevealableTypeDeclHelper {
    var tsdMap: System.Collections.Generic.Dictionary<TopLevelDecl, InternalTypeSynonymDecl>
  }

  trait {:compile false} {:extern} RevealableTypeDecl {
  }

  trait {:compile false} {:extern} NewtypeDecl extends TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl {
    var BaseType: Type
    var Var: BoundVar
    var Constraint: Expression
    var WitnessKind: SubsetTypeDecl__WKind
    var Witness: Expression
    var NativeType: NativeType
  }

  trait {:compile false} {:extern} TypeSynonymDeclBase extends TopLevelDecl, RedirectingTypeDecl {
    var Characteristics: TypeParameter__TypeParameterCharacteristics
    var Rhs: Type
  }

  trait {:compile false} {:extern} TypeSynonymDecl extends TypeSynonymDeclBase, RedirectingTypeDecl, RevealableTypeDecl {
  }

  trait {:compile false} {:extern} InternalTypeSynonymDecl extends TypeSynonymDeclBase, RedirectingTypeDecl {
  }

  trait {:compile false} {:extern} SubsetTypeDecl extends TypeSynonymDecl, RedirectingTypeDecl {
    var Var: BoundVar
    var Constraint: Expression
    var WitnessKind: SubsetTypeDecl__WKind
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
    var tok: Microsoft.Boogie.IToken
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
    var FormalParameterName: Microsoft.Boogie.IToken
    var Actual: Expression
    var IsGhost: bool
  }

  trait {:compile false} {:extern} ActualBindings {
    var ArgumentBindings: System.Collections.Generic.List<ActualBinding>
    var arguments: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} Function extends MemberDecl, TypeParameter__ParentType, ICallable {
    var IsRecursive: bool
    var TailRecursion: Function__TailStatus
    var IsFueled: bool
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var Formals: System.Collections.Generic.List<Formal>
    var Result: Formal
    var ResultType: Type
    var Req: System.Collections.Generic.List<AttributedExpression>
    var Reads: System.Collections.Generic.List<FrameExpression>
    var Ens: System.Collections.Generic.List<AttributedExpression>
    var Decreases: Specification<Expression>
    var Body: Expression
    var ByMethodTok: Microsoft.Boogie.IToken
    var ByMethodBody: BlockStmt
    var ByMethodDecl: Method
    var SignatureEllipsis: Microsoft.Boogie.IToken
    var OverriddenFunction: Function
    var containsQuantifier: bool
    var AllCalls: System.Collections.Generic.List<FunctionCallExpr>
    var CoClusterTarget: Function__CoCallClusterInvolvement
    var {:extern "_inferredDecr"} CSharp__inferredDecr: bool
  }

  trait {:compile false} {:extern} Predicate extends Function {
    var BodyOrigin: Predicate__BodyOriginKind
  }

  trait {:compile false} {:extern} PrefixPredicate extends Function {
    var K: Formal
    var ExtremePred: ExtremePredicate
  }

  trait {:compile false} {:extern} ExtremePredicate extends Function {
    var TypeOfK: ExtremePredicate__KType
    var Uses: System.Collections.Generic.List<FunctionCallExpr>
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

  trait {:compile false} {:extern} Method extends MemberDecl, TypeParameter__ParentType, IMethodCodeContext {
    var SignatureEllipsis: Microsoft.Boogie.IToken
    var IsByMethod: bool
    var MustReverify: bool
    var IsEntryPoint: bool
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var Ins: System.Collections.Generic.List<Formal>
    var Outs: System.Collections.Generic.List<Formal>
    var Req: System.Collections.Generic.List<AttributedExpression>
    var Mod: Specification<FrameExpression>
    var Ens: System.Collections.Generic.List<AttributedExpression>
    var Decreases: Specification<Expression>
    var methodBody: BlockStmt
    var IsRecursive: bool
    var IsTailRecursive: bool
    var AssignedAssumptionVariables: System.Collections.Generic.ISet<IVariable>
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
    var TypeOfK: ExtremePredicate__KType
    var PrefixLemma: PrefixLemma
  }

  trait {:compile false} {:extern} LeastLemma extends ExtremeLemma {
  }

  trait {:compile false} {:extern} GreatestLemma extends ExtremeLemma {
  }

  trait {:compile false} {:extern} Statement extends IAttributeBearingDeclaration {
    var Tok: Microsoft.Boogie.IToken
    var EndTok: Microsoft.Boogie.IToken
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
    var Tok: Microsoft.Boogie.IToken
    var Name: string
    var uniqueId: string
  }

  trait {:compile false} {:extern} AssertLabel extends Label {
    var E: Microsoft.Boogie.Expr
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
    var Args: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} RevealStmt extends Statement {
    var Exprs: System.Collections.Generic.List<Expression>
    var LabeledAsserts: System.Collections.Generic.List<AssertLabel>
    var ResolvedStatements: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} BreakStmt extends Statement {
    var TargetLabel: Microsoft.Boogie.IToken
    var BreakCount: int
    var TargetStmt: Statement
  }

  trait {:compile false} {:extern} ProduceStmt extends Statement {
    var rhss: System.Collections.Generic.List<AssignmentRhs>
    var hiddenUpdate: UpdateStmt
  }

  trait {:compile false} {:extern} ReturnStmt extends ProduceStmt {
    var ReverifyPost: bool
  }

  trait {:compile false} {:extern} YieldStmt extends ProduceStmt {
  }

  trait {:compile false} {:extern} AssignmentRhs {
    var Tok: Microsoft.Boogie.IToken
    var attributes: Attributes
  }

  trait {:compile false} {:extern} ExprRhs extends AssignmentRhs {
    var Expr: Expression
  }

  trait {:compile false} {:extern} TypeRhs extends AssignmentRhs {
    var EType: Type
    var ArrayDimensions: System.Collections.Generic.List<Expression>
    var ElementInit: Expression
    var InitDisplay: System.Collections.Generic.List<Expression>
    var Bindings: ActualBindings
    var Path: Type
    var InitCall: CallStmt
    var Type: Type
  }

  trait {:compile false} {:extern} HavocRhs extends AssignmentRhs {
  }

  trait {:compile false} {:extern} VarDeclStmt extends Statement {
    var Locals: System.Collections.Generic.List<LocalVariable>
    var Update: ConcreteUpdateStatement
  }

  trait {:compile false} {:extern} VarDeclPattern extends Statement {
    var LHS: CasePattern<LocalVariable>
    var RHS: Expression
    var HasGhostModifier: bool
  }

  trait {:compile false} {:extern} ConcreteUpdateStatement extends Statement {
    var Lhss: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} AssignSuchThatStmt extends ConcreteUpdateStatement {
    var Expr: Expression
    var AssumeToken: Microsoft.Boogie.IToken
    var Bounds: System.Collections.Generic.List<ComprehensionExpr__BoundedPool>
    var MissingBounds: System.Collections.Generic.List<IVariable>
  }

  trait {:compile false} {:extern "AssignSuchThatStmt.WiggleWaggleBound"} AssignSuchThatStmt__WiggleWaggleBound extends ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern} UpdateStmt extends ConcreteUpdateStatement {
    var Rhss: System.Collections.Generic.List<AssignmentRhs>
    var CanMutateKnownState: bool
    var OriginalInitialLhs: Expression
    var ResolvedStatements: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} AssignOrReturnStmt extends ConcreteUpdateStatement {
    var Rhs: Expression
    var Rhss: System.Collections.Generic.List<AssignmentRhs>
    var KeywordToken: Microsoft.Boogie.IToken
    var ResolvedStatements: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} AssignStmt extends Statement {
    var Lhs: Expression
    var Rhs: AssignmentRhs
  }

  trait {:compile false} {:extern} LocalVariable extends IVariable, IAttributeBearingDeclaration {
    var Tok: Microsoft.Boogie.IToken
    var EndTok: Microsoft.Boogie.IToken
    var name: string
    var Attributes: Attributes
    var IsGhost: bool
    var uniqueName: string
    var compileName: string
    var OptionalType: Type
    var {:extern "type"} CSharp_type: Type
  }

  trait {:compile false} {:extern} CallStmt extends Statement {
    var Lhs: System.Collections.Generic.List<Expression>
    var MethodSelect: MemberSelectExpr
    var Bindings: ActualBindings
    var OriginalInitialLhs: Expression
  }

  trait {:compile false} {:extern} BlockStmt extends Statement, IRegion {
    var Body: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} DividedBlockStmt extends BlockStmt {
    var BodyInit: System.Collections.Generic.List<Statement>
    var SeparatorTok: Microsoft.Boogie.IToken
    var BodyProper: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} IfStmt extends Statement {
    var IsBindingGuard: bool
    var Guard: Expression
    var Thn: BlockStmt
    var Els: Statement
  }

  trait {:compile false} {:extern} GuardedAlternative {
    var Tok: Microsoft.Boogie.IToken
    var IsBindingGuard: bool
    var Guard: Expression
    var Body: System.Collections.Generic.List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} AlternativeStmt extends Statement {
    var UsesOptionalBraces: bool
    var Alternatives: System.Collections.Generic.List<GuardedAlternative>
  }

  trait {:compile false} {:extern} LoopStmt extends Statement {
    var Invariants: System.Collections.Generic.List<AttributedExpression>
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var Mod: Specification<FrameExpression>
  }

  trait {:compile false} {:extern} OneBodyLoopStmt extends LoopStmt {
    var Body: BlockStmt
    var BodySurrogate: WhileStmt__LoopBodySurrogate
  }

  trait {:compile false} {:extern} WhileStmt extends OneBodyLoopStmt {
    var Guard: Expression
  }

  trait {:compile false} {:extern "WhileStmt.LoopBodySurrogate"} WhileStmt__LoopBodySurrogate {
    var LocalLoopTargets: System.Collections.Generic.List<IVariable>
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
    var Alternatives: System.Collections.Generic.List<GuardedAlternative>
  }

  trait {:compile false} {:extern} ForallStmt extends Statement {
    var BoundVars: System.Collections.Generic.List<BoundVar>
    var Range: Expression
    var Ens: System.Collections.Generic.List<AttributedExpression>
    var Body: Statement
    var ForallExpressions: System.Collections.Generic.List<Expression>
    var CanConvert: bool
    var Bounds: System.Collections.Generic.List<ComprehensionExpr__BoundedPool>
    var Kind: ForallStmt__BodyKind
  }

  trait {:compile false} {:extern} ModifyStmt extends Statement {
    var Mod: Specification<FrameExpression>
    var Body: BlockStmt
  }

  trait {:compile false} {:extern} CalcStmt extends Statement {
    var Lines: System.Collections.Generic.List<Expression>
    var Hints: System.Collections.Generic.List<BlockStmt>
    var UserSuppliedOp: CalcStmt__CalcOp
    var Op: CalcStmt__CalcOp
    var StepOps: System.Collections.Generic.List<CalcStmt__CalcOp>
    var Steps: System.Collections.Generic.List<Expression>
    var Result: Expression
    var DefaultOp: CalcStmt__CalcOp
  }

  trait {:compile false} {:extern "CalcStmt.CalcOp"} CalcStmt__CalcOp {
  }

  trait {:compile false} {:extern "CalcStmt.BinaryCalcOp"} CalcStmt__BinaryCalcOp extends CalcStmt__CalcOp {
    var Op: BinaryExpr__Opcode
  }

  trait {:compile false} {:extern "CalcStmt.TernaryCalcOp"} CalcStmt__TernaryCalcOp extends CalcStmt__CalcOp {
    var Index: Expression
  }

  trait {:compile false} {:extern} MatchStmt extends Statement {
    var source: Expression
    var cases: System.Collections.Generic.List<MatchCaseStmt>
    var Context: MatchingContext
    var MissingCases: System.Collections.Generic.List<DatatypeCtor>
    var UsesOptionalBraces: bool
    var OrigUnresolved: MatchStmt
  }

  trait {:compile false} {:extern} MatchCaseStmt extends MatchCase {
    var body: System.Collections.Generic.List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} SkeletonStatement extends Statement {
    var S: Statement
    var ConditionEllipsis: Microsoft.Boogie.IToken
    var BodyEllipsis: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} TokenWrapper extends Microsoft.Boogie.IToken {
    var WrappedToken: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} NestedToken extends TokenWrapper {
    var Inner: Microsoft.Boogie.IToken
    var Message: string
  }

  trait {:compile false} {:extern} IncludeToken extends TokenWrapper {
    var Include: Include
  }

  trait {:compile false} {:extern} Expression {
    var tok: Microsoft.Boogie.IToken
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
    var InferredTypeArgs: System.Collections.Generic.List<Type>
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
    var TypeArgs: System.Collections.Generic.List<Type>
  }

  trait {:compile false} {:extern "Resolver_IdentifierExpr.ResolverType"} Resolver_IdentifierExpr__ResolverType extends Type {
  }

  trait {:compile false} {:extern "Resolver_IdentifierExpr.ResolverType_Module"} Resolver_IdentifierExpr__ResolverType_Module extends Resolver_IdentifierExpr__ResolverType {
  }

  trait {:compile false} {:extern "Resolver_IdentifierExpr.ResolverType_Type"} Resolver_IdentifierExpr__ResolverType_Type extends Resolver_IdentifierExpr__ResolverType {
  }

  trait {:compile false} {:extern} DisplayExpression extends Expression {
    var Elements: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} SetDisplayExpr extends DisplayExpression {
    var Finite: bool
  }

  trait {:compile false} {:extern} MultiSetDisplayExpr extends DisplayExpression {
  }

  trait {:compile false} {:extern} MapDisplayExpr extends Expression {
    var Finite: bool
    var Elements: System.Collections.Generic.List<ExpressionPair>
  }

  trait {:compile false} {:extern} SeqDisplayExpr extends DisplayExpression {
  }

  trait {:compile false} {:extern} MemberSelectExpr extends Expression {
    var Obj: Expression
    var MemberName: string
    var Member: MemberDecl
    var AtLabel: Label
    var TypeApplication_AtEnclosingClass: System.Collections.Generic.List<Type>
    var TypeApplication_JustMember: System.Collections.Generic.List<Type>
    var ResolvedOutparameterTypes: System.Collections.Generic.List<Type>
  }

  trait {:compile false} {:extern} SeqSelectExpr extends Expression {
    var SelectOne: bool
    var Seq: Expression
    var E0: Expression
    var E1: Expression
  }

  trait {:compile false} {:extern} MultiSelectExpr extends Expression {
    var Array: Expression
    var Indices: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} SeqUpdateExpr extends Expression {
    var Seq: Expression
    var Index: Expression
    var Value: Expression
    var ResolvedUpdateExpr: Expression
  }

  trait {:compile false} {:extern} ApplyExpr extends Expression {
    var Function: Expression
    var Args: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} FunctionCallExpr extends Expression {
    var Name: string
    var Receiver: Expression
    var OpenParen: Microsoft.Boogie.IToken
    var AtLabel: Label
    var Bindings: ActualBindings
    var TypeApplication_AtEnclosingClass: System.Collections.Generic.List<Type>
    var TypeApplication_JustFunction: System.Collections.Generic.List<Type>
    var IsByMethodCall: bool
    var CoCall: FunctionCallExpr__CoCallResolution
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
    var At: string
    var AtLabel: Label
  }

  trait {:compile false} {:extern} UnchangedExpr extends Expression {
    var Frame: System.Collections.Generic.List<FrameExpression>
    var At: string
    var AtLabel: Label
  }

  trait {:compile false} {:extern} UnaryExpr extends Expression {
    var E: Expression
  }

  trait {:compile false} {:extern} UnaryOpExpr extends UnaryExpr {
    var Op: UnaryOpExpr__Opcode
  }

  trait {:compile false} {:extern} FreshExpr extends UnaryOpExpr {
    var At: string
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
    var Op: BinaryExpr__Opcode
    var {:extern "_theResolvedOp"} CSharp__theResolvedOp: BinaryExpr__ResolvedOpcode
    var E0: Expression
    var E1: Expression
    var AccumulatesForTailRecursion: BinaryExpr__AccumulationOperand
  }

  trait {:compile false} {:extern} TernaryExpr extends Expression {
    var Op: TernaryExpr__Opcode
    var E0: Expression
    var E1: Expression
    var E2: Expression
    var PrefixEqUsesNat: bool
  }

  trait {:compile false} {:extern} LetExpr extends Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression {
    var LHSs: System.Collections.Generic.List<CasePattern<BoundVar>>
    var RHSs: System.Collections.Generic.List<Expression>
    var Body: Expression
    var Exact: bool
    var Attributes: Attributes
    var Constraint_Bounds: System.Collections.Generic.List<ComprehensionExpr__BoundedPool>
    var translationDesugaring: Expression
    var lastTranslatorUsed: Translator
    var BodyStartTok: Microsoft.Boogie.IToken
    var BodyEndTok: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} LetOrFailExpr extends ConcreteSyntaxExpression {
    var Lhs: CasePattern<BoundVar>
    var Rhs: Expression
    var Body: Expression
  }

  trait {:compile false} {:extern} ComprehensionExpr extends Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression {
    var BoundVars: System.Collections.Generic.List<BoundVar>
    var Range: Expression
    var term: Expression
    var BodyStartTok: Microsoft.Boogie.IToken
    var BodyEndTok: Microsoft.Boogie.IToken
    var Attributes: Attributes
    var Bounds: System.Collections.Generic.List<ComprehensionExpr__BoundedPool>
  }

  trait {:compile false} {:extern "ComprehensionExpr.BoundedPool"} ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern "ComprehensionExpr.ExactBoundedPool"} ComprehensionExpr__ExactBoundedPool extends ComprehensionExpr__BoundedPool {
    var E: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.BoolBoundedPool"} ComprehensionExpr__BoolBoundedPool extends ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern "ComprehensionExpr.CharBoundedPool"} ComprehensionExpr__CharBoundedPool extends ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern "ComprehensionExpr.AllocFreeBoundedPool"} ComprehensionExpr__AllocFreeBoundedPool extends ComprehensionExpr__BoundedPool {
    var Type: Type
  }

  trait {:compile false} {:extern "ComprehensionExpr.ExplicitAllocatedBoundedPool"} ComprehensionExpr__ExplicitAllocatedBoundedPool extends ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern "ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool"} ComprehensionExpr__SpecialAllocIndependenceAllocatedBoundedPool extends ComprehensionExpr__BoundedPool {
  }

  trait {:compile false} {:extern "ComprehensionExpr.IntBoundedPool"} ComprehensionExpr__IntBoundedPool extends ComprehensionExpr__BoundedPool {
    var LowerBound: Expression
    var UpperBound: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.CollectionBoundedPool"} ComprehensionExpr__CollectionBoundedPool extends ComprehensionExpr__BoundedPool {
    var BoundVariableType: Type
    var CollectionElementType: Type
    var IsFiniteCollection: bool
  }

  trait {:compile false} {:extern "ComprehensionExpr.SetBoundedPool"} ComprehensionExpr__SetBoundedPool extends ComprehensionExpr__CollectionBoundedPool {
    var Set: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.SubSetBoundedPool"} ComprehensionExpr__SubSetBoundedPool extends ComprehensionExpr__BoundedPool {
    var UpperBound: Expression
    var IsFiniteCollection: bool
  }

  trait {:compile false} {:extern "ComprehensionExpr.SuperSetBoundedPool"} ComprehensionExpr__SuperSetBoundedPool extends ComprehensionExpr__BoundedPool {
    var LowerBound: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.MultiSetBoundedPool"} ComprehensionExpr__MultiSetBoundedPool extends ComprehensionExpr__CollectionBoundedPool {
    var MultiSet: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.MapBoundedPool"} ComprehensionExpr__MapBoundedPool extends ComprehensionExpr__CollectionBoundedPool {
    var Map: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.SeqBoundedPool"} ComprehensionExpr__SeqBoundedPool extends ComprehensionExpr__CollectionBoundedPool {
    var Seq: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.DatatypeBoundedPool"} ComprehensionExpr__DatatypeBoundedPool extends ComprehensionExpr__BoundedPool {
    var Decl: DatatypeDecl
  }

  trait {:compile false} {:extern "ComprehensionExpr.DatatypeInclusionBoundedPool"} ComprehensionExpr__DatatypeInclusionBoundedPool extends ComprehensionExpr__BoundedPool {
    var IsIndDatatype: bool
  }

  trait {:compile false} {:extern} QuantifierExpr extends ComprehensionExpr, TypeParameter__ParentType {
    var UniqueId: int
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var currentQuantId: int
    var {:extern "_SplitQuantifier"} CSharp__SplitQuantifier: System.Collections.Generic.List<Expression>
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
    var ProjectionFunctions: System.Collections.Generic.List<Microsoft.Boogie.Function>
  }

  trait {:compile false} {:extern} LambdaExpr extends ComprehensionExpr {
    var Reads: System.Collections.Generic.List<FrameExpression>
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
    var cases: System.Collections.Generic.List<MatchCaseExpr>
    var Context: MatchingContext
    var MissingCases: System.Collections.Generic.List<DatatypeCtor>
    var UsesOptionalBraces: bool
    var OrigUnresolved: MatchExpr
  }

  trait {:compile false} {:extern} CasePattern<VT> {
    var tok: Microsoft.Boogie.IToken
    var Id: string
    var Ctor: DatatypeCtor
    var Var: VT
    var Arguments: System.Collections.Generic.List<CasePattern<VT>>
    var Expr: Expression
  }

  trait {:compile false} {:extern} MatchCase {
    var tok: Microsoft.Boogie.IToken
    var Ctor: DatatypeCtor
    var Arguments: System.Collections.Generic.List<BoundVar>
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
    var Id: System.String
    var Arguments: System.Collections.Generic.List<MatchingContext>
  }

  trait {:compile false} {:extern} ExtendedPattern {
    var Tok: Microsoft.Boogie.IToken
    var IsGhost: bool
  }

  trait {:compile false} {:extern} LitPattern extends ExtendedPattern {
    var OrigLit: Expression
  }

  trait {:compile false} {:extern} IdPattern extends ExtendedPattern {
    var Id: System.String
    var Type: Type
    var Arguments: System.Collections.Generic.List<ExtendedPattern>
    var ResolvedLit: LiteralExpr
  }

  trait {:compile false} {:extern} NestedMatchCase {
    var Tok: Microsoft.Boogie.IToken
    var Pat: ExtendedPattern
  }

  trait {:compile false} {:extern} NestedMatchCaseExpr extends NestedMatchCase {
    var Body: Expression
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} NestedMatchCaseStmt extends NestedMatchCase {
    var Body: System.Collections.Generic.List<Statement>
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} NestedMatchStmt extends ConcreteSyntaxStatement {
    var Source: Expression
    var Cases: System.Collections.Generic.List<NestedMatchCaseStmt>
    var UsesOptionalBraces: bool
  }

  trait {:compile false} {:extern} NestedMatchExpr extends ConcreteSyntaxExpression {
    var Source: Expression
    var Cases: System.Collections.Generic.List<NestedMatchCaseExpr>
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
    var tok: Microsoft.Boogie.IToken
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
    var Updates: System.Collections.Generic.List<CSharpUtils.Tuple3<Microsoft.Boogie.IToken, string, Expression>>
    var LegalSourceConstructors: System.Collections.Generic.List<DatatypeCtor>
  }

  trait {:compile false} {:extern} AutoGeneratedExpression extends ParensExpression {
  }

  trait {:compile false} {:extern} DefaultValueExpression extends ConcreteSyntaxExpression {
    var Formal: Formal
    var Receiver: Expression
    var SubstMap: System.Collections.Generic.Dictionary<IVariable, Expression>
    var TypeMap: System.Collections.Generic.Dictionary<TypeParameter, Type>
  }

  trait {:compile false} {:extern} NegationExpression extends ConcreteSyntaxExpression {
    var E: Expression
  }

  trait {:compile false} {:extern} ChainingExpression extends ConcreteSyntaxExpression {
    var Operands: System.Collections.Generic.List<Expression>
    var Operators: System.Collections.Generic.List<BinaryExpr__Opcode>
    var OperatorLocs: System.Collections.Generic.List<Microsoft.Boogie.IToken>
    var PrefixLimits: System.Collections.Generic.List<Expression>
    var E: Expression
  }

  trait {:compile false} {:extern} SuffixExpr extends ConcreteSyntaxExpression {
    var Lhs: Expression
  }

  trait {:compile false} {:extern} NameSegment extends ConcreteSyntaxExpression {
    var Name: string
    var OptTypeArguments: System.Collections.Generic.List<Type>
  }

  trait {:compile false} {:extern} ExprDotName extends SuffixExpr {
    var SuffixName: string
    var OptTypeArguments: System.Collections.Generic.List<Type>
  }

  trait {:compile false} {:extern} ApplySuffix extends SuffixExpr {
    var AtTok: Microsoft.Boogie.IToken
    var Bindings: ActualBindings
  }

  trait {:compile false} {:extern} Specification<T> {
    var Expressions: System.Collections.Generic.List<T>
    var attributes: Attributes
  }

  trait {:compile false} {:extern} BottomUpVisitor {
  }

  trait {:compile false} {:extern} TopDownVisitor<State> {
  }
}
