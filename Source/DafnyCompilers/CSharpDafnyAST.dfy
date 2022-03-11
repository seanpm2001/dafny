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
    var Name: string
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
    var {:extern "AllBoundVars"} Interface_AllBoundVars: System.Collections.Generic.IEnumerable<BoundVar> // interface property
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
    var IsBoolType: bool
    var IsCharType: bool
    var IsIntegerType: bool
    var IsRealType: bool
    var IsBigOrdinalType: bool
    var IsBitVectorType: bool
    var AsBitVectorType: BitvectorType
    var IsNonempty: bool
    var HasCompilableValue: bool
    var HasFinitePossibleValues: bool
    var IsAllocFree: bool
    var AsCollectionType: CollectionType
    var AsSetType: SetType
    var AsMultiSetType: MultiSetType
    var AsSeqType: SeqType
    var AsMapType: MapType
    var IsRefType: bool
    var IsTopLevelTypeWithMembers: bool
    var AsTopLevelTypeWithMembers: TopLevelDeclWithMembers
    var AsTopLevelTypeWithMembersBypassInternalSynonym: TopLevelDeclWithMembers
    var IsObjectQ: bool
    var IsObject: bool
    var IsNonNullRefType: bool
    var AsNonNullRefType: UserDefinedType
    var IsTraitType: bool
    var AsTraitType: TraitDecl
    var AsSubsetType: SubsetTypeDecl
    var IsArrayType: bool
    var AsArrayType: ArrayClassDecl
    var IsBuiltinArrowType: bool
    var IsArrowTypeWithoutReadEffects: bool
    var IsArrowTypeWithoutPreconditions: bool
    var IsArrowType: bool
    var AsArrowType: ArrowType
    var IsMapType: bool
    var IsIMapType: bool
    var IsISetType: bool
    var AsNewtype: NewtypeDecl
    var AsTypeSynonym: TypeSynonymDecl
    var AsInternalTypeSynonym: InternalTypeSynonymDecl
    var AsRedirectingType: RedirectingTypeDecl
    var AsRevealableType: RevealableTypeDecl
    var IsRevealableType: bool
    var IsDatatype: bool
    var AsDatatype: DatatypeDecl
    var IsIndDatatype: bool
    var AsIndDatatype: IndDatatypeDecl
    var IsCoDatatype: bool
    var AsCoDatatype: CoDatatypeDecl
    var InvolvesCoDatatype: bool
    var IsTypeParameter: bool
    var IsInternalTypeSynonym: bool
    var AsTypeParameter: TypeParameter
    var IsOpaqueType: bool
    var AsOpaqueType: OpaqueTypeDecl
    var SupportsEquality: bool
    var MayInvolveReferences: bool
    var IsOrdered: bool
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
    var Args: System.Collections.Generic.List<Type>
    var Result: Type
    var Arity: int
    // var SupportsEquality: bool // exists in ancestor
  }

  trait {:compile false} {:extern} CollectionType extends NonProxyType {
    var arg: Type
    var CollectionTypeName: string
    var Arg: Type
    // var MayInvolveReferences: bool // exists in ancestor
  }

  trait {:compile false} {:extern} SetType extends CollectionType {
    var finite: bool
    var Finite: bool
    // var CollectionTypeName: string // exists in ancestor
    // var SupportsEquality: bool // exists in ancestor
  }

  trait {:compile false} {:extern} MultiSetType extends CollectionType {
    // var CollectionTypeName: string // exists in ancestor
    // var SupportsEquality: bool // exists in ancestor
  }

  trait {:compile false} {:extern} SeqType extends CollectionType {
    // var CollectionTypeName: string // exists in ancestor
    // var SupportsEquality: bool // exists in ancestor
  }

  trait {:compile false} {:extern} MapType extends CollectionType {
    var finite: bool
    var range: Type
    var Finite: bool
    var Range: Type
    var Domain: Type
    // var CollectionTypeName: string // exists in ancestor
    // var SupportsEquality: bool // exists in ancestor
    // var MayInvolveReferences: bool // exists in ancestor
  }

  trait {:compile false} {:extern} UserDefinedType extends NonProxyType {
    var NamePath: Expression
    var tok: Microsoft.Boogie.IToken
    var Name: string
    var compileName: string
    var ResolvedClass: TopLevelDecl
    var FullName: string
    var CompileName: string
    var FullCompanionCompileName: string
    // var SupportsEquality: bool // exists in ancestor
    // var MayInvolveReferences: bool // exists in ancestor
  }

  trait {:compile false} {:extern} TypeProxy extends Type {
    var T: Type
    var SupertypeConstraints: System.Collections.Generic.List<Resolver__TypeConstraint>
    var SubtypeConstraints: System.Collections.Generic.List<Resolver__TypeConstraint>
    var family: TypeProxy__Family
    var {:extern "_id"} CSharp__id: int
    var id: int
    var Supertypes: System.Collections.Generic.IEnumerable<Type>
    var SupertypesKeepConstraints: System.Collections.Generic.IEnumerable<Type>
    var Subtypes: System.Collections.Generic.IEnumerable<Type>
    var SubtypesKeepConstraints: System.Collections.Generic.IEnumerable<Type>
    // var SupportsEquality: bool // exists in ancestor
    // var MayInvolveReferences: bool // exists in ancestor
  }

  trait {:compile false} {:extern} InferredTypeProxy extends TypeProxy {
    var KeepConstraints: bool
  }

  trait {:compile false} {:extern} ParamTypeProxy extends TypeProxy {
    var orig: TypeParameter
  }

  trait {:compile false} {:extern} IRegion {
    var {:extern "BodyStartTok"} Interface_BodyStartTok: Microsoft.Boogie.IToken // interface property
    var {:extern "BodyEndTok"} Interface_BodyEndTok: Microsoft.Boogie.IToken // interface property
  }

  trait {:compile false} {:extern} INamedRegion extends IRegion {
    var {:extern "RegionName"} Interface_RegionName: string // interface property
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
    // var BodyStartTok: Microsoft.Boogie.IToken // explicit interface
    // var BodyEndTok: Microsoft.Boogie.IToken // explicit interface
    // var RegionName: string // explicit interface
    var ScopeIsInherited: bool
    var CompileName: string
  }

  trait {:compile false} {:extern} TypeParameter extends TopLevelDecl {
    var parent: TypeParameter__ParentType
    var VarianceSyntax: TypeParameter__TPVarianceSyntax
    var Characteristics: TypeParameter__TypeParameterCharacteristics
    var NecessaryForEqualitySupportOfSurroundingInductiveDatatype: bool
    var PositionalIndex: int
    // var WhatKind: string // exists in ancestor
    var Parent: TypeParameter__ParentType
    // var CompileName: string // exists in ancestor
    var Variance: TypeParameter__TPVariance
    var StrictVariance: bool
    var SupportsEquality: bool
    var IsToplevelScope: bool
    // var FullName: string // exists in ancestor
  }

  trait {:compile false} {:extern "TypeParameter.ParentType"} TypeParameter__ParentType {
    var {:extern "FullName"} Interface_FullName: string // interface property
  }

  trait {:compile false} {:extern "TypeParameter.TypeParameterCharacteristics"} TypeParameter__TypeParameterCharacteristics {
    var EqualitySupport: TypeParameter__EqualitySupportValue
    var AutoInit: Type__AutoInitInfo
    var ContainsNoReferenceTypes: bool
    var HasCompiledValue: bool
    var IsNonempty: bool
  }

  trait {:compile false} {:extern} ModuleDecl extends TopLevelDecl {
    var Signature: ModuleSignature
    var Height: int
    var Opened: bool
    // var WhatKind: string // exists in ancestor
    var ResolvedHash: System.Nullable
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
    var ResolvedHash: System.Nullable
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
    var FullDafnyName: string
    var FullName: string
    // var BodyStartTok: Microsoft.Boogie.IToken // explicit interface
    // var BodyEndTok: Microsoft.Boogie.IToken // explicit interface
    // var RegionName: string // explicit interface
    var ResolvedHash: System.Nullable
    var VisibilityScope: VisibilityScope
    var IsDefaultModule: bool
    var CompileName: string
    var RefinementCompileName: string
  }

  trait {:compile false} {:extern} DefaultModuleDecl extends ModuleDefinition {
    // var IsDefaultModule: bool // exists in ancestor
  }

  trait {:compile false} {:extern} TopLevelDecl extends Declaration, TypeParameter__ParentType {
    var EnclosingModuleDefinition: ModuleDefinition
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var WhatKind: string
    var FullDafnyName: string
    var FullName: string
    var FullSanitizedName: string
    var FullSanitizedRefinementName: string
    var FullCompileName: string
    var ViewAsClass: TopLevelDecl
    var AllowsAllocation: bool
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
    // var WhatKind: string // exists in ancestor
    var IsParent: bool
  }

  trait {:compile false} {:extern} ClassDecl extends TopLevelDeclWithMembers, RevealableTypeDecl {
    var HasConstructor: bool
    var NonNullTypeDecl: NonNullTypeDecl
    // var WhatKind: string // exists in ancestor
    var IsDefaultClass: bool
    var IsObjectTrait: bool
    // var AsTopLevelDecl: TopLevelDecl // explicit interface
  }

  trait {:compile false} {:extern} DefaultClassDecl extends ClassDecl {
    // var IsDefaultClass: bool // exists in ancestor
  }

  trait {:compile false} {:extern} ArrayClassDecl extends ClassDecl {
    var Dims: int
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} ArrowTypeDecl extends ClassDecl {
    var Arity: int
    var Requires: Function
    var Reads: Function
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} DatatypeDecl extends TopLevelDeclWithMembers, RevealableTypeDecl, ICallable {
    var Ctors: System.Collections.Generic.List<DatatypeCtor>
    var HasFinitePossibleValues: bool
    var IsRecordType: bool
    // var AsTopLevelDecl: TopLevelDecl // explicit interface
    // var IsGhost: bool // explicit interface
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // exists in ancestor
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    // var AllowsNontermination: bool // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
  }

  trait {:compile false} {:extern} IndDatatypeDecl extends DatatypeDecl, RevealableTypeDecl {
    var GroundingCtor: DatatypeCtor
    var TypeParametersUsedInConstructionByGroundingCtor: array<bool>
    var EqualitySupport: IndDatatypeDecl__ES
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} TupleTypeDecl extends IndDatatypeDecl {
    var ArgumentGhostness: System.Collections.Generic.List<bool>
    var Dims: int
    var NonGhostDims: int
    // var CompileName: string // exists in ancestor
  }

  trait {:compile false} {:extern} CoDatatypeDecl extends DatatypeDecl {
    var SscRepr: CoDatatypeDecl
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} ValuetypeDecl extends TopLevelDecl {
    var Members: System.Collections.Generic.Dictionary<string, MemberDecl>
    var typeTester: System.Func<Type, bool>
    var typeCreator: System.Func<System.Collections.Generic.List<Type>, Type>
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} DatatypeCtor extends Declaration, TypeParameter__ParentType {
    var Formals: System.Collections.Generic.List<Formal>
    var EnclosingDatatype: DatatypeDecl
    var QueryField: SpecialField
    var Destructors: System.Collections.Generic.List<DatatypeDestructor>
    var FullName: string
  }

  trait {:compile false} {:extern} ICodeContext {
    var {:extern "IsGhost"} Interface_IsGhost: bool // interface property
    var {:extern "TypeArgs"} Interface_TypeArgs: System.Collections.Generic.List<TypeParameter> // interface property
    var {:extern "Ins"} Interface_Ins: System.Collections.Generic.List<Formal> // interface property
    var {:extern "EnclosingModule"} Interface_EnclosingModule: ModuleDefinition // interface property
    var {:extern "MustReverify"} Interface_MustReverify: bool // interface property
    var {:extern "FullSanitizedName"} Interface_FullSanitizedName: string // interface property
    var {:extern "AllowsNontermination"} Interface_AllowsNontermination: bool // interface property
  }

  trait {:compile false} {:extern} CodeContextWrapper extends ICodeContext {
    var inner: ICodeContext
    var isGhostContext: bool
    var IsGhost: bool
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var Ins: System.Collections.Generic.List<Formal>
    var EnclosingModule: ModuleDefinition
    var MustReverify: bool
    var FullSanitizedName: string
    var AllowsNontermination: bool
  }

  trait {:compile false} {:extern} ICallable extends ICodeContext {
    var {:extern "Tok"} Interface_Tok: Microsoft.Boogie.IToken // interface property
    var {:extern "WhatKind"} Interface_WhatKind: string // interface property
    var {:extern "NameRelativeToModule"} Interface_NameRelativeToModule: string // interface property
    var {:extern "Decreases"} Interface_Decreases: Specification<Expression> // interface property
    var {:extern "InferredDecreases"} Interface_InferredDecreases: bool // interface property
    var {:extern "AllowsAllocation"} Interface_AllowsAllocation: bool // interface property
  }

  trait {:compile false} {:extern} CallableWrapper extends CodeContextWrapper, ICallable {
    var cwInner: ICallable
    var Tok: Microsoft.Boogie.IToken
    var WhatKind: string
    var NameRelativeToModule: string
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var AllowsAllocation: bool
  }

  trait {:compile false} {:extern} DontUseICallable extends ICallable {
    var WhatKind: string
    var IsGhost: bool
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var Ins: System.Collections.Generic.List<Formal>
    var EnclosingModule: ModuleDefinition
    var MustReverify: bool
    var FullSanitizedName: string
    var AllowsNontermination: bool
    var Tok: Microsoft.Boogie.IToken
    var NameRelativeToModule: string
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var AllowsAllocation: bool
  }

  trait {:compile false} {:extern} IMethodCodeContext extends ICallable {
    var {:extern "Outs"} Interface_Outs: System.Collections.Generic.List<Formal> // interface property
    var {:extern "Modifies"} Interface_Modifies: Specification<FrameExpression> // interface property
  }

  trait {:compile false} {:extern} NoContext extends ICodeContext {
    var Module: ModuleDefinition
    // var IsGhost: bool // explicit interface
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // explicit interface
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    var Decreases: Specification<Expression>
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    var FullSanitizedName: string
    var AllowsNontermination: bool
    var AllowsAllocation: bool
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
    // var WhatKind: string // exists in ancestor
    var SignatureIsOmitted: bool
    var SubExpressions: System.Collections.Generic.IEnumerable<Expression>
    // var IsGhost: bool // explicit interface
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // exists in ancestor
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var Outs: System.Collections.Generic.List<Formal> // explicit interface
    // var Modifies: Specification<FrameExpression> // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    var AllowsNontermination: bool
  }

  trait {:compile false} {:extern "IteratorDecl.EverIncreasingType"} IteratorDecl__EverIncreasingType extends BasicType {
  }

  trait {:compile false} {:extern} MemberDecl extends Declaration {
    var HasStaticKeyword: bool
    var isGhost: bool
    var EnclosingClass: TopLevelDecl
    var RefinementBase: MemberDecl
    var OverriddenMember: MemberDecl
    var WhatKind: string
    var IsStatic: bool
    var IsGhost: bool
    var IsInstanceIndependentConstant: bool
    var IsOverrideThatAddsBody: bool
    var FullDafnyName: string
    var FullName: string
    var FullSanitizedName: string
    var FullSanitizedRefinementName: string
    // var CompileName: string // exists in ancestor
    var FullCompileName: string
    var SubExpressions: System.Collections.Generic.IEnumerable<Expression>
  }

  trait {:compile false} {:extern} Field extends MemberDecl {
    var IsMutable: bool
    var IsUserMutable: bool
    var Type: Type
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} SpecialFunction extends Function, ICodeContext, ICallable {
    var Module: ModuleDefinition
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var NameRelativeToModule: string // explicit interface
  }

  trait {:compile false} {:extern} SpecialField extends Field {
    var SpecialId: SpecialField__ID
    var IdParam: object
    // var FullName: string // exists in ancestor
    // var FullSanitizedName: string // exists in ancestor
    // var FullSanitizedRefinementName: string // exists in ancestor
    // var CompileName: string // exists in ancestor
    // var FullCompileName: string // exists in ancestor
  }

  trait {:compile false} {:extern} DatatypeDestructor extends SpecialField {
    var EnclosingCtors: System.Collections.Generic.List<DatatypeCtor>
    var CorrespondingFormals: System.Collections.Generic.List<Formal>
  }

  trait {:compile false} {:extern} ConstantField extends SpecialField, ICallable {
    var Rhs: Expression
    // var WhatKind: string // exists in ancestor
    // var IsGhost: bool // exists in ancestor
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var Ins: System.Collections.Generic.List<Formal>
    var EnclosingModule: ModuleDefinition
    var MustReverify: bool
    var AllowsNontermination: bool
    var Tok: Microsoft.Boogie.IToken
    var NameRelativeToModule: string
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var AllowsAllocation: bool
  }

  trait {:compile false} {:extern} OpaqueTypeDecl extends TopLevelDeclWithMembers, TypeParameter__ParentType, RevealableTypeDecl {
    var Characteristics: TypeParameter__TypeParameterCharacteristics
    // var WhatKind: string // exists in ancestor
    var SupportsEquality: bool
    var AsTopLevelDecl: TopLevelDecl
  }

  trait {:compile false} {:extern} RedirectingTypeDecl extends ICallable {
    var {:extern "Name"} Interface_Name: string // interface property
    var {:extern "tok"} Interface_tok: Microsoft.Boogie.IToken // interface property
    var {:extern "Attributes"} Interface_Attributes: Attributes // interface property
    var {:extern "Module"} Interface_Module: ModuleDefinition // interface property
    var {:extern "Var"} Interface_Var: BoundVar // interface property
    var {:extern "Constraint"} Interface_Constraint: Expression // interface property
    var {:extern "WitnessKind"} Interface_WitnessKind: SubsetTypeDecl__WKind // interface property
    var {:extern "Witness"} Interface_Witness: Expression // interface property
    var {:extern "IdGenerator"} Interface_IdGenerator: FreshIdGenerator // interface property
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
    var {:extern "AsTopLevelDecl"} Interface_AsTopLevelDecl: TopLevelDecl // interface property
  }

  trait {:compile false} {:extern} NewtypeDecl extends TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl {
    var BaseType: Type
    var Var: BoundVar
    var Constraint: Expression
    var WitnessKind: SubsetTypeDecl__WKind
    var Witness: Expression
    var NativeType: NativeType
    // var WhatKind: string // exists in ancestor
    // var AsTopLevelDecl: TopLevelDecl // explicit interface
    var EqualitySupport: TypeParameter__EqualitySupportValue
    // var Name: string // exists in ancestor
    // var tok: Microsoft.Boogie.IToken // exists in ancestor
    // var Attributes: Attributes // exists in ancestor
    // var Module: ModuleDefinition // explicit interface
    // var Var: BoundVar // explicit interface
    // var Constraint: Expression // explicit interface
    // var WitnessKind: SubsetTypeDecl__WKind // explicit interface
    // var Witness: Expression // explicit interface
    // var IdGenerator: FreshIdGenerator // exists in ancestor
    // var IsGhost: bool // explicit interface
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // exists in ancestor
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    // var AllowsNontermination: bool // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
  }

  trait {:compile false} {:extern} TypeSynonymDeclBase extends TopLevelDecl, RedirectingTypeDecl {
    var Characteristics: TypeParameter__TypeParameterCharacteristics
    var Rhs: Type
    // var WhatKind: string // exists in ancestor
    var SupportsEquality: bool
    // var Name: string // exists in ancestor
    // var tok: Microsoft.Boogie.IToken // exists in ancestor
    // var Attributes: Attributes // exists in ancestor
    // var Module: ModuleDefinition // explicit interface
    // var Var: BoundVar // explicit interface
    // var Constraint: Expression // explicit interface
    // var WitnessKind: SubsetTypeDecl__WKind // explicit interface
    // var Witness: Expression // explicit interface
    // var IdGenerator: FreshIdGenerator // exists in ancestor
    // var IsGhost: bool // explicit interface
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // exists in ancestor
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    // var AllowsNontermination: bool // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
  }

  trait {:compile false} {:extern} TypeSynonymDecl extends TypeSynonymDeclBase, RedirectingTypeDecl, RevealableTypeDecl {
    // var AsTopLevelDecl: TopLevelDecl // explicit interface
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
    // var WhatKind: string // exists in ancestor
    // var Var: BoundVar // explicit interface
    // var Constraint: Expression // explicit interface
    // var WitnessKind: SubsetTypeDecl__WKind // explicit interface
    // var Witness: Expression // explicit interface
  }

  trait {:compile false} {:extern} NonNullTypeDecl extends SubsetTypeDecl {
    var Class: ClassDecl
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} IVariable {
    var CompileNameIdGenerator: FreshIdGenerator
    var {:extern "Name"} Interface_Name: string // interface property
    var {:extern "DisplayName"} Interface_DisplayName: string // interface property
    var {:extern "UniqueName"} Interface_UniqueName: string // interface property
    var {:extern "HasBeenAssignedUniqueName"} Interface_HasBeenAssignedUniqueName: bool // interface property
    var {:extern "CompileName"} Interface_CompileName: string // interface property
    var {:extern "Type"} Interface_Type: Type // interface property
    var {:extern "OptionalType"} Interface_OptionalType: Type // interface property
    var {:extern "IsMutable"} Interface_IsMutable: bool // interface property
    var {:extern "IsGhost"} Interface_IsGhost: bool // interface property
    var {:extern "Tok"} Interface_Tok: Microsoft.Boogie.IToken // interface property
  }

  trait {:compile false} {:extern} IVariableContracts extends IVariable {
    var Name: string
    var DisplayName: string
    var UniqueName: string
    var HasBeenAssignedUniqueName: bool
    var CompileName: string
    var Type: Type
    var OptionalType: Type
    var IsMutable: bool
    var IsGhost: bool
    var Tok: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} NonglobalVariable extends IVariable {
    var tok: Microsoft.Boogie.IToken
    var name: string
    var uniqueName: string
    var specialChars: array<char>
    var compileName: string
    var {:extern "type"} CSharp_type: Type
    var isGhost: bool
    var Name: string
    var DisplayName: string
    var UniqueName: string
    var HasBeenAssignedUniqueName: bool
    var CompileName: string
    var SyntacticType: Type
    var Type: Type
    // var OptionalType: Type // explicit interface
    var IsMutable: bool
    var IsGhost: bool
    var Tok: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} Formal extends NonglobalVariable {
    var InParam: bool
    var IsOld: bool
    var DefaultValue: Expression
    var IsNameOnly: bool
    var NameForCompilation: string
    // var IsMutable: bool // exists in ancestor
    var HasName: bool
    // var CompileName: string // exists in ancestor
  }

  trait {:compile false} {:extern} ImplicitFormal extends Formal {
  }

  trait {:compile false} {:extern} ThisSurrogate extends ImplicitFormal {
  }

  trait {:compile false} {:extern} BoundVar extends NonglobalVariable {
    // var IsMutable: bool // exists in ancestor
  }

  trait {:compile false} {:extern} ActualBinding {
    var FormalParameterName: Microsoft.Boogie.IToken
    var Actual: Expression
    var IsGhost: bool
  }

  trait {:compile false} {:extern} ActualBindings {
    var ArgumentBindings: System.Collections.Generic.List<ActualBinding>
    var arguments: System.Collections.Generic.List<Expression>
    var WasResolved: bool
    var Arguments: System.Collections.Generic.List<Expression>
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
    // var WhatKind: string // exists in ancestor
    var IsTailRecursive: bool
    var IsAccumulatorTailRecursive: bool
    var SignatureIsOmitted: bool
    var Original: Function
    // var IsOverrideThatAddsBody: bool // exists in ancestor
    var AllowsAllocation: bool
    var ContainsQuantifier: bool
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    var AllowsNontermination: bool
    // var IsGhost: bool // exists in ancestor
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // explicit interface
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    var ReadsHeap: bool
  }

  trait {:compile false} {:extern} Predicate extends Function {
    var BodyOrigin: Predicate__BodyOriginKind
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} PrefixPredicate extends Function {
    var K: Formal
    var ExtremePred: ExtremePredicate
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} ExtremePredicate extends Function {
    var TypeOfK: ExtremePredicate__KType
    var Uses: System.Collections.Generic.List<FunctionCallExpr>
    var PrefixPredicate: PrefixPredicate
    var KNat: bool
  }

  trait {:compile false} {:extern} LeastPredicate extends ExtremePredicate {
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} GreatestPredicate extends ExtremePredicate {
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} TwoStateFunction extends Function {
    // var WhatKind: string // exists in ancestor
    // var ReadsHeap: bool // exists in ancestor
  }

  trait {:compile false} {:extern} TwoStatePredicate extends TwoStateFunction {
    // var WhatKind: string // exists in ancestor
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
    // var WhatKind: string // exists in ancestor
    var SignatureIsOmitted: bool
    var Original: Method
    // var IsOverrideThatAddsBody: bool // exists in ancestor
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var IsGhost: bool // exists in ancestor
    // var TypeArgs: System.Collections.Generic.List<TypeParameter> // explicit interface
    // var Ins: System.Collections.Generic.List<Formal> // explicit interface
    // var Outs: System.Collections.Generic.List<Formal> // explicit interface
    // var Modifies: Specification<FrameExpression> // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
    // var NameRelativeToModule: string // explicit interface
    // var Decreases: Specification<Expression> // explicit interface
    // var InferredDecreases: bool // explicit interface
    var AllowsAllocation: bool
    // var EnclosingModule: ModuleDefinition // explicit interface
    // var MustReverify: bool // explicit interface
    var AllowsNontermination: bool
    // var CompileName: string // exists in ancestor
    var Body: BlockStmt
    var IsLemmaLike: bool
    var BodyForRefinement: BlockStmt
  }

  trait {:compile false} {:extern} Lemma extends Method {
    // var WhatKind: string // exists in ancestor
    // var AllowsAllocation: bool // exists in ancestor
  }

  trait {:compile false} {:extern} TwoStateLemma extends Method {
    // var WhatKind: string // exists in ancestor
    // var AllowsAllocation: bool // exists in ancestor
  }

  trait {:compile false} {:extern} Constructor extends Method {
    // var WhatKind: string // exists in ancestor
    var BodyInit: System.Collections.Generic.List<Statement>
    var BodyProper: System.Collections.Generic.List<Statement>
    var HasName: bool
  }

  trait {:compile false} {:extern} PrefixLemma extends Method {
    var K: Formal
    var ExtremeLemma: ExtremeLemma
    // var WhatKind: string // exists in ancestor
    // var AllowsAllocation: bool // exists in ancestor
  }

  trait {:compile false} {:extern} ExtremeLemma extends Method {
    var TypeOfK: ExtremePredicate__KType
    var PrefixLemma: PrefixLemma
    var KNat: bool
    // var AllowsAllocation: bool // exists in ancestor
  }

  trait {:compile false} {:extern} LeastLemma extends ExtremeLemma {
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} GreatestLemma extends ExtremeLemma {
    // var WhatKind: string // exists in ancestor
  }

  trait {:compile false} {:extern} Statement extends IAttributeBearingDeclaration {
    var Tok: Microsoft.Boogie.IToken
    var EndTok: Microsoft.Boogie.IToken
    var Labels: LList<Label>
    var attributes: Attributes
    var IsGhost: bool
    var Attributes: Attributes
    var SubStatements: System.Collections.Generic.IEnumerable<Statement>
    var SubExpressions: System.Collections.Generic.IEnumerable<Expression>
    var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression>
    var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression>
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
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ExpectStmt extends PredicateStmt {
    var Message: Expression
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} AssumeStmt extends PredicateStmt {
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} PrintStmt extends Statement {
    var Args: System.Collections.Generic.List<Expression>
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} RevealStmt extends Statement {
    var Exprs: System.Collections.Generic.List<Expression>
    var LabeledAsserts: System.Collections.Generic.List<AssertLabel>
    var ResolvedStatements: System.Collections.Generic.List<Statement>
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} BreakStmt extends Statement {
    var TargetLabel: Microsoft.Boogie.IToken
    var BreakCount: int
    var TargetStmt: Statement
  }

  trait {:compile false} {:extern} ProduceStmt extends Statement {
    var rhss: System.Collections.Generic.List<AssignmentRhs>
    var hiddenUpdate: UpdateStmt
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} ReturnStmt extends ProduceStmt {
    var ReverifyPost: bool
  }

  trait {:compile false} {:extern} YieldStmt extends ProduceStmt {
  }

  trait {:compile false} {:extern} AssignmentRhs {
    var Tok: Microsoft.Boogie.IToken
    var attributes: Attributes
    var Attributes: Attributes
    var CanAffectPreviouslyKnownExpressions: bool
    var SubExpressions: System.Collections.Generic.IEnumerable<Expression>
    var SubStatements: System.Collections.Generic.IEnumerable<Statement>
  }

  trait {:compile false} {:extern} ExprRhs extends AssignmentRhs {
    var Expr: Expression
    // var CanAffectPreviouslyKnownExpressions: bool // exists in ancestor
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    var Arguments: System.Collections.Generic.List<Expression>
    // var CanAffectPreviouslyKnownExpressions: bool // exists in ancestor
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} HavocRhs extends AssignmentRhs {
    // var CanAffectPreviouslyKnownExpressions: bool // exists in ancestor
  }

  trait {:compile false} {:extern} VarDeclStmt extends Statement {
    var Locals: System.Collections.Generic.List<LocalVariable>
    var Update: ConcreteUpdateStatement
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} VarDeclPattern extends Statement {
    var LHS: CasePattern<LocalVariable>
    var RHS: Expression
    var HasGhostModifier: bool
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    var LocalVars: System.Collections.Generic.IEnumerable<LocalVariable>
  }

  trait {:compile false} {:extern} ConcreteUpdateStatement extends Statement {
    var Lhss: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} AssignSuchThatStmt extends ConcreteUpdateStatement {
    var Expr: Expression
    var AssumeToken: Microsoft.Boogie.IToken
    var Bounds: System.Collections.Generic.List<ComprehensionExpr__BoundedPool>
    var MissingBounds: System.Collections.Generic.List<IVariable>
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern "AssignSuchThatStmt.WiggleWaggleBound"} AssignSuchThatStmt__WiggleWaggleBound extends ComprehensionExpr__BoundedPool {
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern} UpdateStmt extends ConcreteUpdateStatement {
    var Rhss: System.Collections.Generic.List<AssignmentRhs>
    var CanMutateKnownState: bool
    var OriginalInitialLhs: Expression
    var ResolvedStatements: System.Collections.Generic.List<Statement>
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} AssignOrReturnStmt extends ConcreteUpdateStatement {
    var Rhs: Expression
    var Rhss: System.Collections.Generic.List<AssignmentRhs>
    var KeywordToken: Microsoft.Boogie.IToken
    var ResolvedStatements: System.Collections.Generic.List<Statement>
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} AssignStmt extends Statement {
    var Lhs: Expression
    var Rhs: AssignmentRhs
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    var Name: string
    var DisplayName: string
    var UniqueName: string
    var HasBeenAssignedUniqueName: bool
    var CompileName: string
    // var OptionalType: Type // explicit interface
    var Type: Type
    var IsMutable: bool
    // var IsGhost: bool // explicit interface
    // var Tok: Microsoft.Boogie.IToken // explicit interface
  }

  trait {:compile false} {:extern} CallStmt extends Statement {
    var Lhs: System.Collections.Generic.List<Expression>
    var MethodSelect: MemberSelectExpr
    var Bindings: ActualBindings
    var OriginalInitialLhs: Expression
    var Args: System.Collections.Generic.List<Expression>
    var Receiver: Expression
    var Method: Method
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} BlockStmt extends Statement, IRegion {
    var Body: System.Collections.Generic.List<Statement>
    // var BodyStartTok: Microsoft.Boogie.IToken // explicit interface
    // var BodyEndTok: Microsoft.Boogie.IToken // explicit interface
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
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
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} LoopStmt extends Statement {
    var Invariants: System.Collections.Generic.List<AttributedExpression>
    var Decreases: Specification<Expression>
    var InferredDecreases: bool
    var Mod: Specification<FrameExpression>
    var LoopSpecificationExpressions: System.Collections.Generic.IEnumerable<Expression>
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} OneBodyLoopStmt extends LoopStmt {
    var Body: BlockStmt
    var BodySurrogate: WhileStmt__LoopBodySurrogate
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} WhileStmt extends OneBodyLoopStmt {
    var Guard: Expression
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} AlternativeLoopStmt extends LoopStmt {
    var UsesOptionalBraces: bool
    var Alternatives: System.Collections.Generic.List<GuardedAlternative>
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    var S0: Statement
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ModifyStmt extends Statement {
    var Mod: Specification<FrameExpression>
    var Body: BlockStmt
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var SpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    var AllCalcOps: System.Collections.Generic.IEnumerable<CalcStmt__CalcOp>
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
    var Source: Expression
    var Cases: System.Collections.Generic.List<MatchCaseStmt>
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} MatchCaseStmt extends MatchCase {
    var body: System.Collections.Generic.List<Statement>
    var Attributes: Attributes
    var Body: System.Collections.Generic.List<Statement>
  }

  trait {:compile false} {:extern} SkeletonStatement extends Statement {
    var S: Statement
    var ConditionEllipsis: Microsoft.Boogie.IToken
    var BodyEllipsis: Microsoft.Boogie.IToken
    var ConditionOmitted: bool
    var BodyOmitted: bool
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
  }

  trait {:compile false} {:extern} TokenWrapper extends Microsoft.Boogie.IToken {
    var WrappedToken: Microsoft.Boogie.IToken
    var col: int
    var filename: string
    var IsValid: bool
    var kind: int
    var line: int
    var pos: int
    var val: string
  }

  trait {:compile false} {:extern} NestedToken extends TokenWrapper {
    var Inner: Microsoft.Boogie.IToken
    var Message: string
    var Outer: Microsoft.Boogie.IToken
  }

  trait {:compile false} {:extern} IncludeToken extends TokenWrapper {
    var Include: Include
    // var val: string // exists in ancestor
  }

  trait {:compile false} {:extern} Expression {
    var tok: Microsoft.Boogie.IToken
    var {:extern "type"} CSharp_type: Type
    var Resolved: Expression
    var Type: Type
    var SubExpressions: System.Collections.Generic.IEnumerable<Expression>
    var ComponentTypes: System.Collections.Generic.IEnumerable<Type>
    var IsImplicit: bool
  }

  trait {:compile false} {:extern} StaticReceiverExpr extends LiteralExpr {
    var UnresolvedType: Type
    var Implicit: bool
    var OriginalResolved: Expression
    // var IsImplicit: bool // exists in ancestor
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
    var Arguments: System.Collections.Generic.List<Expression>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ThisExpr extends Expression {
  }

  trait {:compile false} {:extern} ExpressionPair {
    var A: Expression
    var B: Expression
  }

  trait {:compile false} {:extern} ImplicitThisExpr extends ThisExpr {
    // var IsImplicit: bool // exists in ancestor
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
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} SetDisplayExpr extends DisplayExpression {
    var Finite: bool
  }

  trait {:compile false} {:extern} MultiSetDisplayExpr extends DisplayExpression {
  }

  trait {:compile false} {:extern} MapDisplayExpr extends Expression {
    var Finite: bool
    var Elements: System.Collections.Generic.List<ExpressionPair>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern} SeqSelectExpr extends Expression {
    var SelectOne: bool
    var Seq: Expression
    var E0: Expression
    var E1: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} MultiSelectExpr extends Expression {
    var Array: Expression
    var Indices: System.Collections.Generic.List<Expression>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} SeqUpdateExpr extends Expression {
    var Seq: Expression
    var Index: Expression
    var Value: Expression
    var ResolvedUpdateExpr: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ApplyExpr extends Expression {
    var Function: Expression
    var Args: System.Collections.Generic.List<Expression>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    var Args: System.Collections.Generic.List<Expression>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern} SeqConstructionExpr extends Expression {
    var ExplicitElementType: Type
    var N: Expression
    var Initializer: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern} MultiSetFormingExpr extends Expression {
    var E: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} OldExpr extends Expression {
    var E: Expression
    var At: string
    var AtLabel: Label
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} UnchangedExpr extends Expression {
    var Frame: System.Collections.Generic.List<FrameExpression>
    var At: string
    var AtLabel: Label
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} UnaryExpr extends Expression {
    var E: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
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
    var ResolvedOp: BinaryExpr__ResolvedOpcode
    var ResolvedOp_PossiblyStillUndetermined: BinaryExpr__ResolvedOpcode
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} TernaryExpr extends Expression {
    var Op: TernaryExpr__Opcode
    var E0: Expression
    var E1: Expression
    var E2: Expression
    var PrefixEqUsesNat: bool
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var BodyStartTok: Microsoft.Boogie.IToken // explicit interface
    // var BodyEndTok: Microsoft.Boogie.IToken // explicit interface
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
    var BoundVars: System.Collections.Generic.IEnumerable<BoundVar>
    var AllBoundVars: System.Collections.Generic.IEnumerable<BoundVar>
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
    var WhatKind: string
    var Term: Expression
    var AllBoundVars: System.Collections.Generic.IEnumerable<BoundVar>
    // var BodyStartTok: Microsoft.Boogie.IToken // explicit interface
    // var BodyEndTok: Microsoft.Boogie.IToken // explicit interface
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.BoundedPool"} ComprehensionExpr__BoundedPool {
    var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues
  }

  trait {:compile false} {:extern "ComprehensionExpr.ExactBoundedPool"} ComprehensionExpr__ExactBoundedPool extends ComprehensionExpr__BoundedPool {
    var E: Expression
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.BoolBoundedPool"} ComprehensionExpr__BoolBoundedPool extends ComprehensionExpr__BoundedPool {
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.CharBoundedPool"} ComprehensionExpr__CharBoundedPool extends ComprehensionExpr__BoundedPool {
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.AllocFreeBoundedPool"} ComprehensionExpr__AllocFreeBoundedPool extends ComprehensionExpr__BoundedPool {
    var Type: Type
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.ExplicitAllocatedBoundedPool"} ComprehensionExpr__ExplicitAllocatedBoundedPool extends ComprehensionExpr__BoundedPool {
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool"} ComprehensionExpr__SpecialAllocIndependenceAllocatedBoundedPool extends ComprehensionExpr__BoundedPool {
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.IntBoundedPool"} ComprehensionExpr__IntBoundedPool extends ComprehensionExpr__BoundedPool {
    var LowerBound: Expression
    var UpperBound: Expression
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.CollectionBoundedPool"} ComprehensionExpr__CollectionBoundedPool extends ComprehensionExpr__BoundedPool {
    var BoundVariableType: Type
    var CollectionElementType: Type
    var IsFiniteCollection: bool
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.SetBoundedPool"} ComprehensionExpr__SetBoundedPool extends ComprehensionExpr__CollectionBoundedPool {
    var Set: Expression
  }

  trait {:compile false} {:extern "ComprehensionExpr.SubSetBoundedPool"} ComprehensionExpr__SubSetBoundedPool extends ComprehensionExpr__BoundedPool {
    var UpperBound: Expression
    var IsFiniteCollection: bool
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.SuperSetBoundedPool"} ComprehensionExpr__SuperSetBoundedPool extends ComprehensionExpr__BoundedPool {
    var LowerBound: Expression
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
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
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern "ComprehensionExpr.DatatypeInclusionBoundedPool"} ComprehensionExpr__DatatypeInclusionBoundedPool extends ComprehensionExpr__BoundedPool {
    var IsIndDatatype: bool
    // var Virtues: ComprehensionExpr__BoundedPool__PoolVirtues // exists in ancestor
  }

  trait {:compile false} {:extern} QuantifierExpr extends ComprehensionExpr, TypeParameter__ParentType {
    var UniqueId: int
    var TypeArgs: System.Collections.Generic.List<TypeParameter>
    var currentQuantId: int
    var {:extern "_SplitQuantifier"} CSharp__SplitQuantifier: System.Collections.Generic.List<Expression>
    // var WhatKind: string // exists in ancestor
    var SplitResolvedOp: BinaryExpr__ResolvedOpcode
    var SplitQuantifier: System.Collections.Generic.List<Expression>
    var SplitQuantifierExpression: Expression
    var FullName: string
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ForallExpr extends QuantifierExpr {
    // var WhatKind: string // exists in ancestor
    // var SplitResolvedOp: BinaryExpr__ResolvedOpcode // exists in ancestor
  }

  trait {:compile false} {:extern} ExistsExpr extends QuantifierExpr {
    // var WhatKind: string // exists in ancestor
    // var SplitResolvedOp: BinaryExpr__ResolvedOpcode // exists in ancestor
  }

  trait {:compile false} {:extern} SetComprehension extends ComprehensionExpr {
    var Finite: bool
    var TermIsImplicit: bool
    // var WhatKind: string // exists in ancestor
    var TermIsSimple: bool
  }

  trait {:compile false} {:extern} MapComprehension extends ComprehensionExpr {
    var Finite: bool
    var TermLeft: Expression
    var ProjectionFunctions: System.Collections.Generic.List<Microsoft.Boogie.Function>
    // var WhatKind: string // exists in ancestor
    var IsGeneralMapComprehension: bool
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} LambdaExpr extends ComprehensionExpr {
    var Reads: System.Collections.Generic.List<FrameExpression>
    // var WhatKind: string // exists in ancestor
    var Body: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} WildcardExpr extends Expression {
  }

  trait {:compile false} {:extern} StmtExpr extends Expression {
    var S: Statement
    var E: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} ITEExpr extends Expression {
    var IsBindingGuard: bool
    var Test: Expression
    var Thn: Expression
    var Els: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} MatchExpr extends Expression {
    var source: Expression
    var cases: System.Collections.Generic.List<MatchCaseExpr>
    var Context: MatchingContext
    var MissingCases: System.Collections.Generic.List<DatatypeCtor>
    var UsesOptionalBraces: bool
    var OrigUnresolved: MatchExpr
    var Source: Expression
    var Cases: System.Collections.Generic.List<MatchCaseExpr>
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern} CasePattern<VT> {
    var tok: Microsoft.Boogie.IToken
    var Id: string
    var Ctor: DatatypeCtor
    var Var: VT
    var Arguments: System.Collections.Generic.List<CasePattern<VT>>
    var Expr: Expression
    var Vars: System.Collections.Generic.IEnumerable<VT>
  }

  trait {:compile false} {:extern} MatchCase {
    var tok: Microsoft.Boogie.IToken
    var Ctor: DatatypeCtor
    var Arguments: System.Collections.Generic.List<BoundVar>
  }

  trait {:compile false} {:extern} MatchCaseExpr extends MatchCase {
    var body: Expression
    var Attributes: Attributes
    var Body: Expression
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
    var OptimisticallyDesugaredLit: LiteralExpr
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
    // var NonSpecificationSubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} UnboxingCastExpr extends Expression {
    var E: Expression
    var FromType: Type
    var ToType: Type
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
  }

  trait {:compile false} {:extern} AttributedExpression {
    var E: Expression
    var Label: AssertLabel
    var attributes: Attributes
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} FrameExpression {
    var tok: Microsoft.Boogie.IToken
    var E: Expression
    var FieldName: string
    var Field: Field
  }

  trait {:compile false} {:extern} ConcreteSyntaxExpression extends Expression {
    var ResolvedExpression: Expression
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
    // var ComponentTypes: System.Collections.Generic.IEnumerable<Type> // exists in ancestor
  }

  trait {:compile false} {:extern} ConcreteSyntaxStatement extends Statement {
    var ResolvedStatement: Statement
    // var SubStatements: System.Collections.Generic.IEnumerable<Statement> // exists in ancestor
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
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    // var SubExpressions: System.Collections.Generic.IEnumerable<Expression> // exists in ancestor
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
    var Args: System.Collections.Generic.List<Expression>
  }

  trait {:compile false} {:extern} Specification<T> {
    var Expressions: System.Collections.Generic.List<T>
    var attributes: Attributes
    var Attributes: Attributes
  }

  trait {:compile false} {:extern} BottomUpVisitor {
  }

  trait {:compile false} {:extern} TopDownVisitor<State> {
  }
}
