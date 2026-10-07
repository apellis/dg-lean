# Roadmap

Results to formalize, in build order. Each item names what must be proved, on the library's
own definitions, and where the standard proof is. Items marked **(Mathlib)** are general
statements that would fit Mathlib as they stand; items marked **(stretch)** are desirable but
not on the critical path. Record declaration names next to items as they are completed.

References:

- [BL] J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578, 1994, §10.
- [Ke] B. Keller, *Deriving DG categories*, Ann. Sci. ENS 27 (1994), 63–102.
- [Ke2] B. Keller, *On differential graded categories*, ICM 2006 (survey).
- [Ne] A. Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*, JAMS 9 (1996); *Triangulated categories*, Ann. Math. Studies 148.
- [Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
  Appl. Categ. Structures 19 (2011), 757–782, arXiv:0809.4782.
- [St] The Stacks Project, Chapter "Differential graded algebra" (tag 09JD).
- [Ve] J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239.

Throughout, `R` is a commutative ring, `A` a dg algebra over `R` (cohomologically ℤ-graded, see
`docs/CONVENTIONS.md`), and "dg module" means left dg `A`-module unless stated.

## Tier 1 — Graded algebra with Koszul signs

1.1 Graded `R`-modules as internal direct sums (`DirectSum.Decomposition`), homogeneous
    elements, degree, graded linear maps of degree `n`, the graded `Hom` (`⊕ₙ Hom^n`), and the
    Koszul-signed composition and evaluation rules. Reuse Mathlib's `GradedRing`,
    `GradedAlgebra`, `DirectSum.GAlgebra`, `SetLike.GradedMonoid`.
    — done (graded maps and the graded `Hom`; the Koszul-signed rules for the interaction of
    graded maps with graded actions are part of 1.3): `DG.HasDegree`, `DG.GradedHom`,
    `DG.GradedHom.comp`, `DG.GradedHom.id`, `DG.GradedHom.liftEquiv`,
    `DG.GradedHom.ext_homogeneous`, `DG.GradedHOM`, `DG.GradedHOM.grading`,
    `DG.GradedHOM.eval`, `DG.GradedHOM.compHom`, `DG.GradedHOM.eval_compHom`, `DG.GradedEND`,
    `DG.GradedEND.instGRing`, `DG.GradedEND.instGradedRing`, `DG.GradedEND.evalRingHom`;
    generic helpers `DG.summand`, `DG.instDecompositionSummand`, `DG.instGradedRingSummand`,
    `DG.proj`, `DG.liftHomogeneous`, `DG.decompose_addHom_ext` (`DG/Graded/Basic.lean`,
    `DG/Graded/Hom.lean`).
1.2 Graded (super)commutativity, the opposite graded algebra with the signed product, graded
    tensor product of graded algebras over `R` with the signed product; associativity, unit,
    symmetry `A ⊗ B ≅ B ⊗ A` with the Koszul sign.
    — done: `DG.IsGradedComm`, `DG.IsGradedCommStrict`, `DG.GradedOpposite` (with
    `DG.GradedOpposite.op_mul_op`, `DG.GradedOpposite.opOpAlgEquiv`, `DG.isGradedComm_iff_op_mul`);
    the tensor product is Mathlib's `GradedTensorProduct` for `ι = ℤ` (its sign is
    `DG.koszulSign`, `DG.uzpow_neg_one_eq_koszulSign`), with `DG.GradedTensorProduct.grading`,
    `DG.GradedTensorProduct.instGradedAlgebra`, `DG.GradedTensorProduct.tmul_mul_tmul`,
    `DG.GradedTensorProduct.comm_tmul`, `DG.GradedTensorProduct.assoc`,
    `DG.GradedTensorProduct.lid`.
1.3 Graded modules over graded algebras: left, right, bimodules; a right module is a left
    module over the opposite algebra; graded `Hom_A`, graded tensor product `M ⊗_A N` with
    signs; the corner algebra `eAe` and the modules `Ae`, `eA` for a homogeneous idempotent
    `e` of degree `0`. — done (left, right and bimodules; `eAe`, `Ae`, `eA` for a degree-`0`
    idempotent cocycle `e`): `DG.DGModule`, `DG.DGRightModule`, `DG.DGBimodule`,
    `DG.DGIdempotent`, `DG.DGIdempotent.Corner`, `DG.DGIdempotent.LeftCorner`,
    `DG.DGIdempotent.RightCorner`; the opposite algebra, `Hom_A`, `⊗_A` are open.
1.4 Regrading constructions: from a `ℤ/2`-graded algebra to a 2-periodic `ℤ`-graded one and
    back; from a grading with a map of degree `k` to a grading with a map of degree `1`.
    Acceptance: equivalences of the corresponding categories of graded modules.
    — done (graded and dg). For `ℤ/2`: `DG.Periodize`, `DG.Periodize.periodUnit`,
    `DG.Periodize.quotientEquiv`, `DG.PeriodicityUnit.periodizeEquiv`, `DG.GradedModuleCat`,
    `DG.GradedModuleCat.periodizeEquivalence`, `DG.Periodize.dgRing`,
    `DG.GradedModuleCat.periodizeDGEquivalence`; for a differential of degree `k`, the
    regrading by residues with the object-level decomposition: `DG.RegradeByDivision`,
    `DG.residueEquiv`, `DG.residueEquiv_d`, `DG.RegradeByDivision.dgRing` (Leibniz sign
    `(-1)^{|a|/k}` on `A^{qk}`). The comparison with `DG.DGModuleCat (Periodize ℬ)` is proved:
    `DG.GradedModuleCat.periodicDGModuleCatEquivalence`,
    `DG.GradedModuleCat.zmod2DGModuleCatEquivalence`. For a ring `A` concentrated in degrees
    divisible by `k ≥ 1` (`DG.IsConcentratedInMultiples`; necessary for the residue classes to
    be submodules), `A ≅ ⨁ q, A^{qk}` (`DG.regradeRingEquiv`, compatible with the
    differentials: `DG.regradeRingHom_d`), and the category equivalences
    `DG.GradedModuleCat.regradeEquivalence : GradedModuleCat 𝒜 ≌ (ZMod k → GradedModuleCat ℬ)`
    and, for a differential of degree `k`, `DG.GradedModuleCat.regradeDGEquivalence` and
    `DG.GradedModuleCat.divDGModuleCatEquivalence : DivDGModuleCat 𝒜 k dA ≌
    (ZMod k → DGModuleCat (⨁ q, A^{qk}))`, `M ↦ (⨁ q, M^{qk + r})_r`.

## Tier 2 — dg algebras and dg modules

2.1 `DGAlgebra R A`: graded algebra with a degree-`1` differential `d`, `d ∘ d = 0`, Leibniz
    rule. Basic API: `d 1 = 0`, `d` of a product, `d` of a power of an even element, the graded
    Leibniz rule for `n`-fold products. `DGAlgHom`. The opposite dg algebra, tensor product of
    dg algebras, dg subalgebras, dg ideals and quotients, the kernel and image of `d`, the
    cohomology algebra `H(A)` as a graded algebra with zero differential, and the dg algebra
    structure on `H(A)` viewed as a dg algebra. `R` as a dg algebra in degree `0`; a graded
    algebra as a dg algebra with `d = 0`.
    — done: `DG.DGAddCommGroup`, `DG.DGRing`, `DG.DGAlgebra`, `DG.d_one`, `DG.d_mul`, `DG.d_pow`,
    `DG.d_list_prod`, `DG.DGRingHom`, `DG.DGAlgHom`, `DG.DGSubring`, `DG.DGIdeal`,
    `DG.DGIdeal.Quotient.dgRing`, `DG.DGRingHom.ker`, `DG.cocyclesDGSubring`,
    `DG.coboundariesDGIdeal`, `DG.Cohomology.dgRing` (the cohomology ring with `d = 0`),
    `DG.DGRingHom.cohomologyRingMap`, `DG.DGRing.ofGradedRing`, `DG.DGAlgebra.degreeZero`.
    The opposite dg algebra: `DG.GradedOpposite.instDGAlgebra`, `DG.GradedOpposite.opOpDGAlgEquiv`,
    `DG.GradedOpposite.opDGAlgEquiv` (graded-commutative case); right dg modules as left dg
    `Aᵒᵖ`-modules: `DG.rightModuleEquivOpModule`. The tensor product:
    `DG.GradedTensorProduct.instDGAlgebra`, `DG.GradedTensorProduct.d_tmul`,
    `DG.GradedTensorProduct.includeLeftDGAlgHom`, `DG.GradedTensorProduct.map`,
    `DG.GradedTensorProduct.commDGAlgEquiv`, `DG.GradedTensorProduct.assocDGAlgEquiv`,
    `DG.GradedTensorProduct.lidDGAlgEquiv`; `DG.DGAlgEquiv`. The `R`-algebra `H(A)`:
    `DG.Cohomology.galgebra`, `DG.Cohomology.dgAlgebra`, `DG.DGAlgHom.cohomologyAlgHom`.
2.2 `DGModule A M`: left dg module; right dg modules and bimodules; `DGModuleHom` (degree-`0`
    chain maps) — done (modules, right modules, bimodules, restriction of scalars):
    `DG.DGModule`, `DG.DGModuleHom`, `DG.DGRightModule`, `DG.DGBimodule`,
    `DG.RestrictScalars`, `DG.DGModuleHom.restrictScalars`; the category: `DG.DGModuleCat`,
    `DG.DGModuleCat.abelian`, `DG.DGModuleCat.forget_preservesFiniteLimits`,
    `DG.DGModuleCat.forget_preservesFiniteColimits`, `DG.DGModuleCat.shortExact_map_forget`,
    `DG.DGModuleCat.preadditive`, `DG.DGModuleCat.instLinear`, `DG.DGModuleCat.hasFiniteBiproducts`,
    `DG.DGModuleCat.hasCoproducts`, `DG.DGModuleCat.hasProducts` (graded products),
    `DG.DGModuleCat.forget`, `DG.DGModuleCat.forget_faithful`,
    `DG.DGModuleCat.forget_preservesColimitsOfShape_discrete`, `DG.DGSubmodule`;
    restriction and extension of scalars: `DG.DGModuleCat.restrictScalars`,
    `DG.DGModuleCat.extendScalars`, `DG.DGModuleCat.extendRestrictScalarsAdj`,
    `DG.DGModuleCat.restrictScalars_preservesFiniteLimits`;
    the abelian category `DGModuleCat A` **(Mathlib)**: it is `R`-linear,
    abelian, with arbitrary (co)products, and the forgetful functor to
    `CochainComplex (ModuleCat R) ℤ` is exact and faithful. Restriction of scalars along a
    `DGAlgHom`, and extension of scalars `A ⊗_B -`.
2.3 `HOM_A(M, N)`: the dg `R`-module of graded `A`-linear maps with
    `d f = d_N ∘ f - (-1)^{|f|} f ∘ d_M`; `END_A(M)` as a dg algebra acting on `M` on the right
    (`m · f = (-1)^{|f||m|} f m`); `M` is a dg `(A, END_A(M))`-bimodule. `HOM_A(A e, A e) ≅ e A e`
    as dg algebras for `e` a degree-`0` idempotent with `d e ∈ A e` (the differential on `eAe`
    is `e a e ↦ e d(a e)`), and `A e` is a dg `(A, eAe)`-bimodule.
    — done: the Hom complex and `END`: `DG.Cochain`, `DG.Cochain.comp`, `DG.Cochain.id`,
    `DG.δ`, `DG.δ_δ`, `DG.δ_comp`, `DG.Cocycle`, `DG.Cocycle.equivHom`, `DG.DGModule.HOM`,
    `DG.DGModule.END`, `DG.DGModule.END.instDGRing` (product `f * g = (-1)^{|f||g|} g ∘ f`),
    `DG.DGModule.END.rightAction`; for `d e = 0`: `eAe` as a dg ring, `A e` as a dg
    `(A, eAe)`-bimodule, `e A` as a dg `(eAe, A)`-bimodule
    (`DG.DGIdempotent.Corner.instDGRing`, `DG.DGIdempotent.LeftCorner.instDGBimodule`,
    `DG.DGIdempotent.RightCorner.instDGBimodule`); `M` as a dg `(A, END_A(M))`-bimodule:
    `DG.DGModule.END.instDGBimodule`; `END_A(A e) ≅ e A e`:
    `DG.DGIdempotent.endLeftCornerEquiv`, `DG.DGModule.END.selfEquiv`; the case `d e ∈ A e`
    with the differential `e a e ↦ e d(a e)`: `DG.LeftDGIdempotent`,
    `DG.LeftDGIdempotent.Corner.instDGRing`, `DG.LeftDGIdempotent.Corner.coe_d_mk`,
    `DG.LeftDGIdempotent.LeftCorner.instDGBimodule`, `DG.LeftDGIdempotent.endLeftCornerEquiv`.
2.4 Tensor products: `M ⊗_A N` for a right dg module `M` and left dg module `N`, with the
    signed differential; associativity, `A ⊗_A N ≅ N`, `HOM`–`⊗` adjunction at the level of dg
    modules; `M ⊗_R N` with the signed differential. — done (with `M ⊗_R N` over `R = ℤ`):
    the adjunction `DG.TensorProductOver.curryEquiv`
    (`HOM_A(M ⊗_B N, P) ≅ HOM_B(N, HOM_A(M, P))`), `DG.TensorProductOver.homEquiv`,
    `DG.TensorProductOver.homEquiv_comp_lTensor`, `DG.TensorProductOver.homEquiv_comp`,
    `DG.DGModule.HOM.LeftAction.instDGModule`, `DG.DGModule.HOM.evalOneEquiv`
    (`HOM_A(A, P) ≅ P`); `DG.instDGAddCommGroupTensorProduct`,
    `DG.d_tmul_of_mem`, `DG.gradeInvolution`, `DG.tensorMap`, `DG.tensorComm`,
    `DG.tensorAssoc`, `DG.instDGModuleTensorProduct`, `DG.DGAddEquiv`,
    `DG.IsDGAddSubgroup`, `DG.DGAddCommGroup.quotient`, `DG.TensorProductOver`,
    `DG.TensorProductOver.instDGAddCommGroup`, `DG.TensorProductOver.d_tmul_of_mem`,
    `DG.TensorProductOver.op_smul_tmul`, `DG.TensorProductOver.lift`,
    `DG.TensorProductOver.lift_unique`, `DG.TensorProductOver.map`,
    `DG.TensorProductOver.instDGModule`, `DG.TensorProductOver.lidDGModuleEquiv`,
    `DG.TensorProductOver.rid`, `DG.TensorProductOver.RightAction.instDGRightModule`,
    `DG.TensorProductOver.assocEquiv` (`DG/Module/TensorProduct.lean`,
    `DG/Module/TensorProductOver.lean`, `DG/Module/Quotient.lean`, `DG/Algebra/AddEquiv.lean`).
2.5 Cohomology `H(M)` as a graded `H(A)`-module, functorial; `H` commutes with finite direct
    sums and with arbitrary direct sums; quasi-isomorphisms; the long exact cohomology
    sequence of a short exact sequence of dg modules (reduce to Mathlib's
    `HomologicalComplex.homologySequence`). — done: `DG.cohomology`, `DG.cohomology.mk`, `DG.cohomology.mkOf`,
    `DG.cohomology.lift`, `DG.cohomology.map` (`map_id`, `map_comp`, `map_zero`, `map_add`),
    `DG.DGModuleHom.IsQuasiIso` (`isQuasiIso_id`, `IsQuasiIso.comp`,
    `IsQuasiIso.of_comp_left`, `IsQuasiIso.of_comp_right`), `DG.Cohomology`
    (`DG.Cohomology.instDGAddCommGroup`), `DG.cohomology.smulHom`, `DG.Cohomology.gring`,
    `DG.Cohomology.ring`, `DG.Cohomology.dgRing`, `DG.Cohomology.gmodule`,
    `DG.Cohomology.module`, `DG.Cohomology.dgModule`, `DG.cohomology.prodAddEquiv`
    (with `DG.Prod.instDGAddCommGroup`, `DG.Prod.instDGModule`),
    `DG.cohomology.directSumAddEquiv`; comparison with Mathlib's homology
    `DG.DGModuleCat.cohomologyAddEquiv`; the long exact sequence `DG.DGModuleCat.δ`,
    `DG.DGModuleCat.δ_mk`, `DG.DGModuleCat.cohomology_exact₁`, `DG.DGModuleCat.cohomology_exact₂`,
    `DG.DGModuleCat.cohomology_exact₃`, `DG.DGModuleCat.cohomologyAddEquiv_δ`.
2.6 Comparison with Mathlib's monoidal category: a `DGAlgebra R A` is the same as a monoid
    object `Mon (CochainComplex (ModuleCat R) ℤ)` and a dg module is a `Mod` object;
    equivalences of categories in both directions. Requires the monoidal structure of
    `Mathlib/Algebra/Homology/Monoidal.lean` with `ComplexShape.TensorSigns` for `ℤ`.
    **(Mathlib)**
    — done: `DG.DGAlgCat.monEquivalence`
    (`DGAlgCat R ≌ Mon (CochainComplex (ModuleCat R) ℤ)`), `DG.DGModuleCat.modEquivalence`
    (`DGModuleCat A ≌ Mod` of the corresponding monoid object), `DG.ComplexTensor.d_tmul`
    (Mathlib's tensor product of complexes has the library's sign); the instances
    `CategoryTheory.MonoidalPreadditive.curriedTensor_additive`,
    `DG.ModuleCat.preservesColimits_curriedTensor_obj` needed for Mathlib's monoidal structure on
    `CochainComplex (ModuleCat R) ℤ` to be found at the pinned revision.
2.7 Examples: the Koszul complex `K(x₁, …, xₙ)` on a commutative ring as a commutative dg
    algebra; `END_R(C)` for a cochain complex `C`; the free dg algebra on a graded set with
    prescribed differential (semi-free dg algebras); the truncations. **(stretch:** de Rham
    complex of a polynomial algebra.)
    — done (except the de Rham stretch goal): `DG.KoszulComplex` (for a linear form
    `φ : M → R`; `DG.KoszulComplex.ofElements x` is `K(x₁, …, xₙ)`), `DG.KoszulComplex.instDGAlgebra`,
    `DG.KoszulComplex.isGradedCommStrict`, `DG.KoszulComplex.ofElements.cohomologyZeroAddEquiv`
    (`H⁰ ≅ R ⧸ (x₁, …, xₙ)`); `DG.DGModule.END.instDGAlgebra`, `DG.DGModule.END.cohomologyZeroAddEquiv`
    (`H⁰(END_A(M))` = maps up to homotopy); `DG.truncLEZero`, `DG.bijective_cohomologyMap_truncLEZero`,
    `DG.truncGEZeroπ`, `DG.bijective_cohomologyMap_truncGEZeroπ`; `DG.SemiFree`
    (free dg algebra on graded generators with prescribed differential),
    `DG.freeDeriv_freeDeriv_eq_zero_iff`, `DG.SemiFree.liftEquiv`. The `R`-module structure on
    Hom complexes: `DG.Cochain.instModuleGround`, `DG.DGModule.END.instAlgebra`.

## Dg categories (the setting for tiers 3–7)

Tiers 3–7 are to be stated for small dg categories wherever possible, with dg algebras as the
one-object case (see `docs/CONVENTIONS.md`, "Dg categories"). The dg-algebra results of tier 3
already in the library are kept as the concrete one-object case and are to be identified with
the dg-category versions through the one-object equivalence.

D.1 Dg categories: the mixin `DGCategory`, dg functors, the opposite dg category (with the
    Koszul-signed composition), the categories `Z⁰(C)` and `H⁰(C)`, the one-object dg category
    `SingleObj A` of a dg ring, and the dg category `C_A` with objects `ℤ` and
    `C_A(k, l) = A⟨l - k⟩` attached to a dg ring `A` with an internal grading.
D.2 Dg modules over a dg category: the abelian category `DGModuleCat C`, representable modules
    and the dg Yoneda lemma (`Hom(C(X, -), M) ≅ Z⁰(M X)`, and the Hom complex version), the
    equivalence `DGModuleCat A ≌ DGModuleCat (SingleObj A)`, and the equivalence of the
    category of bigraded dg `A`-modules with `DGModuleCat C_A`.
    — D.1 done: `DG.DGCategory`, `DG.d_comp`, `DG.DGCategory.Z0`, `DG.DGCategory.H0`,
    `CategoryTheory.Functor.IsDGFunctor`, `DG.DGOpposite`, `DG.SingleObj.dgCategory_iff`,
    `DG.WeightCategory`, `DG.WeightCategory.shiftEquiv`. D.2 done (except the Hom-complex form of
    Yoneda): `DG.CatModule`, `DG.CatModule.abelian`, `DG.CatModule.hasCoproducts`,
    `DG.CatModule.eval`, `DG.CatModule.representable`, `DG.CatModule.yonedaEquiv`,
    `DG.CatModule.yonedaFullyFaithful`, `DG.CatModule.singleObjEquivalence`,
    `DG.CatModule.weightEquivalence`, `DG.BigradedDGModuleCat.internalShiftToCatModuleIso`.
    Also: the Hom-complex Yoneda lemma `DG.CatModule.yonedaHOM` (`HOM(C(X, -), M) ≅ M X`); right
    modules (`CatModule (DGOpposite C)`, `DG.CatModule.ract`), bimodules `DG.CatBimodule`, the tensor
    product `DG.CatTensorProduct` with `DG.CatTensorProduct.lid` (co-Yoneda) and
    `DG.CatTensorProduct.singleObjEquiv` (agrees with `⊗_A`), induction along a dg functor
    `DG.CatModule.induction` with `DG.CatModule.inductionAdjunction` and
    `DG.CatModule.inductionRepresentableIso`.
D.3 Tier 3 for dg modules over `C`: Hom complexes, shifts, cones, homotopies, the homotopy
    category, its triangulated structure, compatibility with the one-object case.
    — done: `DG.CatModule.Cochain`, `DG.CatModule.HOM`, `DG.CatModule.DGHomotopy`,
    `DG.CatModule.HomotopyCategory`, `DG.CatModule.HomotopyCategory.homAddEquivCohomology`,
    `DG.CatModule.hasShift`, `DG.CatModule.cone`, `DG.CatModule.HomotopyCategory.pretriangulated`,
    `DG.CatModule.HomotopyCategory.isTriangulated`, `DG.CatModule.HomotopyCategory.precomp_isTriangulated`
    (restriction along a dg functor), `DG.CatModule.HomotopyCategory.eval_isTriangulated`,
    `DG.CatModule.HomotopyCategory.cohomologyFunctor_isHomological`,
    `DG.CatModule.HomotopyCategory.singleObjEquivalence` (with `DG.HomotopyCategory A`).
    For `DG.DGLinear R C`, `DG.CatModule.instLinear` and
    `DG.CatModule.HomotopyCategory.instLinear` give `R`-linearity, including quotient and shift
    functors; the one-object comparison is linear (`toDGHomotopyCategory_linear`).
    `DG.CatModule.HOM.rightShiftEquiv` and `leftShiftEquiv` identify the Hom complexes into
    and out of shifts, with `homShiftAddEquivCohomology` on the homotopy category.
D.4 Tier 4 for `C`: acyclic modules, quasi-isomorphisms, the derived category `D(C)`,
    K-projective and semi-free modules (cells are shifts of representable modules), resolutions,
    derived functors along dg functors and bimodules, and Keller's theorem that a
    quasi-equivalence of dg categories induces a triangulated equivalence of derived categories
    [Ke, §9].
    — D.4 partly done: the derived category `DG.CatModule.DerivedCategory C` (triangulated
    localization at quasi-isomorphisms, `DG.CatModule.DerivedCategory.isIso_Q_map_iff`,
    `DG.CatModule.DerivedCategory.isZero_Q_obj_iff`, cohomology at each object homological,
    coproducts preserved by `Q`), `DG.CatModule.DerivedCategory.singleObjEquivalence`
    (`D(SingleObj A) ≌ D(A)`, triangulated), `DG.CatModule.DerivedCategory.restrict`
    (triangulated restriction along a dg functor); K-projective modules
    `DG.CatModule.IsKProjective`, `DG.CatModule.isKProjective_iff_isAcyclic_hom`,
    `DG.CatModule.isKProjective_representable`, `DG.CatModule.isKProjective_corner` (summands
    `e · C(X, -)` for degree-`0` cocycle idempotents), closure under retracts and homotopy
    equivalences. Resolutions: `DG.CatModule.exists_kProjective_resolution` (every `M` has an
    objectwise surjective quasi-isomorphism `P ⟶ M` from a K-projective `P`, built from shifted
    representables by iterated cones and a sequential colimit, `DG.CatModule.Resolution.colim`;
    `DG.CatModule.seqColimit`, `DG.CatModule.SeqColimit.isKProjective`);
    `DG.CatModule.DerivedCategory.Qh_map_bijective_of_isKProjective`,
    `DG.CatModule.DerivedCategory.homAddEquivOfIsKProjective` (`Hom_{D(C)}(P, N) ≅ H⁰ HOM(P, N)`),
    `DG.CatModule.isIso_quotient_map_of_isQuasiIso`,
    `DG.CatModule.DerivedCategory.kProjectiveEquivalence` (K-projectives of `H(C)` ≌ `D(C)`).
    Derived induction: `DG.CatModule.pathObj`, `DG.CatModule.homotopic_iff_homEquiv`,
    `DG.CatModule.IsKProjective.of_adjunction`, `DG.CatModule.DerivedCategory.induction`,
    `DG.CatModule.DerivedCategory.inductionAdjunction` (`LF_! ⊣ F^*`),
    `DG.CatModule.DerivedCategory.inductionObjIso` (`LF_! (Q P) ≅ Q (F_! P)` for K-projective `P`).
    Keller's theorem: `DG.IsQuasiEquivalence`, `DG.CatModule.DerivedCategory.kellerEquivalence`
    (`LF_! : D(C) ≌ D(D)` with quasi-inverse `F^*`, both triangulated;
    `DG.CatModule.DerivedCategory.induction_isTriangulated`), via
    `DG.CatModule.DerivedCategory.isIso_unit_app` (localizing argument with
    `compactlyGenerates`) and `DG.CatModule.DerivedCategory.isIso_counit_app`;
    `DG.CatModule.HasDerivedCategory.small` (a model of `D(C)` with small Hom sets).
    Semi-free modules: `DG.CatModule.SemiFreeFiltration` (cells shifted lifted representables),
    `DG.CatModule.FiniteCellFiltration` (cells shifted corners `e · C(X, -)`), both K-projective
    and with the lifting property (`DG.CatModule.hasLiftingProperty_iff`: lifting property ⟺
    K-projective ∧ graded-projective, the corrected form of 3.5); `Resolution.semiFreeFiltration`,
    `DG.CatModule.exists_semiFreeResolution`, the bundle `DG.CatModule.SemiFreeResolution` with
    uniqueness up to homotopy equivalence over `M` and functoriality up to homotopy
    (`SemiFreeResolution.dgHomotopyEquiv`, `lift`, `homotopic_lift`, `lift_comp`),
    `DG.CatModule.hasLiftingProperty_iff_exists_retract`,
    `DG.CatModule.isKProjective_iff_exists_dgHomotopyEquiv`.
    Derived functors along bimodules: `DG.CatBimodule.homFunctor` (`HOM_D(B, -)`),
    `DG.CatBimodule.tensorHomAdjunction` (`B ⊗_C - ⊣ HOM_D(B, -)` on dg modules),
    `DG.CatModule.HomotopyCategory.homFunctor` (triangulated), and, for bimodules `B` whose
    left modules `B(-, Y)` are K-projective, `DG.CatModule.DerivedCategory.derivedTensor`,
    `DG.CatModule.DerivedCategory.rhom` and `derivedTensorAdjunction` (`⊗^L ⊣ RHOM`, both
    triangulated, `⊗^L` preserves coproducts), `derivedTensorObjIso`, and
    `derivedTensorOfFunctorIso` (`D(F-, -) ⊗^L - ≅ LF_!`), `rhomOfFunctorIso`. Isomorphisms of dg
    bimodules (`DG.CatBimodule.Iso`) induce isomorphisms of Hom functors, `RHOM` and `⊗^L`
    (`CatBimodule.homFunctorIso`, `rhomIso`, `derivedTensorIso`; `derivedTensorIsoId` for bimodules
    isomorphic to the diagonal, `singleObjDerivedTensorIsoId` for dg rings;
    `DG/Category/Derived/TensorIso.lean`); derived induction along a quasi-isomorphism of dg rings is
    an equivalence (`DGRingHom.derivedInductionEquivalence`). Open: general
    bimodules (would need bimodule resolutions, i.e. tensor products of dg categories).
D.5 Tiers 5–7 for `C`: the representable modules are compact and generate `D(C)`, so the
    compact objects are the thick closure of the representables; `K₀(C)`; positive dg
    categories and Schnürer's theorem; the internal shift of tier 7 as the dg autoequivalence of
    `C_A` shifting objects by `1`.
    — D.5 partly done: `DG.CatModule.DerivedCategory.compactlyGenerates` (the representable
    modules `Q C(X, -)` compactly generate `D(C)`, `DG.CompactlyGenerates`), with
    `DG.CatModule.DerivedCategory.isCompact_Q_obj`,
    `DG.CatModule.DerivedCategory.isZero_of_forall_representable`, and
    `DG.CatModule.DerivedCategory.thickClosure_representable_eq_isCompact` (compact objects =
    thick closure of the representables). `K₀(C)`: `DG.CatModule.PerfectDerivedCategory`,
    `DG.DGCategory.K0` with `map` along dg functors (`map_representable`, `map_id`, `map_comp`),
    `mapEquivOfIsQuasiEquivalence`, `mk_mem_closure_representable` (classes of objects of the
    triangulated closure of the representables lie in their span; `K₀(C)` need not be generated
    by representables, e.g. `k × k` in degree `0`). Positive dg categories:
    `DG.DGCategory.IsPositive` ((P1) no negative degrees, (P2) identities are finite sums of
    orthogonal simple degree-`0` idempotents, (P3) `d = 0` in degree `0`;
    `DG.SingleObj.isPositive_iff`, `DG.WeightCategory.isPositive_iff`) and Schnürer's theorem
    for them: `DG.DGCategory.IsPositive.isCompact_iff`,
    `DG.DGCategory.IsPositive.exists_finiteCellFiltration_of_isCompact` (ordered cells
    `(e · C(X, -))⟦n⟧`, `e` simple); `K₀` is generated by simple corners
    (`DG.DGCategory.IsPositive.closure_cell_eq_top`).

## Tier 3 — The homotopy category

3.1 Homotopy between dg module maps (`f - g = d h + h d` with `h` of degree `-1`), the
    null-homotopic maps form an ideal; the homotopy category `H(A) := DGModuleCat A / ~`
    (`CategoryTheory.Quotient`), additive and `R`-linear; `Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`.
    — done: `DG.HomotopyCategory`, `DG.HomotopyCategory.quotient`,
    `DG.HomotopyCategory.instLinear`, `DG.HomotopyCategory.homAddEquivCohomology`
    (`Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`), `DG.HomotopyCategory.isZero_quotient_obj_iff`;
    `DG.DGHomotopy`, `DG.Homotopic`,
    `DG.homotopic_equivalence`, `DG.nullHomotopic`, `DG.comp_mem_nullHomotopic`,
    `DG.quotientNullHomotopicAddEquivCohomology`, `DG.DGHomotopy.cohomology_map_eq`,
    `DG.DGHomotopyEquiv.isQuasiIso_hom`, `DG.IsContractible.subsingleton_cohomology`.
3.2 Shift `[1]` on `DGModuleCat A` and on `H(A)` (`CategoryTheory.HasShift`, via
    `Mathlib`'s `hasShiftMk`), with `HOM_A(M, N[n]) ≅ HOM_A(M, N)[n]`.
    — done: `DG.DGModule.HOM.rightShiftEquiv` (`HOM_A(M, N[n]) ≅ HOM_A(M, N)[n]`),
    `DG.DGModule.HOM.leftShiftEquiv`, `DG.HomotopyCategory.homShiftAddEquivCohomology`
    (`Hom_{H(A)}(M, N[n]) ≅ Hⁿ(HOM_A(M, N))`), `DG.HomotopyCategory.shiftFunctor_linear`,
    `DG.DGModuleCat.hasShift`,
    `DG.HomotopyCategory.hasShift`, `DG.HomotopyCategory.commShiftQuotient`,
    `DG.DGModuleCat.forgetCommShift` (the shift agrees with Mathlib's on underlying complexes);
    `DG.Shift`, `DG.Shift.instDGModule`,
    `DG.DGModuleHom.shift`, `DG.Shift.zeroEquiv`, `DG.Shift.addEquiv`.
3.3 Mapping cone `C(f) = N ⊕ M[1]`, the standard triangle `M → N → C(f) → M[1]`, and the
    pretriangulated structure on `H(A)` **(Mathlib)**: distinguished triangles are those
    isomorphic to standard ones; verify the axioms TR1–TR4 following Mathlib's
    `HomotopyCategory.Pretriangulated`/`Triangulated` files for cochain complexes (the proofs
    are the same with `A`-linearity carried along). `H(A)` is triangulated (octahedral axiom).
    — done: `DG.HomotopyCategory.pretriangulated`, `DG.HomotopyCategory.isTriangulated`,
    `DG.Cone.triangle`, `DG.HomotopyCategory.triangleh_distinguished`,
    `DG.Cone.rotateHomotopyEquiv`, `DG.Cone.shiftTriangleIso`,
    `DG.HomotopyCategory.mappingConeCompTriangleh_distinguished`; `DG.Cone`, `DG.Cone.instDGModule`,
    `DG.Cone.inr`, `DG.Cone.fstHom`, `DG.Cone.map`; the cochain-level API ported from
    Mathlib's `MappingCone.lean` with identical signs: `DG.Cone.inl`, `DG.Cone.fst`,
    `DG.Cone.snd`, `DG.Cone.δ_inl`, `DG.Cone.δ_snd`, `DG.Cone.desc`, `DG.Cone.lift`,
    `DG.Cone.descHomotopy`, `DG.Cone.liftHomotopy`, `DG.Cone.mapOfHomotopy`,
    `DG.Cone.isContractible_id`, `DG.Cone.mappingConeCompHomotopyEquiv`; shifts of cochains
    `DG.Cochain.rightShift`, `DG.Cochain.leftShift`, `DG.Cochain.shift`, `DG.δ_rightShift`,
    `DG.δ_leftShift`.
3.4 The forgetful functor `H(A) ⥤ HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)`
    commutes with shifts and cones, hence is a triangulated functor; `H` is a homological
    functor on `H(A)`.
    — done: `DG.HomotopyCategory.forget`, `DG.HomotopyCategory.forget_isTriangulated`,
    `DG.Cone.forgetTriangleIso` (the cone agrees with Mathlib's `mappingCone`),
    `DG.HomotopyCategory.homologyFunctor_isHomological`, `DG.HomotopyCategory.forget_linear`,
    `DG.HomotopyCategory.homologyFunctorIso` (Mathlib's homology agrees with `DG.cohomology`).
3.5 Special modules: K-projective (cofibrant) modules (`Hom_{H(A)}(P, N) = 0` for all acyclic
    `N`; equivalently the lifting property against surjective quasi-isomorphisms; prove the
    equivalence), semi-free modules (union of an exhaustive filtration with subquotients
    direct sums of shifts of `A`), finite-cell modules (finite filtration with subquotients
    direct summands `Ae[n]` of shifts of `A` for degree-`0` idempotents `e` with `d e = 0`).
    Semi-free ⟹ K-projective; direct summands and shifts of K-projectives are K-projective;
    `A` and finite-cell modules are K-projective. [Ke §3], [BL 10.12], [St].
    **Erratum.** The "equivalently" above is false as stated: the lifting property against
    surjective quasi-isomorphisms is equivalent to being K-projective *and* projective as a
    graded module (`DG.hasLiftingProperty_iff`). Counterexample to the literal statement: over
    `A = ℤ` in degree `0`, the cone of the identity of `ℚ` is contractible, hence K-projective,
    but not graded-projective, so it lacks the lifting property.
    — done (concrete level; statements in terms of homotopy classes of maps rather than the
    bundled category): `DG.IsAcyclic`, `DG.IsKProjective`,
    `DG.isKProjective_iff_isAcyclic_hom`, `DG.isKProjective_self`, `DG.IsKProjective.shift`,
    `DG.IsKProjective.of_retract`, `DG.IsKProjective.directSum`, `DG.IsKProjective.cone`,
    `DG.DGIdempotent.isKProjective_leftCorner`, `DG.SemiFreeFiltration`,
    `DG.SemiFreeFiltration.isKProjective`, `DG.FiniteCellFiltration`,
    `DG.FiniteCellFiltration.isKProjective`, `DG.IsGradedProjective`, `DG.HasLiftingProperty`,
    `DG.hasLiftingProperty_iff`, `DG.SemiFreeFiltration.hasLiftingProperty`.
3.6 For `P` K-projective, `HOM_A(P, -)` preserves quasi-isomorphisms and
    `Hom_{H(A)}(P, N) ≅ Hom_{H(A)}(P, N')` along a quasi-isomorphism `N → N'`.
    — done (concrete level): `DG.DGModuleHom.isQuasiIso_iff_isAcyclic_cone`,
    `DG.IsKProjective.bijective_cohomology_postcomp`, `DG.IsKProjective.postcompHomotopyEquiv`.

## Tier 4 — The derived category

4.1 Quasi-isomorphisms in `H(A)` are the morphisms whose cone is acyclic; the acyclic
    modules form a thick triangulated subcategory; the class of quasi-isomorphisms is
    compatible with the triangulation (a multiplicative system in Verdier's sense). Use
    Mathlib's `Triangulated.Subcategory` and `Localization.Triangulated`.
    — done (for dg rings): `DG.HomotopyCategory.quasiIso`, `DG.HomotopyCategory.subcategoryAcyclic`,
    `DG.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`,
    `DG.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff` (and Mathlib's instances: calculus
    of fractions, compatibility with the triangulation).
4.2 `D(A) := H(A)[qis⁻¹]` via `CategoryTheory.Localization`, with a `HasDerivedCategory`-style
    class for a chosen small model; `D(A)` is triangulated and `H(A) ⥤ D(A)` is a
    triangulated localization functor; it has arbitrary coproducts, preserved by the
    localization functor.
    — done (for dg rings): `DG.HasDerivedCategory`, `DG.DerivedCategory`, `DG.DerivedCategory.Qh`,
    `DG.DerivedCategory.Q`, `DG.DerivedCategory.pretriangulated`, `DG.DerivedCategory.isTriangulated`,
    `DG.DerivedCategory.isIso_Q_map_iff`, `DG.DerivedCategory.isZero_Q_obj_iff`,
    `DG.DerivedCategory.homologyFunctor_isHomological`, `DG.DerivedCategory.hasCoproducts`,
    `DG.DerivedCategory.Q_preservesCoproducts`; `DG.HomotopyCategory.quotient_isLocalization`.
4.3 Existence of K-projective (semi-free) resolutions: every dg module `M` admits a
    surjective quasi-isomorphism `P → M` with `P` semi-free (the standard iterated-cone or
    telescope construction, [Ke §3.1], [BL 10.12.2.4], [St, "Resolutions"]). Uniqueness up
    to homotopy equivalence over `M`. Consequently the K-projective modules form a full
    subcategory of `H(A)` equivalent to `D(A)`, and `Hom_{D(A)}(M, N) ≅ H⁰(HOM_A(P_M, N))`.
    Dually **(stretch)**: K-injective resolutions.
    — done (concrete level, before `D(A)`): `DG.exists_semiFreeResolution` (a surjective
    quasi-isomorphism from a semi-free module, [St 09KP]), `DG.SemiFreeResolution`,
    `DG.SemiFreeResolution.dgHomotopyEquiv` (uniqueness up to homotopy equivalence over `M`),
    `DG.SemiFreeResolution.lift`, `DG.SemiFreeResolution.homotopic_lift`;
    `DG.hasLiftingProperty_iff_exists_retract` (cofibrant = retract of semi-free),
    `DG.isKProjective_iff_exists_dgHomotopyEquiv`.
4.4 Derived functors: `M ⊗^L_B -` and `RHOM_A(M, -)` for a dg `(A, B)`-bimodule `M`, defined
    on `D(B)` resp. `D(A)` via K-projective resolutions, well defined up to canonical
    isomorphism, triangulated; the derived tensor–Hom adjunction; compatibility with shifts
    and coproducts. Induction `φ^* = A ⊗^L_B -` and restriction `φ_* = RHOM_A(A, -)` (which is
    the underived restriction of scalars) along a `DGAlgHom φ : B → A`, and `φ^* ⊣ φ_*`.
    — done in the dg-category setting (see D.4) for bimodules `B` with K-projective left
    modules; for a dg ring map `φ : B → A`: `DG.DGRingHom.derivedInduction`,
    `DG.DGRingHom.derivedRestriction`, `DG.DGRingHom.derivedInductionAdjunction` (`φ^* ⊣ φ_*`),
    `DG.DGRingHom.derivedInductionIsoDerivedTensor` (`φ^* ≅ A ⊗^L_B -`). On K-projective dg
    modules `φ^*` is extension of scalars: `φ^*(P) ≅ A ⊗_B P` (`DG.DGRingHom.derivedInductionObjIso`,
    via `DG.DGRingHom.extendScalarsCompToCatModuleIso` and `DG.IsKProjective.toCatModuleObj`), and
    `K₀(φ) [P] = [A ⊗_B P]` for `P` also compact (`DG.DGRing.K0.map_mk_of_isKProjective`). For a
    dg `(A, B)`-bimodule `M` over dg rings, K-projective as a left module: `M ⊗^L_B - : D(B) ⥤ D(A)`
    (`DG.DGBimodule.derivedTensor`, triangulated), `M ⊗^L_B B ≅ M` (`DG.DGBimodule.derivedTensorSelfIso`),
    preserving compact objects when `M` is compact (`DG.DGBimodule.isCompact_derivedTensor_obj`, via
    `DG.DerivedCategory.isCompact_obj_of_isCompact_self`). Open: identification of `φ_*` with
    derived restriction of scalars on `DGModuleCat`.
4.5 Keller's theorem [Ke, Ex. 6.1], [BL 10.12.5.1]: if `φ : B → A` is a quasi-isomorphism of dg
    algebras, `φ^*` and `φ_*` are mutually inverse triangulated equivalences `D(B) ≃ D(A)`.
    Corollary: for a dg algebra `A`, the following are equivalent: `D(A) ≃ 0`; `H(A) = 0`;
    there is `x ∈ A` with `d x = 1`. (`H(A) = 0 ⟹ D(A) ≃ 0` by Keller applied to `0 → A`;
    `d x = 1 ⟹ H(A) = 0` by `d(x y) = y - x d y`.)
    — done: `DG.DGRingHom.derivedEquivalence` (`D(B) ≌ D(A)` for a quasi-isomorphism `B → A`,
    obtained from Keller's theorem for `SingleObj B ⥤ SingleObj A`,
    `DG.DGRingHom.isQuasiEquivalence_singleObjFunctor`, and `D(SingleObj A) ≌ D(A)`);
    `DG.DerivedCategory.tfae_isZero` (the corollary; `d x = 1` makes every dg module acyclic,
    `DG.IsAcyclic.of_exists_d_eq_one`, so Keller's theorem is not needed there).
4.6 Comparison with Mathlib **(Mathlib)**: for `A = R` concentrated in degree `0`, `D(A)` is
    equivalent to Mathlib's `DerivedCategory (ModuleCat R)` as triangulated categories.
    More generally `D(A)` for a graded ring with zero differential vs. the derived category of
    graded modules **(stretch)**.
    — done (except the graded stretch): `DG.DGModuleCat.cochainComplexEquivalence`,
    `DG.HomotopyCategory.comparisonEquivalence` (triangulated), `DG.DerivedCategory.comparisonEquivalence`
    (`D(R) ≌ DerivedCategory (ModuleCat R)`, with `DG.DerivedCategory.comparison_isTriangulated`);
    `R` in degree `0` via the scoped instances of `DG.DegreeZero`.
4.7 **(stretch)** dg categories: the definitions of tiers 2–4 for a small dg category `𝒜`
    (Keller's setting), with a dg algebra as the one-object case; the dg category of dg
    modules and its `HOM` complexes; the Yoneda dg functor. This is the natural level of
    generality for Mathlib; consider designing tier 2–4 statements so that the dg-category
    versions are obtained by a change of the indexing type rather than by re-proof.

## Tier 5 — Compact objects and Grothendieck groups

5.1 Compact objects of an additive category with arbitrary coproducts: `Hom(M, -)` commutes
    with coproducts **(Mathlib)**. In a triangulated category with coproducts the compact
    objects form a thick triangulated subcategory `𝒯^c`; shifts, cones and direct summands of
    compacts are compact. — done: `DG.IsCompact`, `DG.coproductComparison`,
    `DG.isCompact_iff_preservesColimitsOfShape`, `DG.IsCompact.of_retract`,
    `DG.IsCompact.of_iso`, `DG.isCompact_biprod_iff`, `DG.IsCompact.shift`,
    `DG.isCompact_shift_iff`, `DG.IsCompact.ext₁`, `DG.IsCompact.ext₂`, `DG.IsCompact.ext₃`,
    `DG.compactSubcategory`, `DG.compactSubcategory_of_retract`.
5.2 The perfect derived category `D^c(A) := D(A)^c`. `A` is compact in `D(A)` (since
    `Hom_{D(A)}(A[n], N) ≅ H^{-n}(N)` commutes with coproducts); hence every finite-cell module
    is compact; more generally the thick subcategory generated by `A` consists of compacts.
    — done: `DG.DerivedCategory.isCompact_Q_self`, `DG.DerivedCategory.compactlyGenerates`,
    `DG.PerfectDerivedCategory`, `DG.DerivedCategory.isCompact_Q_leftCorner`,
    `DG.FiniteCellFiltration.isCompact_Q_obj`; `DG.IsCompact.map_of_adjunction`.
5.3 Keller/Neeman: the compact objects of `D(A)` are exactly the objects of the thick
    subcategory generated by `A` [Ke, Thm 5.3], [Ne]. Requires: `D(A)` is compactly generated
    by `A`, and Neeman's theorem that in a compactly generated triangulated category the
    compacts are the thick closure of the generators (a Brown-representability argument, or
    the "smashing" argument of [Ne, Thm 2.1]). **(stretch if 5.6 can be reached without it;**
    see tier 6.)
    — done (abstract part, for a triangulated category compactly generated by a set; the
    application to `D(A)` remains): `DG.IsThick`, `DG.ThickClosure`, `DG.thickClosure`,
    `DG.thickClosure_le`, `DG.isThick_isCompact`, `DG.thickClosure_le_isCompact`
    (`DG/Compact/Thick.lean`); `DG.hocolim`, `DG.hocolimι`, `DG.hocolim_exists_desc`,
    `DG.hocolim_exists_factor`, `DG.hocolim_exists_eq_of_comp_eq`
    (`DG/Compact/HomotopyColimit.lean`); `DG.CompactlyGenerates`, `DG.thickClosure_of_isCompact`,
    `DG.thickClosure_eq_isCompact` (`DG/Compact/Generation.lean`).
    — application to `D(A)` done: `DG.DerivedCategory.thickClosure_self_eq_isCompact`.
5.4 The Grothendieck group `K₀(𝒯)` of a triangulated category (or of an essentially small
    triangulated category): free abelian group on isomorphism classes modulo `[N] = [M] + [L]`
    for distinguished triangles `M → N → L → M[1]` **(Mathlib)**. Functoriality along
    triangulated functors, `[M[1]] = -[M]`, `[M ⊕ N] = [M] + [N]`, invariance under
    triangulated equivalences, additivity over finite filtrations (iterated cones), the
    Euler characteristic of a bounded complex with values in `K₀` of an abelian category
    (comparison with Mathlib's derived category of an abelian category where possible).
    — done: `DG.K0`, `DG.K0.mk`,
    `DG.K0.lift`, `DG.K0.mk_obj₂`, `DG.K0.mk_eq_of_iso`, `DG.K0.mk_shift_one`,
    `DG.K0.mk_shift`, `DG.K0.mk_biprod`, `DG.K0.mk_last_eq_add_sum`, `DG.K0.map`,
    `DG.K0.map_id`, `DG.K0.map_comp`, `DG.K0.mapEquiv` (`DG/K0/Triangulated.lean`);
    `DG.AbelianK0`, `DG.AbelianK0.mk_X₂`, `DG.AbelianK0.lift`, `DG.AbelianK0.map`,
    `DG.AbelianK0.mapEquiv` (`DG/K0/Abelian.lean`); `DG.AbelianK0.eulerChar`,
    `DG.AbelianK0.eulerChar_eq_finsum_homology`, `DG.AbelianK0.eulerChar_X₂`,
    `DG.AbelianK0.eulerChar_eq_zero_of_exactAt`, `DG.AbelianK0.toDerived`,
    `DG.AbelianK0.toDerived_eulerChar`, `DG.K0.mk_Q_obj_eq_toDerived` (`DG/K0/Euler.lean`;
    Mathlib has no bounded derived category at the pin, so the comparison is the map
    `K₀(C) → K₀(D(C))` and its compatibility with `χ`).
5.5 `K₀(A) := K₀(D^c(A))`; functoriality along dg algebra maps (induction preserves compacts);
    invariance under quasi-isomorphisms of dg algebras (from 4.5); for a finite-cell module
    with subquotients `A e_i [n_i]`, `[M] = Σ (-1)^{n_i} [A e_i]`.
    — done: `DG.DGRing.K0`, `DG.DGRing.K0.map` (with `map_self`, `map_id`, `map_comp`,
    `map_leftCorner`), `DG.DGRing.K0.mapEquivOfIsQuasiIso`, `DG.DGRing.K0.mk_finiteCell`
    (`[M] = Σ (-1)^{nᵢ} [A eᵢ]`), `DG.K0.compactMapEquiv`, `DG.K0.mapCompact`.
5.6 Computations: `K₀` of a field `k` in degree `0` is `ℤ`, generated by `[k]` (every object
    of `D^c(k)` is a finite direct sum of shifts of `k`; compact ⟺ finite total dimension);
    `K₀(R) ≅ K₀(R\text{-proj})` for a ring `R` in degree `0` (perfect complexes; reduce to
    Mathlib where possible) **(stretch)**; Künneth-type statement
    `K₀(A ⊗_k B) ≅ K₀(A) ⊗ K₀(B)` under hypotheses to be determined from tier 6 (positive dg
    algebras over a field).
    — done for a field: `DG.DGRing.K0.equivIntOfField : K₀(k) ≃+ ℤ`, `[k] ↦ 1`, via the Euler
    characteristic of total cohomology; `DG.DerivedCategory.isCompact_iff_hasFiniteCohomology`.
    `DG.DerivedCategory.nonempty_iso_shiftSum_of_isCompact`: every compact object of `D(k)` is
    a finite direct sum of shifts of `k`.
    — perfect-complex step for general rings: `DG.IsPerfect.isThick` and
    `DG.perfectK0Equiv : K₀(D^perf(R)) ≃+ DG.ProjK0 R` in Mathlib's derived
    category (`DG/Derived/PerfectThick.lean`, `DG/K0/PerfectComplex.lean`).
    — compacts are perfect complexes: for any ring, the perfect objects are the thick closure
    of `R[0]` (`DG.IsPerfect.thickClosure_eq`, `DG.IsPerfect.le_of_isThick`); for a commutative
    ring `R`, an object of `D(R)` is compact iff its image under
    `DG.DerivedCategory.comparisonEquivalence` is perfect
    (`DG.DerivedCategory.isCompact_iff_isPerfect`), hence
    `DG.DGRing.K0.projK0Equiv : K₀(R) ≃+ DG.ProjK0 R` with `[R] ↦ [R]`
    (`DG.DGRing.K0.projK0Equiv_self`; `DG/Derived/PerfectCompact.lean`,
    `DG/K0/PerfectCompact.lean`).
    Open: the same for non-commutative rings (needs a comparison
    `DGModuleCat S ≌ CochainComplex (ModuleCat S) ℤ` for a ring `S` in degree `0`);
    remaining stretch items.
    — `K₀(ℤ) ≃ ℤ`: the rank `DG.ProjK0.rankEquiv : DG.ProjK0 R ≃+ ℤ` when finitely generated
    projective modules are free, hence `DG.DGRing.K0.rankEquiv`, `[R] ↦ 1`, with the instances
    `DG.DGRing.K0.equivIntOfIsPrincipalIdealRing` (e.g. `R = ℤ`) and
    `DG.DGRing.K0.equivIntOfIsLocalRing` (`DG/K0/ProjectiveRank.lean`).

## Tier 6 — Positive dg algebras (Schnürer)

6.1 Definition: `A` is positive if `Aⁿ = 0` for `n < 0`, `A⁰` is a semisimple ring, and
    `d = 0` on `A⁰` (equivalently `d : A⁰ → A¹` vanishes). Basic consequences: the
    degree-`0` idempotents of `A⁰` are cocycles, `A e` is a finite-cell module for each such
    `e`, the truncations `A^{≥ n}` are dg ideals.
    — done: `DG.DGIdempotent.finiteCellFiltration` (`A e` is finite-cell), `DG.IsPositive`
    (conditions (P1)–(P3) of [Sch, §1]), `DG.IsPositive.degreeZero`, `DG.IsPositive.dgIdempotent`,
    `DG.IsPositive.degreeZeroDGSubring`, `DG.IsPositive.projZero`, `DG.IsPositive.ker_projZero`,
    `DG.IsPositive.quotientTruncGEOneEquiv`, `DG.truncGE`, `DG.IsPositive.cohomologyZeroEquiv`,
    `DG.IsPositive.subsingleton_cohomology_of_neg`.
6.2 Schnürer's theorem [Sch, Thm. 1, proved as Thms. 13 and 16; numbering of arXiv:0809.4782v2]
    (Schnürer works over a commutative ring `k`, with right dg modules; left dg modules over
    `A` are right dg modules over the graded opposite, which is positive when `A` is, so no
    field hypothesis is needed for this item): for a positive dg algebra `A`, a
    dg module is compact in `D(A)` iff it is isomorphic in `D(A)` to a finite-cell module
    (Schnürer: `D^c(A)` is the thick closure of the modules `A e` with `e` a primitive
    idempotent of `A⁰`, and every object of this thick closure is isomorphic to a finite-cell
    module, via the weight/t-structure argument of [Sch §§3–5]). Follow [Sch] closely; note
    the proof uses the non-positive truncation t-structure on `D(A)` for `A` positive and the
    finiteness of `A⁰`-modules.
    — done: `DG.IsPositive.isCompact_iff`, `DG.IsPositive.isCompact_Q_obj_iff` (compact ⟺
    isomorphic in `D(A)` to a module with an ordered finite-cell filtration),
    `DG.IsPositive.exists_finiteCellFiltration_of_isCompact` (cells `A e` with `e` simple), via
    cell towers (`DG.CellTower`, `DG.IsOrderedCellFamily.isThick`) and
    `DG.GradedSplitting.exists_distinguished`. Deviation from [Sch]: closure under direct
    summands is proved directly in `D(A)` by induction on ordered cell towers (the route via
    Prop 31 / Cor 32 is circular, its (iii) ⇒ (i) using Thm 16), avoiding Le–Chen.
6.3 Corollary: `K₀(A) ≅ K₀(A⁰)` for `A` positive over a field, the isomorphism sending
    `[A e]` to `[A⁰ e]`, and `K₀(A)` is free on the classes of the `A e` for a complete set of
    primitive orthogonal idempotents of `A⁰` up to isomorphism. In particular
    `K₀(A) ≅ ℤ` when `A⁰ = k`.
    — done, with no field or finiteness hypothesis: `DG.IsPositive.K0DegreeZeroEquiv`
    (`K₀(A) ≃+ K₀(A⁰)`, `[A e] ↦ [A⁰ e]`), `DG.IsPositive.basis` (free on the classes `[A e]`
    of simple idempotents up to `DG.DGIdempotent.Equiv`, i.e. `A⁰ e ≅ A⁰ f`,
    `DG.idemEquiv_iff_nonempty_linearEquiv`), `DG.IsPositive.K0EquivIntOfDivisionRing`,
    `DG.IsPositive.K0EquivIntOfField`; via `DG.IsSemisimpleCellFamily.basis` and Euler
    characteristics of homological functors over division rings (`DG.Homological.eulerChar`).
    Extension of scalars from `ℤ` (`DG/Positive/ScalarExtension.lean`): for a commutative ring `K`
    and a dg ring `A`, `K ⊗ A = K ᵍ⊗[ℤ] A` (`DG.ExtendScalars`, `K` in degree `0`) is a dg
    `K`-algebra (`DG.ExtendScalars.algebra`, `dgAlgebra`, via the central elements `k ⊗ 1`) with
    the dg ring map `DG.ExtendScalars.unitHom : A → K ⊗ A`; its degree-`0` part is `K ⊗_ℤ A⁰`
    (`DG.ExtendScalars.degreeZeroEquiv`). If `Aⁿ = 0` for `n < 0`, `d(A⁰) = 0` and `K ⊗_ℤ A⁰` is
    semisimple, then `K ⊗ A` is positive (`DG.ExtendScalars.isPositive_of_isSemisimpleRing`; `A⁰`
    itself need not be semisimple), so 6.3 computes `K₀(K ⊗ A)`. If `A⁰ = ℤ · 1` (not positive:
    `ℤ` is not semisimple), `K ⊗ A` is positive for `K` semisimple (`DG.ExtendScalars.isPositive`),
    and `K₀(K ⊗ A) ≃ ℤ`, `[K ⊗ A] ↦ 1`, when `K` is a field and `1` has infinite order in `A`
    (`DG.ExtendScalars.K0EquivInt`). Base change of dg modules
    (`DG/Positive/ScalarExtensionModule.lean`): `K ⊗_ℤ M` is a dg `K ⊗ A`-module, the external
    tensor product of `K` and `M` (`DG.ExtendScalars.baseChange`), and it is extension of scalars
    along `unitHom`: `(K ⊗ A) ⊗_A M ≅ K ⊗_ℤ M`, `x ⊗ m ↦ x • (1 ⊗ m)`
    (`DG.ExtendScalars.extendScalarsEquiv`), naturally in `M` (`DG.ExtendScalars.extendScalarsIso`).
    Derived: derived induction along `unitHom` is `K ⊗_ℤ -` on K-projective modules
    (`DG.ExtendScalars.derivedInductionObjIso`), and `K₀(unitHom) [P] = [K ⊗_ℤ P]` for `P`
    K-projective and compact (`DG.ExtendScalars.K0_map_mk`). Extension of scalars and base change
    preserve K-projectivity (`DG.IsKProjective.extendScalars`, `DG.ExtendScalars.isKProjective_baseChange`).
    Bimodules (`DG/Positive/ScalarExtensionBimodule.lean`): for a dg `(A, B)`-bimodule `X`, `K ⊗_ℤ X`
    is a dg `(K ⊗ A, K ⊗ B)`-bimodule (`DG.ExtendScalars.instDGBimodule`), with left module the base
    change of `X` and right action `(x ⊗ m) • (k ⊗ b) = x k ⊗ m b`. Derived tensor products
    (`DG/Positive/ScalarExtensionTensor.lean`): `(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B) ≅ K ⊗_ℤ X`
    (`DG.ExtendScalars.derivedTensorBaseChangeSelfIso`) and, for `X` compact in `D(A)`,
    `[(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B)] = K₀(unitHom) [X ⊗^L_B B]` (`DG.ExtendScalars.K0_mk_derivedTensor_self`).
    Open: a natural isomorphism `(K ⊗ X) ⊗^L_{K ⊗ B} unitHom^*(-) ≅ unitHom^*(X ⊗^L_B -)`.
6.4 Formality: a dg algebra `A` is formal if it is connected to `H(A)` (zero differential) by
    a zigzag of quasi-isomorphisms; Keller's theorem then gives `D(A) ≃ D(H(A))` and
    `K₀(A) ≅ K₀(H(A))`. Criterion: if `H(A)` is a free (super)commutative graded algebra on
    homogeneous cocycle representatives, or more generally if a graded algebra map
    `H(A) → A` splitting the cocycles exists, then `A` is formal (via the direct quasi-
    isomorphism `H(A) → A`). Transfer of positivity along quasi-isomorphisms where it holds.
    — done: `DG.QuasiIsomorphic`, `DG.IsFormal`, `DG.IsFormal.nonempty_derivedEquivalence`
    (`D(A) ≌ D(H(A))`), `DG.IsFormal.nonempty_K0_addEquiv`, the criterion
    `DG.isFormal_of_isCohomologySection` (a dg ring map `H(A) → A` sending each class to a
    representing cocycle), `DG.IsPositive.cohomology`. The free graded-commutative criterion is
    proved for strictly graded-commutative dg algebras (`DG.isFormal_of_isFreeGradedCommAlgebra`),
    or graded-commutative dg algebras when `2` is invertible
    (`DG.isFormal_of_isFreeGradedCommAlgebra_of_isGradedComm`). Graded commutativity alone does
    not ensure square-zero cocycle representatives for odd generators.
6.5 Künneth for positive dg algebras over a field: `K₀(A ⊗_k B) ≅ K₀(A) ⊗_ℤ K₀(B)` when `A`,
    `B` (hence `A ⊗ B`) are positive, from 6.3 and `K₀` of tensor products of semisimple
    algebras.
    — Erratum: without a splitting hypothesis the statement is false (`ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` gives
    `ℤ²` vs `ℤ`), and `A ⊗ B` need not be positive (for a purely inseparable extension `K` of
    `𝔽_p(t)`, `K ⊗ K` is not semisimple). Repaired statement, done:
    `DG.IsPositive.K0KunnethEquiv : K₀(A) ⊗[ℤ] K₀(B) ≃ₗ[ℤ] K₀(A ⊗_k B)`,
    `[A e] ⊗ [B f] ↦ [(A ⊗ B)(e ⊗ f)]`, when `A⁰`, `B⁰` are split semisimple over `k`
    (`IsSplitSemisimple`: `e A⁰ e = k e` for simple `e`); `DG.IsPositive.tensorProduct`,
    `DG.isSemisimpleRing_tensorProduct`. The isomorphism is induced by the derived external tensor
    product (`DG.DerivedCategory.K0ExternalTensorOver_eq_K0KunnethEquiv`; see Tier 8).

## Tier 7 — Internal gradings

7.1 Bigraded dg algebras: an additional `ℤ`-grading ("internal" or "weight" grading) on `A`
    preserved by `d`, `∂`-compatible with the product; bigraded dg modules; the internal shift
    `M⟨1⟩` as an autoequivalence of `DGModuleCat A`, `H(A)` and `D(A)`, commuting with `[1]`,
    triangulated. Compact objects and `K₀` in the bigraded setting; `K₀(A)` is a
    `ℤ[q, q⁻¹]`-module via `q [M] = [M⟨1⟩]`.
    — done (on dg modules and the module category; not yet on the homotopy or derived category
    or `K₀`): `DG.InternalGrading`, `DG.BigradedDGRing`, `DG.BigradedDGModule`, `DG.bigrading`,
    `DG.isInternal_inf_iff`, `DG.InternalShift`, `DG.InternalShift.shiftEquiv`
    (`M[n]⟨k⟩ ≅ M⟨k⟩[n]`, no sign), `DG.BigradedDGModuleCat`,
    `DG.BigradedDGModuleCat.internalHasShift`, `DG.BigradedDGModuleCat.internalShiftShiftIso`,
    `DG.cohomology.wgrading`, `DG.cohomology.internalShiftAddEquiv`.
    — done on `H(C_A)`, `D(C_A)` and `K₀` (via the weight dg category): the internal shift
    `⟨s⟩` as restriction along `k ↦ k + s`, `DG.CatModule.DerivedCategory.internalShift`
    (triangulated, `internalShiftAddIso`, `internalShiftEquiv`, `internalShiftShiftIso`,
    compatible with modules via `toCatModuleCompInternalShiftIso`), preservation of compact
    objects (`isCompact_internalShift_obj_iff`), and the `ℤ[q, q⁻¹]`-module structure on `K₀` of
    `H(C_A)`, `D(C_A)` and `D(C_A)^c` with `qⁿ • [M] = [M⟨n⟩]` (`DG.TriangulatedIntAction`,
    `DerivedCategory.T_smul_mk`, `T_smul_mk_compact`); functoriality of restriction
    (`DG.CatModule.DerivedCategory.restrictCompIso`, `restrictNatIso`). Coherence of the
    ℤ-action beyond isomorphism classes is not formalized.
7.2 Positive bigraded dg algebras, in two versions, both to be proved:
    (a) *graded*: `Aⁿ = 0` for `n < 0`, `d = 0` on `A⁰`, and `A⁰` (the homological degree-`0` part,
    graded by weight) is graded semisimple (every graded `A⁰`-module is a direct sum of graded
    simple modules). Obtained from Schnürer's theorem for positive dg categories (D.5) applied to
    the weight dg category `C_A` of D.1, whose degree-`0` category has semisimple module category
    exactly when `A⁰` is graded semisimple. Conclusions: compact objects of `D(A)` are the
    finite-cell modules (cells shifted in both gradings); `K₀(A) ≅ K₀(A⁰)` as `ℤ[q, q⁻¹]`-modules.
    Here `K₀(A⁰)` need not be free: a graded simple module isomorphic to its shift `⟨d⟩` (e.g. over
    a graded division ring with a unit of weight `d`) contributes `ℤ[q, q⁻¹]/(q^d - 1)`.
    (b) *ungraded*: as (a) with `A⁰` semisimple as a ring. Deduced from (a) via "semisimple implies
    graded semisimple" (the degree-`0` component of a projection onto a graded submodule is a
    graded projection), with the sharper conclusion that `K₀(A) ≅ K₀(A⁰)` is free over
    `ℤ[q, q⁻¹]` on the classes of the simple `A⁰`-modules up to shift; `K₀(k) ≅ ℤ[q, q⁻¹]` for a
    field `k` in bidegree `(0, 0)`. Also: for `A⁰` finite-dimensional over a field the two
    hypotheses coincide.
    — (a) done for `D(C_A)`: `DG.IsGradedSemisimpleRing`, `DG.IsGradedPositive`,
    `DG.IsGradedPositive.isCompact_iff`, `DG.IsGradedPositive.exists_finiteCellFiltration_of_isCompact`
    (cells shifted in both gradings), `DG.IsGradedPositive.span_cell_eq_top` (`K₀(C_A)` is
    generated over `ℤ[q, q⁻¹]` by the classes `[A e]`, `e` graded simple;
    `DG.WeightCategory.T_smul_cell`). (b) done in part: `DG.isGradedSemisimpleRing_of_isSemisimpleRing`,
    `DG.IsPositive.isCompact_iff_weight`, and the coincidence of hypotheses
    `DG.isGradedPositive_iff_isPositive` (for `A⁰` finite-dimensional over a field; more
    generally `DG.isSemisimpleRing_of_isGradedSemisimpleRing` for gradings bounded below).
    `DG.IsGradedPositive.K0DegreeZeroEquiv` proves `K₀(C_A) ≅ K₀(C_{A⁰})` over `ℤ[q, q⁻¹]`.
    With `A⁰` Artinian, `DG.IsGradedPositive.laurentBasis` proves freeness on graded simple
    idempotents up to shift (in particular `DG.IsPositive.laurentBasis` in case (b)); no such
    freeness is claimed from graded semisimplicity alone in (a).
    `DG.IsPositive.K0EquivLaurentOfField` gives `K₀(C_A) ≅ ℤ[q, q⁻¹]` when `A⁰` is the ground
    field, including a field in bidegree `(0, 0)`. Open: transport of the finite-cell description
    to bigraded modules along `weightEquivalence`.
7.3 Graded Morita theory: for a bigraded dg algebra `A` and a degree-`(0,0)` idempotent `e`
    with `d e = 0` such that `A e A = A`, the functors `Ae ⊗_{eAe} -` and `eA ⊗_A -` induce an
    equivalence `D(eAe) ≃ D(A)` compatible with shifts; `K₀(eAe) ≅ K₀(A)`.
    — Erratum: as printed, 7.3 is false. Counterexample
    (`DG/Examples/MoritaCounterexample.lean`): for a nontrivial commutative ring `R` in degree
    `0`, `K = cone(id_R)`, `V = K ⊕ R`, `A = END_R(V)` and `e` the projection onto `K`, one has
    `A e A = A` but `e A e` is acyclic while `d x = 1` has no solution in `A`, so `D(e A e) = 0`
    and `D(A) ≠ 0` (`DG.MoritaCounterexample.isEmpty_derivedEquivalence`). The relation
    `1 = Σ aᵢ e bᵢ` may need non-closed `aᵢ, bᵢ`. Repaired statement, done:
    `DG.DGIdempotent.moritaEquivalence : D(e A e) ≌ D(A)` (triangulated) under
    `DG.DGIdempotent.IsFullH0` (`1 ∈ Z⁰(A) e Z⁰(A) + B⁰(A)`, i.e. `[e]` generates `H⁰(A)` as a
    two-sided ideal), which follows from `A e A = A` when `A` is non-negatively graded with
    `d(A⁰) = 0` (`DG.DGIdempotent.isFullH0_of_one_mem_span`, e.g. positive `A`); general form
    `DG.DGIdempotent.moritaEquivalenceOfReflects` (`M ↦ e M` reflects acyclicity); dg-category
    form `DG.IdempotentFamily.moritaEquivalence`, `DG.CatModule.DerivedCategory.inductionEquivalence`
    (quasi-fully faithful `F` whose restriction reflects acyclicity),
    `DG.CatModule.DerivedCategory.restrict_isEquivalence_iff`; bigraded form
    `DG.DGIdempotent.gradedMoritaEquivalence : D(C_{eAe}) ≌ D(C_A)` for `e` of weight `0`,
    compatible with `⟨s⟩` (`gradedMoritaEquivalenceInternalShiftIso`); `K₀`:
    `DG.DGIdempotent.K0MoritaEquiv` (`K₀(eAe) ≃+ K₀(A)`) and the `ℤ[q, q⁻¹]`-linear
    `DG.DGIdempotent.gradedK0MoritaEquiv`. Open: images of individual classes, identification of
    the functors with `A e ⊗^L_{eAe} -`, `e A ⊗^L_A -`.
7.4 Half-graded dg modules and the super Grothendieck group. Setting: `ℤ × ℤ/2`-graded dg
    algebras and modules (internal degree, parity) whose differential has bidegree `(k, 1̄)`,
    i.e. is odd and of internal degree `k` (main case `k = 2`); relate to the regradings of 1.4.
    (a) Triangulated structure: the translation is the parity shift `Π` combined with the internal
        shift `⟨∓k⟩` (the cone of a bidegree-`(0, 0̄)` map needs both); fix the sign convention.
    (b) Odd morphisms: odd closed maps up to homotopy, from the `ℤ/2`-graded HOM complexes (on
        `D(A)` via K-projective resolutions); odd closed maps `X → Y` correspond to even closed
        maps `ΠX → Y`, compatibly with homotopy and composition.
    (c) Super `K₀`: the group generated by objects up to isomorphisms of either parity, modulo
        distinguished triangles (definition); comparison theorem: it is the ordinary `K₀` of the
        (even) triangulated category modulo `[ΠX] = [X]`.
    (d) Over a field `k`: the ordinary `K₀(D(k)) ≅ ℤ[q]/(q^{2k} - 1)`, free on `qⁱ[k]`,
        `0 ≤ i < 2k`, with `[Πk] = -qᵏ[k]` (bigraded modules split into `2k` blocks indexed by
        `j + kε mod 2k`, cycled by `⟨1⟩`); the super `K₀(D(k)) ≅ ℤ[q, q⁻¹]/(1 + qᵏ)`, for `k = 2`
        the Gaussian integers `ℤ[√-1]`; for `k = 2`, `⟨1⟩ ∘ ⟨1⟩` is isomorphic to the translation
        up to an odd natural isomorphism. Also over `ℤ` for complexes of free abelian groups.
    — (a), (b), (c) done and (d) in part, via the weight dg category of the regraded ring
    (`DG/HalfGraded/`): `DG.HalfGradedDGRing`, `DG.HalfGradedDGRing.parityShift` and
    `parityShiftD` (`Π = ⟨-k⟩ ⋙ ⟦1⟧`, `shiftOneIso : ⟦1⟧ ≅ ⟨k⟩ ⋙ Π`, sign conventions of the
    cone), `internalShiftOneOneOddIso` (`⟨1⟩ ⋙ ⟨1⟩ ≅ ⟦1⟧ ⋙ Π` for `k = 2`); odd morphisms
    `oddEquiv`, `oddCohomologyEquiv`, `oddDerivedEquiv` (for K-projective sources), `OddIso`;
    the super Grothendieck group `SuperK0`, `SuperK0c` with the comparison `superK0Equiv`,
    `superK0cEquiv` (even `K₀` modulo `[Π X] = [X]`, via `DG.K0Rel.equivQuotient`); over a field,
    `DG.HalfGradedDGRing.Field.K0Equiv : K₀(D(k)^c) ≃+ (Fin (2k) → ℤ)` for all `k > 0`
    (`DG.IsOrthonormalGenerating.K0Equiv`); `DG.HalfGradedDGRing.Field.K0LinearEquiv :
    K₀(D(k)^c) ≃ₗ[ℤ[q, q⁻¹]] ℤ[q, q⁻¹]/(q^{2k} - 1)` (`[k] ↦ 1`, basis `qⁱ[k]`,
    `0 ≤ i < 2k`), `cls_parityShift` (`[Π k] = -qᵏ[k]`), `Field.superK0Equiv` (super
    `K₀(D(k)^c) ≃+ ℤ[q, q⁻¹]/(1 + qᵏ)`) and, for `k = 2`, `superK0EquivGaussianInt`
    (`≃ ℤ[√-1]`). For every integer parameter and every half-graded ring,
    `mk_parityShiftCompact` gives `[ΠX] = -q⁻ᵏ[X]`, and `parityRelations_eq` identifies the parity
    relations with `(1 + qᵏ)K₀`. If `hd x = 1` for some `x`, every dg module over `C_H` is
    acyclic, `D(C_H) = 0` and `K₀(D(C_H)^c)`, `SuperK0c H` vanish (`DG/HalfGraded/Vanishing.lean`,
    `isAcyclic_of_hd_eq_one`, `isZero_of_hd_eq_one`, `compactK0_subsingleton`,
    `superK0c_subsingleton`). `SuperK0c` carries Laurent-polynomial and quotient-ring scalar
    actions (`superK0cModule`, `superK0cQuotientModule`); `T_smul_superK0c_mk` identifies the action
    with the actual internal shift. The field comparison is linear over both coefficient rings
    (`Field.superK0LinearEquiv`, `Field.superK0QuotientLinearEquiv`). `superK0cMap` uniquely descends
    a supplied Laurent-linear compact-K₀ map at a common integer parameter; `superK0cQuotientMap`
    is linear over the quotient coefficient ring. This does not construct a ring-induced derived
    functor. At parameter `2`, every `SuperK0c H` has canonical Gaussian scalars, compatible with
    the Laurent action (`superK0c_evalI_smul`); powers of `i` act by actual internal shifts
    (`gaussian_zpow_smul_superK0c_mk`). `Field.superK0GaussianLinearEquiv` upgrades the existing
    additive field comparison, preserving the regular class and all internal shifts.
    `HalfGradedDGRing.ofDGRing` places an ordinary dg ring's degree `n` at `(2n, n mod 2)` on
    the same underlying ring, with its original differential. Diagonal components and projections
    recover the originals; off-diagonal components vanish (`DG/HalfGraded/Diagonal.lean`).
    For any ordinary dg module, `DG.Diagonal.toCatModuleObj` constructs an actual module over
    the regraded ring's weight category (`DG/HalfGraded/DiagonalModule.lean`), with its action
    and differential induced by the originals. `halfGrading_zero_weight` recovers each original
    homogeneous component, and `toWeightZero_injective` embeds it in the weight-zero object.
    `DG.Diagonal.toCatModule` extends this to an actual functor on ordinary dg modules
    (`DG/HalfGraded/DiagonalFunctor.lean`), preserving the original maps on homogeneous
    generators, action, differential and every weight; the weight-zero injection is natural.
    `DiagonalCohomology.lean` proves the natural all-weight comparison:
    `Hⁿ(F(M)(4t)) ≃+ Hⁿ⁺²ᵗ(M)`, with every unsupported weight zero. Consequently
    `isQuasiIso_toCatModule_iff` proves preservation and reflection of the existing
    quasi-isomorphism predicates, over arbitrary dg rings and in all integer degrees.
    `DiagonalDerived.lean` constructs the induced `DG.Diagonal.toDerived` between the
    existing derived categories, with natural localization comparison `QCompToDerivedIso`
    and the actual quasi-isomorphic-roof formula `toDerived_map_roof`.
    `DiagonalRegular.lean` identifies the full diagonal regular module with the weight-zero
    representable, including all supported periodic copies, and proves its actual derived image
    compact (`isCompact_toDerived_regular`). `DiagonalEvaluation.lean` strengthens evaluation
    at weight `4t` to a natural chain-complex isomorphism with the underlying complex of the
    ordinary shift by `2t`, including the signed differential. This comparison forgets the
    action. `DiagonalRecovery.lean` then embeds the actual ring as weight-zero
    endomorphisms at every weight and defines `recover A w` for arbitrary CatModules by
    dg restriction, retaining their existing action. Actual evaluation is `A`-linear;
    `recoveryNatIso` gives `toCatModule A ⋙ recover A 0 ≅ 𝟭` as genuine dg modules.
    All-supported-weight recovery as signed shifted dg modules and CatModule shift/cone
    comparisons are not yet proved.
    `DiagonalDerivedRecovery.lean` identifies the recovery cohomology map with actual
    weightwise cohomology, descends recovery through localization, and proves
    `toDerived A ⋙ recoveryDerived A 0 ≅ 𝟭`. Consequently `toDerived` is faithful on
    arbitrary derived morphisms, not just localized module maps. A left inverse does not
    imply fullness. `DiagonalFullness.lean` separately proves full faithfulness on the
    actual module categories: the genuine periodic unit arrow determines every supported
    weight component from weight zero, and unsupported weights vanish. Its explicit
    inverse on morphisms is weight-zero recovery conjugated by `recoveryIso`, with both
    inverse laws. This is not a fullness theorem for derived localization.
    `DiagonalAdjunction.lean` constructs the actual module-level adjunction
    `diagonalAdjunction : toCatModule A ⊣ recover A 0` on unrestricted target CatModules.
    Its counit evaluates and then uses the target's existing periodic-unit action;
    factorization of arbitrary supported-weight arrows and vanishing in the unsupported
    branch prove full action compatibility. The unit is `(recoveryNatIso A).inv`, and
    both triangle identities hold. `DiagonalDerivedAdjunction.lean` descends this actual
    adjunction through the existing quasi-isomorphism localizations. Its unit is proved
    equal to `(derivedRecoveryNatIso A).inv`, yielding genuine derived full faithfulness
    (`toDerivedFullyFaithful`, `toDerived_full`) and preimages with both inverse laws for
    arbitrary derived morphisms. The localized unit and counit formulas retain the actual
    recovery comparison and action-compatible counit. Arbitrary dg rings and independent
    derived Hom universes are preserved; no general compactness result is inferred.
    `DiagonalEssentialImage.lean` identifies the actual module essential image exactly by
    vanishing outside weights divisible by four. An explicit inverse periodic-action formula
    proves that the existing counit is bijective on every supported weight. The derived
    essential image is characterized by vanishing of all off-support weight cohomology,
    for every module representative and every derived object isomorphic to it
    (`mem_essImage_toDerived_Q_iff_cohomologicallySupported`,
    `mem_essImage_toDerived_iff_of_iso`). This does not require the unsupported values
    themselves to vanish. `DiagonalShift.lean` constructs genuine natural isomorphisms
    comparing the existing signed shifts with the actual diagonal functor, at module
    and derived levels, for arbitrary integers and all weights. The module comparison
    uses actual restriction-shift compatibility and the existing counit on shifted
    diagonal modules; the derived comparison descends that map through localization.
    Its signed action/differential equations and localized-component formula are explicit.
    `DiagonalImageEquivalence.lean` bundles the module equivalence with the actual
    full subcategory of supported modules, and the derived equivalence with the full
    subcategory of objects admitting an off-support-acyclic representative. Its
    `derivedSupported_iff_of_iso` detects this property on every chosen representative;
    it does not require the representative's values to vanish. The forward functors
    are the existing diagonal functors with codomain restricted, with explicit
    inclusion comparisons. `DiagonalShiftCoherence.lean` proves zero/add coherence
    of the existing module and derived shift comparisons. Its actual `CommShift`
    instances come from the recovery adjunction and quasi-isomorphism localization;
    the comparison isomorphisms are proved equal to the previously constructed ones,
    preserving independent derived Hom universes. `DiagonalRecoveryTriangulated.lean`
    identifies the existing derived recovery at every weight with localization of actual
    homotopy restriction followed by one-object evaluation, and proves it preserves
    distinguished triangles with coherent shifts. `DiagonalDerivedTriangulated.lean`
    identifies the original recovery comparison with its homotopy-localized form and
    proves the existing derived adjunction respects the existing forward and recovery
    shift structures. The actual forward diagonal functor consequently preserves
    distinguished triangles by the triangulated-adjunction theorem. Independent
    derived Hom universes are retained. `DiagonalCompact.lean` proves that actual
    restriction/evaluation recovery preserves coproducts before localization and that
    the existing derived recovery preserves coproducts at every weight, on unrestricted
    target objects. The original derived adjunction consequently proves preservation
    of every `IsCompact.{v}` object by the actual diagonal functor, with coproducts
    indexed in the common module universe and independent derived Hom universes.
    `DiagonalCompactK0.lean` restricts that same triangulated functor to the existing
    compact subcategories and supplies its compact `K₀` homomorphism with the formula
    on object classes. No `K₀` isomorphism or larger-universe coproduct preservation
    is asserted. `DiagonalConeRecovery.lean` supplies an explicit module-level cone
    comparison after weight-zero scalar restriction: componentwise evaluation and
    homogeneous-decomposition lift are inverse on the original cones. It proves
    inclusion/projection compatibility, the actual triangle's negative connecting
    map, and both differential signs. Scalar restriction itself commutes with cones
    at every weight. `DiagonalCone.lean` upgrades the comparison to an actual
    all-weight CatModule isomorphism: support of the original target cone is proved,
    and its genuine action-compatible counit supplies compatibility across distinct
    weights. The comparison has a supported-weight formula using evaluation, the
    explicit cone lift, and periodic-unit action. It respects the original inclusion,
    first projection through the existing coherent signed shift comparison, actual
    negative triangle connecting map, and both differential signs. Arbitrary dg rings
    and independent ring/module universes are retained. `DiagonalConeNaturality.lean`
    proves naturality of that original all-weight comparison under arbitrary commuting
    squares, using the existing `Cone.map` and `CatModule.cone.map`. It also bundles
    the original standard-triangle comparison with identity first/second components,
    the original cone isomorphism as third component, and the existing coherent signed
    shift. `DiagonalDerivedCone.lean` transports the original cone and standard-triangle
    comparisons through the existing localization comparison to `toDerived`, with
    arbitrary-square naturality for actual dg module maps. The first two triangle
    components are the existing localization comparisons and the third is exactly
    localization of the original cone map after its source comparison; the negative
    connecting maps and coherent shifts are retained, with independent derived Hom
    universes. A standalone forward homotopy functor/comparison and bundled
    arrow-to-triangle functor naturality remain open. No cone functor on arbitrary
    derived arrows or equivalence with the whole target is asserted.
    `DiagonalBlocks.lean` proves the block decomposition: every dg module `M` over the
    diagonal weight category is the direct sum of its four blocks
    `(toCatModule (recover 0 (M⟨r⟩)))⟨-r⟩`, `r = 0, …, 3` (an isomorphism of dg modules,
    `isIso_blocksMap`), hence every object `X` of the derived category satisfies
    `X ≅ ⨁_{r=0}^{3} (toDerived (recoveryDerived 0 (X⟨r⟩)))⟨-r⟩` (`blocksDerivedIso`).
    A fully faithful coproduct-preserving functor reflects compact objects
    (`IsCompact.of_map_of_fullyFaithful`), so weight-zero derived recovery preserves compact
    objects. `DiagonalK0.lean` computes, for an arbitrary dg ring `A`,
    `K₀(D(C_H)^c) ≃ₗ[ℤ[q,q⁻¹]] (ℤ[q,q⁻¹] ⧸ (q⁴ - 1)) ⊗[ℤ] K₀(D(A)^c)` (`Diagonal.K0LinearEquiv`)
    and `SuperK0c H ≃ₗ[ℤ[q,q⁻¹]] (ℤ[q,q⁻¹] ⧸ (1 + q²)) ⊗[ℤ] K₀(D(A)^c)`
    (`Diagonal.superK0LinearEquiv`), with `[toDerived X] ↦ 1 ⊗ [X]`; along the way,
    `q²ᵏ` acts trivially on `K₀(D(C_H)^c)` for every half-graded dg ring
    (`HalfGradedDGRing.T_two_mul_smul_compactK0`). `DiagonalK0Map.lean`: for triangulated
    functors `F : D(A) ⥤ D(B)` and `G : D(C_{H_A}) ⥤ D(C_{H_B})` preserving compact objects,
    with `G` commuting with the internal shifts and `G ∘ ι_A ≅ ι_B ∘ F`, the map induced by `G`
    on `K₀` is `ℤ[q,q⁻¹]`-linear and equals `id ⊗ K₀(F)` under `K0LinearEquiv`, and likewise on
    `SuperK0c` (`K0LinearEquiv_mapCompact`, `superK0LinearEquiv_superK0cMap`; for any Laurent-linear
    map compatible with the diagonals, `K0LinearEquiv_linearMap`). `DiagonalInduction.lean`: a
    morphism of dg rings `φ` induces `HalfGradedDGRing.Hom.ofDGRingHom φ`; the diagonal functor is
    derived induction along the weight-zero inclusion (`toDerivedInductionIso`, via
    `recoveryDerivedIso`), so `K₀` of the induced weight functor is `id ⊗ K₀(φ)` under
    `K0LinearEquiv` and `superK0LinearEquiv` (`K0LinearEquiv_K0Map_ofDGRingHom`,
    `superK0LinearEquiv_superK0cMap_ofDGRingHom`; dg modules and Hom groups in the universe of
    the rings). `DiagonalTransport.lean`: every triangulated `F : D(A) ⥤ D(B)` has a diagonal
    transport `Fᵈ X = ∏_{r<4} (ι_B (F (R₀ (X⟨r⟩))))⟨-r⟩` (`Diagonal.transport`), triangulated
    (via `DG.piFunctor_isTriangulated`, products of triangulated functors, `DG/K0/PiFunctor.lean`),
    preserving compact objects when `F` does, with `Fᵈ ∘ ι_A ≅ ι_B ∘ F`
    (`Diagonal.transportToDerivedIso`) and `Fᵈ (X⟨n⟩) ≅ (Fᵈ X)⟨n⟩` (`Diagonal.transportShiftIso`, the
    block of index `4` identified with that of index `0` through `X⟨4⟩ ≅ X⟦2⟧` from `Π Π ≅ 𝟭`); its
    maps on `K₀` and `SuperK0c` are `id ⊗ K₀(F)` (`Diagonal.K0LinearEquiv_transport`,
    `Diagonal.superK0LinearEquiv_transport`). This applies to derived tensor products with dg
    bimodules (`DG.DGBimodule.derivedTensor`). Open: an arbitrary parameter `k`; the identification
    of the transport of `M ⊗^L_B -` with the derived tensor product with the diagonal regrading of
    `M` over the weight dg categories.
    Generic half-graded morphisms: `HalfGradedDGRing.Hom.weightFunctor` and
    `Hom.K0Map` give actual derived-induction maps, Laurent-linear for arbitrary
    common `k`. A quasi-isomorphism (`Hom.IsQuasiIso`: bijective on the cohomology of every
    weight component of the regraded rings) has a quasi-equivalence as weight functor
    (`Hom.isQuasiEquivalence_weightFunctor`) and induces `K₀(C_H) ≃ₗ[ℤ[q, q⁻¹]] K₀(C_{H'})` and
    `SuperK0c H ≃ₗ SuperK0c H'` (`Hom.K0LinearEquiv`, `Hom.superK0cLinearEquiv`,
    `DG/HalfGraded/HomQuasiIso.lean`).
    Positivity (`HalfGraded/Positive.lean`, `DG.HalfGradedDGRing.IsPositive`): `k > 0`,
    `A^{j,•} = 0` for `j < 0` and `0 < j < k`, `d = 0` on `A^{0,•}`, and `A^{0,•}`
    (`internalZeroSubring`) graded semisimple as a `ℤ/2`-graded ring (`DG.IsGradedSemisimpleRing`,
    now for gradings by any abelian group). Under it `K₀(C_H)` is generated by the classes
    `[e · C_H(w, -)]`, `e` an idempotent of `A^{0,0̄}` (`IsPositive.closure_cell_eq_top`, via
    Schnürer for the positive model of formal shifts), and `IsPositive.K0DegreeZeroEquiv`
    (`K₀(C_H) ≃ₗ[ℤ[q, q⁻¹]] K₀(C_{H^{0,•}})`, `H^{0,•} = internalZeroPart`) and
    `IsPositive.superK0cDegreeZeroEquiv` (the same for super `K₀`) identify compact `K₀` with that
    of `A^{0,•}`, via projection/inclusion (`IsPositive.K0EquivOfRetract` for any retraction which
    is the identity on `A^{0,0̄}`). The case `A^{0,1̄} = 0`, `A^{0,0̄}` semisimple:
    `IsPositive.of_isSemisimpleRing`, `IsPositive.K0DegreeZeroEvenEquiv` (`K₀(C_H) ≅ K₀(C_{A⁰})`).
    Examples (`DG/Bigraded/GradedDivisionRing.lean`, `HalfGraded/PositiveSuper.lean`): matrices
    over a graded division ring are graded semisimple, in particular `M(m|n)` over a division ring
    (`isGradedSemisimpleRing_superMatrix`) and `Q(n) = Mₙ(K) ⊗ Cl₁` over a field
    (`isGradedSemisimpleRing_queerMatrix`); a graded semisimple superring placed in internal
    degree `0` is positive (`isPositive_ofSuper`). Odd units: if `c, c' ∈ A^{0,1̄}`, `c c' = 1` and
    `c' a c = a` on `A^{0,0̄}`, then `q⁻ᵏ x = -x` on `K₀(C_H)` and `[Π X] = [X]` already in the
    even `K₀` (`IsPositive.T_neg_smul_eq_neg`, `IsPositive.mk_parityShiftCompact_eq_mk`); e.g.
    `Cl₁ = K[ℤ/2]` (`clifford`, `isPositive_clifford`, `clifford_odd_ne_zero`,
    `clifford_mk_parityShiftCompact`), where `[Π K] = -qᵏ[K] ≠ [K]` for `K` itself. Open: freeness
    of `K₀(C_H)` over `ℤ[q, q⁻¹]/(q^{2k} - 1)` resp. `ℤ[q, q⁻¹]/(1 + qᵏ)` on the graded simple
    `A^{0,•}`-modules of the two types (no basis is constructed here). These are not numerical
    computations or integral scalar-extension theorems; issue #6 E remains open.
    As in 5.5, `K₀` is that of the compact objects (`K₀` of all of `D(k)` vanishes
    by the Eilenberg swindle). Open: the case over `ℤ`; a concrete category of half-graded
    modules equivalent to `CatModule C_H` (half-graded modules are used as dg modules over the
    weight category of the regraded ring).

## Tier 8 — Filling out (candidates for upstreaming)

- Commutative dg algebras, dg Lie algebras and the Chevalley–Eilenberg dg algebra **(stretch)**.
  — done: `DG.IsCDGA` (with `DG.Cohomology.isCDGA`, `DG.GradedTensorProduct.isCDGA`,
  `DG.KoszulComplex.isCDGA`), `DG.DGLieAlgebra`, `DG.DGLieAlgebra.ofDGAlgebra` (graded commutator),
  `DG.DGModule.END.dgLieAlgebra`; for an ordinary Lie algebra with trivial coefficients:
  `DG.ChevalleyEilenberg.ceComplex`, `DG.ChevalleyEilenberg.ceD_ceD`,
  `DG.ChevalleyEilenberg.ceCohomologyZeroEquiv`, `DG.ChevalleyEilenberg.ceCohomologyOneEquiv`
  (`H¹ ≅ (𝔤/[𝔤,𝔤])^*`), `DG.ChevalleyEilenberg.CEAlgebra.isCDGA`. Open: graded `𝔤`, coefficients.
- Hochschild cochain complex of a dg algebra as a dg module; `HH⁰ = Z(A)` for `d = 0`.
  — done for `d = 0`: `DG.hochschildComplex`, `DG.hochschildDiff_hochschildDiff`,
  `DG.hochschildCohomologyZeroEquiv` (`HH⁰(A, M)ᵏ ≅` the degree-`k` graded center),
  `DG.HochschildTotal`. Open: the internal differentials for general dg `A`.
- The bar construction and the standard semi-free resolution `A ⊗ T(sĀ) ⊗ M`; comparison with
  the resolution of 4.3.
  — done over `ℤ` (unnormalized bar construction): `DG.Bar`, `DG.Bar.instDGModule`,
  `DG.Bar.isQuasiIso_augmentation` (via the contracting homotopy `DG.Bar.d_homotopy_add_homotopy_d`),
  `DG.Bar.isKProjective` and `DG.Bar.semiFreeResolution` under the hypothesis that each term
  `A ⊗ (A[1])^{⊗n} ⊗ M` is K-projective, resp. a direct sum of shifts of `A`,
  `DG.Bar.exists_dgHomotopyEquiv_semiFreeResolution`. Note: freeness of `A` and `M` as graded groups
  does not make the filtration by tensor length semi-free when the differentials are nonzero.
  Open: a general commutative ground ring, the normalized version with `Ā`.
- Minimal models over a field (`d = 0` on `A^0`, indecomposables) for positive/connected dg
  algebras; uniqueness up to isomorphism.
- Perfect complexes over a ring and `K₀(D^{perf}(R)) ≅ K₀(R\text{-proj})` (comparison with
  Mathlib's `ModuleCat`).
  — done: `DG.perfectK0Equiv` (any ring, in Mathlib's derived category); compact objects of
  `D(R)` are the perfect complexes and `DG.DGRing.K0.projK0Equiv` for a commutative ring (5.6).
- The derived category of a dg category (4.7) and Morita theory for dg categories.
- Compactly generated triangulated categories and Brown representability [Ne] **(Mathlib)**.
  — done: `DG.CompactlyGenerates.exists_iso_preadditiveYoneda` (Brown representability, for a
  pretriangulated category with coproducts compactly generated by a set),
  `DG.CompactlyGenerates.isRepresentable`, `DG.CompactlyGenerates.isLeftAdjoint`
  (coproduct-preserving triangulated functors have right adjoints),
  `DG.CompactlyGenerates.forall_of_isLocalizing`.
- The external tensor product: for dg rings `A`, `B`, dg modules `M` over `A` and `N` over `B`,
  `M ⊠ N = M ⊗ N` over `A ⊗ B`, and its derived functor `D(A) × D(B) → D(A ⊗ B)`.
  — done over `ℤ` (`A ⊗ B = A ᵍ⊗[ℤ] B`): `DG.ExternalTensor.instDGModule`,
  `DG.ExternalTensor.homotopyFunctor` (`K(A) ⥤ K(B) ⥤ K(A ⊗ B)`), shifts and cones
  (`DG.ExternalTensor.shiftLeftEquiv`, `shiftRightEquiv`, `coneLeftEquiv`, `coneRightEquiv`);
  `DG.DerivedCategory.externalTensor` on K-projective resolutions (no flatness hypothesis),
  `DG.DerivedCategory.externalTensorRegularIso` (`A ⊠ᴸ B ≅ A ⊗ B`); triangulated in each
  variable (`DG.ExternalTensor.commShiftLeft`, `commShiftRight`,
  `DG.DerivedCategory.externalTensor_obj_isTriangulated`,
  `DG.DerivedCategory.externalTensor_flip_obj_isTriangulated`, via the triangulated equivalence
  `DG.DerivedCategory.kProjectiveEquivalence`); compact objects are preserved
  (`DG.DerivedCategory.isCompact_externalTensor`). Over a commutative ring `R`:
  `DG.DerivedCategory.externalTensorOver R A B : D(A) ⥤ D(B) ⥤ D(A ᵍ⊗[R] B)`, the product over `ℤ`
  followed by derived induction along `DG.GradedTensorProduct.intComparison : A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`
  (triangulated in each variable, preserves compact objects, via
  `DG.DGRingHom.derivedInduction_isTriangulated` and `DG.DGRingHom.isCompact_derivedInduction_obj`).
  On `K₀`: `DG.DerivedCategory.K0ExternalTensor` (`[X] ⊗ [Y] ↦ [X ⊠ᴸ Y]`) and
  `DG.DerivedCategory.K0ExternalTensorOver R`, with `[A e] ⊗ [B f] ↦ [(A ⊗ B)(e ⊗ f)]`
  (`DG.ExternalTensor.leftCornerTensorIso`, `DG.DerivedCategory.K0ExternalTensorOver_leftCorner`);
  over a field it is the Künneth isomorphism of 6.5
  (`DG.DerivedCategory.K0ExternalTensorOver_eq_K0KunnethEquiv`).
  The dg module `M ⊗_R N` over `A ᵍ⊗[R] B`: `DG.ExternalTensorOver R A B M N` (Koszul rule
  `DG.ExternalTensorOver.tmul_smul_tmul`, functoriality `DG.ExternalTensorOver.tensorDGHom`; for
  `R = ℤ` it is the product over `ℤ`, `DG.ExternalTensorOver.intEquiv`), and it is induced from the
  product over `ℤ`: `DG.ExternalTensorOver.extendEquiv :
  (A ⊗_R B) ⊗_{A ⊗_ℤ B} (M ⊗_ℤ N) ≅ M ⊗_R N`. For K-projective `P`, `P'`: `P ⊠ P'` and
  `P ⊗_R P'` are K-projective (`DG.ExternalTensor.isKProjective`,
  `DG.ExternalTensorOver.isKProjective`, via `DG.IsKProjective.tensorProductOver` and the `HOM`–`⊗`
  adjunction), and `Q P ⊠ᴸ_R Q P' ≅ Q (P ⊗_R P')`
  (`DG.DerivedCategory.externalTensorOverObjIso`).
- t-structures on `D(A)` for non-positively/positively graded `A` (Mathlib has the definition
  of a t-structure).
  — done for non-positively graded dg rings: `DG.DerivedCategory.tStructure`, with heart
  `ModuleCat H⁰(A)` (`DG.DerivedCategory.tStructureHeart`).
