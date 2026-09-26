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
    Open: the opposite and tensor product dg algebras, the `R`-algebra structure on `H(A)`.
2.2 `DGModule A M`: left dg module; right dg modules and bimodules; `DGModuleHom` (degree-`0`
    chain maps) — done (modules, right modules, bimodules, restriction of scalars):
    `DG.DGModule`, `DG.DGModuleHom`, `DG.DGRightModule`, `DG.DGBimodule`,
    `DG.RestrictScalars`, `DG.DGModuleHom.restrictScalars`;
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
    modules; `M ⊗_R N` with the signed differential. — done (except the `HOM`–`⊗` adjunction,
    and with `M ⊗_R N` over `R = ℤ`): `DG.instDGAddCommGroupTensorProduct`,
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
    `HomologicalComplex.homologySequence`). — done (except arbitrary direct sums and the long
    exact sequence): `DG.cohomology`, `DG.cohomology.mk`, `DG.cohomology.mkOf`,
    `DG.cohomology.lift`, `DG.cohomology.map` (`map_id`, `map_comp`, `map_zero`, `map_add`),
    `DG.DGModuleHom.IsQuasiIso` (`isQuasiIso_id`, `IsQuasiIso.comp`,
    `IsQuasiIso.of_comp_left`, `IsQuasiIso.of_comp_right`), `DG.Cohomology`
    (`DG.Cohomology.instDGAddCommGroup`), `DG.cohomology.smulHom`, `DG.Cohomology.gring`,
    `DG.Cohomology.ring`, `DG.Cohomology.dgRing`, `DG.Cohomology.gmodule`,
    `DG.Cohomology.module`, `DG.Cohomology.dgModule`, `DG.cohomology.prodAddEquiv`
    (with `DG.Prod.instDGAddCommGroup`, `DG.Prod.instDGModule`).
2.6 Comparison with Mathlib's monoidal category: a `DGAlgebra R A` is the same as a monoid
    object `Mon_ (CochainComplex (ModuleCat R) ℤ)` and a dg module is a `Mod_` object;
    equivalences of categories in both directions. Requires the monoidal structure of
    `Mathlib/Algebra/Homology/Monoidal.lean` with `ComplexShape.TensorSigns` for `ℤ`.
    **(Mathlib)**
2.7 Examples: the Koszul complex `K(x₁, …, xₙ)` on a commutative ring as a commutative dg
    algebra; `END_R(C)` for a cochain complex `C`; the free dg algebra on a graded set with
    prescribed differential (semi-free dg algebras); the truncations. **(stretch:** de Rham
    complex of a polynomial algebra.)

## Tier 3 — The homotopy category

3.1 Homotopy between dg module maps (`f - g = d h + h d` with `h` of degree `-1`), the
    null-homotopic maps form an ideal; the homotopy category `H(A) := DGModuleCat A / ~`
    (`CategoryTheory.Quotient`), additive and `R`-linear; `Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`.
    — done (before the quotient category): `DG.DGHomotopy`, `DG.Homotopic`,
    `DG.homotopic_equivalence`, `DG.nullHomotopic`, `DG.comp_mem_nullHomotopic`,
    `DG.quotientNullHomotopicAddEquivCohomology`, `DG.DGHomotopy.cohomology_map_eq`,
    `DG.DGHomotopyEquiv.isQuasiIso_hom`, `DG.IsContractible.subsingleton_cohomology`.
3.2 Shift `[1]` on `DGModuleCat A` and on `H(A)` (`CategoryTheory.HasShift`, via
    `Mathlib`'s `hasShiftMk`), with `HOM_A(M, N[n]) ≅ HOM_A(M, N)[n]`.
    — done (on dg modules, not yet categorical): `DG.Shift`, `DG.Shift.instDGModule`,
    `DG.DGModuleHom.shift`, `DG.Shift.zeroEquiv`, `DG.Shift.addEquiv`.
3.3 Mapping cone `C(f) = N ⊕ M[1]`, the standard triangle `M → N → C(f) → M[1]`, and the
    pretriangulated structure on `H(A)` **(Mathlib)**: distinguished triangles are those
    isomorphic to standard ones; verify the axioms TR1–TR4 following Mathlib's
    `HomotopyCategory.Pretriangulated`/`Triangulated` files for cochain complexes (the proofs
    are the same with `A`-linearity carried along). `H(A)` is triangulated (octahedral axiom).
    — done (on dg modules, not yet categorical): `DG.Cone`, `DG.Cone.instDGModule`,
    `DG.Cone.inr`, `DG.Cone.fst`, `DG.Cone.inl`, `DG.Cone.snd`, `DG.Cone.map`,
    `DG.Cone.contraction`, `DG.Cone.d_contraction_add_contraction_d`.
3.4 The forgetful functor `H(A) ⥤ HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)`
    commutes with shifts and cones, hence is a triangulated functor; `H` is a homological
    functor on `H(A)`.
3.5 Special modules: K-projective (cofibrant) modules (`Hom_{H(A)}(P, N) = 0` for all acyclic
    `N`; equivalently the lifting property against surjective quasi-isomorphisms; prove the
    equivalence), semi-free modules (union of an exhaustive filtration with subquotients
    direct sums of shifts of `A`), finite-cell modules (finite filtration with subquotients
    direct summands `Ae[n]` of shifts of `A` for degree-`0` idempotents `e` with `d e = 0`).
    Semi-free ⟹ K-projective; direct summands and shifts of K-projectives are K-projective;
    `A` and finite-cell modules are K-projective. [Ke §3], [BL 10.12], [St].
3.6 For `P` K-projective, `HOM_A(P, -)` preserves quasi-isomorphisms and
    `Hom_{H(A)}(P, N) ≅ Hom_{H(A)}(P, N')` along a quasi-isomorphism `N → N'`.

## Tier 4 — The derived category

4.1 Quasi-isomorphisms in `H(A)` are the morphisms whose cone is acyclic; the acyclic
    modules form a thick triangulated subcategory; the class of quasi-isomorphisms is
    compatible with the triangulation (a multiplicative system in Verdier's sense). Use
    Mathlib's `Triangulated.Subcategory` and `Localization.Triangulated`.
4.2 `D(A) := H(A)[qis⁻¹]` via `CategoryTheory.Localization`, with a `HasDerivedCategory`-style
    class for a chosen small model; `D(A)` is triangulated and `H(A) ⥤ D(A)` is a
    triangulated localization functor; it has arbitrary coproducts, preserved by the
    localization functor.
4.3 Existence of K-projective (semi-free) resolutions: every dg module `M` admits a
    surjective quasi-isomorphism `P → M` with `P` semi-free (the standard iterated-cone or
    telescope construction, [Ke §3.1], [BL 10.12.2.4], [St, "Resolutions"]). Uniqueness up
    to homotopy equivalence over `M`. Consequently the K-projective modules form a full
    subcategory of `H(A)` equivalent to `D(A)`, and `Hom_{D(A)}(M, N) ≅ H⁰(HOM_A(P_M, N))`.
    Dually **(stretch)**: K-injective resolutions.
4.4 Derived functors: `M ⊗^L_B -` and `RHOM_A(M, -)` for a dg `(A, B)`-bimodule `M`, defined
    on `D(B)` resp. `D(A)` via K-projective resolutions, well defined up to canonical
    isomorphism, triangulated; the derived tensor–Hom adjunction; compatibility with shifts
    and coproducts. Induction `φ^* = A ⊗^L_B -` and restriction `φ_* = RHOM_A(A, -)` (which is
    the underived restriction of scalars) along a `DGAlgHom φ : B → A`, and `φ^* ⊣ φ_*`.
4.5 Keller's theorem [Ke, Ex. 6.1], [BL 10.12.5.1]: if `φ : B → A` is a quasi-isomorphism of dg
    algebras, `φ^*` and `φ_*` are mutually inverse triangulated equivalences `D(B) ≃ D(A)`.
    Corollary: for a dg algebra `A`, the following are equivalent: `D(A) ≃ 0`; `H(A) = 0`;
    there is `x ∈ A` with `d x = 1`. (`H(A) = 0 ⟹ D(A) ≃ 0` by Keller applied to `0 → A`;
    `d x = 1 ⟹ H(A) = 0` by `d(x y) = y - x d y`.)
4.6 Comparison with Mathlib **(Mathlib)**: for `A = R` concentrated in degree `0`, `D(A)` is
    equivalent to Mathlib's `DerivedCategory (ModuleCat R)` as triangulated categories.
    More generally `D(A)` for a graded ring with zero differential vs. the derived category of
    graded modules **(stretch)**.
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
5.6 Computations: `K₀` of a field `k` in degree `0` is `ℤ`, generated by `[k]` (every object
    of `D^c(k)` is a finite direct sum of shifts of `k`; compact ⟺ finite total dimension);
    `K₀(R) ≅ K₀(R\text{-proj})` for a ring `R` in degree `0` (perfect complexes; reduce to
    Mathlib where possible) **(stretch)**; Künneth-type statement
    `K₀(A ⊗_k B) ≅ K₀(A) ⊗ K₀(B)` under hypotheses to be determined from tier 6 (positive dg
    algebras over a field).

## Tier 6 — Positive dg algebras (Schnürer)

6.1 Definition: `A` is positive if `Aⁿ = 0` for `n < 0`, `A⁰` is a semisimple ring, and
    `d = 0` on `A⁰` (equivalently `d : A⁰ → A¹` vanishes). Basic consequences: the
    degree-`0` idempotents of `A⁰` are cocycles, `A e` is a finite-cell module for each such
    `e`, the truncations `A^{≥ n}` are dg ideals.
    — done (except "`A e` is a finite-cell module", which needs 3.5): `DG.IsPositive`
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
6.3 Corollary: `K₀(A) ≅ K₀(A⁰)` for `A` positive over a field, the isomorphism sending
    `[A e]` to `[A⁰ e]`, and `K₀(A)` is free on the classes of the `A e` for a complete set of
    primitive orthogonal idempotents of `A⁰` up to isomorphism. In particular
    `K₀(A) ≅ ℤ` when `A⁰ = k`.
6.4 Formality: a dg algebra `A` is formal if it is connected to `H(A)` (zero differential) by
    a zigzag of quasi-isomorphisms; Keller's theorem then gives `D(A) ≃ D(H(A))` and
    `K₀(A) ≅ K₀(H(A))`. Criterion: if `H(A)` is a free (super)commutative graded algebra on
    homogeneous cocycle representatives, or more generally if a graded algebra map
    `H(A) → A` splitting the cocycles exists, then `A` is formal (via the direct quasi-
    isomorphism `H(A) → A`). Transfer of positivity along quasi-isomorphisms where it holds.
6.5 Künneth for positive dg algebras over a field: `K₀(A ⊗_k B) ≅ K₀(A) ⊗_ℤ K₀(B)` when `A`,
    `B` (hence `A ⊗ B`) are positive, from 6.3 and `K₀` of tensor products of semisimple
    algebras.

## Tier 7 — Internal gradings

7.1 Bigraded dg algebras: an additional `ℤ`-grading ("internal" or "weight" grading) on `A`
    preserved by `d`, `∂`-compatible with the product; bigraded dg modules; the internal shift
    `M⟨1⟩` as an autoequivalence of `DGModuleCat A`, `H(A)` and `D(A)`, commuting with `[1]`,
    triangulated. Compact objects and `K₀` in the bigraded setting; `K₀(A)` is a
    `ℤ[q, q⁻¹]`-module via `q [M] = [M⟨1⟩]`.
7.2 Positive bigraded dg algebras: Schnürer's theorem with internal gradings (the same proof;
    or deduce from 6.2 by forgetting the internal grading and a graded-idempotent argument),
    `K₀(A) ≅ K₀(A⁰)` as `ℤ[q, q⁻¹]`-modules where `A⁰` is the homological degree-`0` part
    graded by weight; `K₀(k) ≅ ℤ[q, q⁻¹]` for a field `k` in bidegree `(0,0)`.
7.3 Graded Morita theory: for a bigraded dg algebra `A` and a degree-`(0,0)` idempotent `e`
    with `d e = 0` such that `A e A = A`, the functors `Ae ⊗_{eAe} -` and `eA ⊗_A -` induce an
    equivalence `D(eAe) ≃ D(A)` compatible with shifts; `K₀(eAe) ≅ K₀(A)`.
7.4 Regraded variants: dg algebras whose differential has internal degree `k` and homological
    degree `1` (e.g. `k = 2`), obtained from 7.1 by the regrading of 1.4; identification of the
    homological shift with an internal shift on `K₀` when the two gradings are linked (for a
    differential of bidegree `(k, 1)` with the homological grading determined by the internal
    one, `K₀` becomes a module over `ℤ[q, q⁻¹]/(1 + q^k)`-type quotients; state and prove the
    precise version).

## Tier 8 — Filling out (candidates for upstreaming)

- Commutative dg algebras, dg Lie algebras and the Chevalley–Eilenberg dg algebra **(stretch)**.
- Hochschild cochain complex of a dg algebra as a dg module; `HH⁰ = Z(A)` for `d = 0`.
- The bar construction and the standard semi-free resolution `A ⊗ T(sĀ) ⊗ M`; comparison with
  the resolution of 4.3.
- Minimal models over a field (`d = 0` on `A^0`, indecomposables) for positive/connected dg
  algebras; uniqueness up to isomorphism.
- Perfect complexes over a ring and `K₀(D^{perf}(R)) ≅ K₀(R\text{-proj})` (comparison with
  Mathlib's `ModuleCat`).
- The derived category of a dg category (4.7) and Morita theory for dg categories.
- Compactly generated triangulated categories and Brown representability [Ne] **(Mathlib)**.
- t-structures on `D(A)` for non-positively/positively graded `A` (Mathlib has the definition
  of a t-structure).
