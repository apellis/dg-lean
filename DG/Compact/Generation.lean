import DG.Compact.HomotopyColimit
import DG.Compact.Thick
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Compact objects of a compactly generated triangulated category

Let `C` be a triangulated category with coproducts, and `G : ι → C` a family of objects indexed
by a small type. `G` *compactly generates* `C` (`DG.CompactlyGenerates G`) if every `G i` is
compact and an object `Y` with `Hom(G i⟦n⟧, Y) = 0` for all `i` and all `n : ℤ` is zero. The
main theorem is

* `DG.thickClosure_eq_isCompact`: if `G` compactly generates `C`, the compact objects of `C`
  are exactly the objects of the thick closure of `G` (Neeman; [Stacks, Prop. 13.37.6,
  Tag 09SR] for a single generator). The inclusion of the thick closure in the compact objects
  is `DG.thickClosure_le_isCompact`; the converse is `DG.thickClosure_of_isCompact`.

## Proof

For an object `X`, the *cellular tower* `P 0 ⟶ P 1 ⟶ ⋯` of objects over `X`
(`DG.CellTower.tower`, [Stacks, Lemma 13.37.3, Tag 09SN]) has `P 0 = ∐ G i⟦n⟧`, the coproduct
over all morphisms `G i⟦n⟧ ⟶ X`, and `P (k + 1)` is the cone of the morphism to `P k` from the
coproduct of the shifted generators over all morphisms `G i⟦n⟧ ⟶ P k` which vanish in `X`.
The induced morphism `h : hocolim P ⟶ X` from the homotopy colimit (`DG.Compact.HomotopyColimit`)
is bijective on `Hom(G i⟦n⟧, -)` (surjective by construction of `P 0`, injective by construction
of `P (k + 1)`, using that the `G i⟦n⟧` are compact), hence its cone is zero by generation and
`h` is an isomorphism. If `X` is compact, `h⁻¹` factors through some `P k`, so `X` is a
retract of `P k`, and the section `X ⟶ P k` still has compact source.

The `P k` are built from infinite coproducts; the remaining step
(`DG.CellTower.compactlyFactorsThrough_tower`) shows that every morphism from a compact object
to `P k` factors through an object of the thick closure of `G`. For `P 0` this is the
factorization of a morphism from a compact object to a coproduct through a finite subcoproduct
(`DG.CompactlyFactorsThrough.coproduct`). For the inductive step
(`DG.CompactlyFactorsThrough.ext₃`) let `Q ⟶ P ⟶ P' ⟶ Q⟦1⟧` be distinguished and
`φ : K ⟶ P'` with `K` compact. The composition `K ⟶ Q⟦1⟧` factors through an object `M` of the
thick closure; the fibre `K'` of `c : K ⟶ M` is compact and `K' ⟶ K ⟶ P'` lifts to
`g : K' ⟶ P`, which by induction factors through an object `L` of the thick closure. The
homotopy pushout `N` of `K ← K' ⟶ L` then receives `K` and maps to `P'` compatibly with `φ`, and
the octahedral axiom provides a distinguished triangle `N ⟶ M ⟶ L⟦1⟧ ⟶ N⟦1⟧`, so `N` lies in the
thick closure. This step uses the octahedral axiom, so `C` is assumed triangulated
(`IsTriangulated C`), not only pretriangulated.

## Universes

With `C : Type u`, `[Category.{v} C]` and `ι : Type w`, the cells of the tower are indexed by
types in `Type (max w v)`, so compactness and the existence of coproducts are taken relative to
`Type (max w v)` (`IsCompact.{max w v}`, `HasCoproducts.{max w v} C`); for a generating family
indexed by a type in `Type`, or in `Type v`, this is the universe `v` of the morphisms.
`DG.IsCompact.down` lowers the universe of compactness; it is used to apply the results of
`DG.Compact.HomotopyColimit` (which need compactness for `ℕ`-indexed coproducts only).

## References

* [Ne96] A. Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*, J. Amer. Math. Soc. 9 (1996), 205–236, §2.
* [Stacks] The Stacks project, Section 13.37 (Compact objects).
-/

universe w w' v u

namespace DG

open CategoryTheory Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Compactness relative to a universe implies compactness relative to any smaller universe. -/
theorem IsCompact.down {X : C} (h : IsCompact.{max w w'} X) : IsCompact.{w} X := by
  rw [isCompact_iff_preservesColimitsOfShape] at h ⊢
  intro ι
  have := h (ULift.{w'} ι)
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- `CompactlyFactorsThrough.{w} P Y`: every morphism from a compact object (relative to the
universe `w`) to `Y` factors through an object satisfying `P`. -/
def CompactlyFactorsThrough (P : ObjectProperty C) (Y : C) : Prop :=
  ∀ ⦃K : C⦄, IsCompact.{w} K → ∀ φ : K ⟶ Y, ∃ L, P L ∧ ∃ (a : K ⟶ L) (b : L ⟶ Y), φ = a ≫ b

namespace CompactlyFactorsThrough

variable {P : ObjectProperty C}

theorem of_mem {Y : C} (hY : P Y) : CompactlyFactorsThrough.{w} P Y :=
  fun _ _ φ => ⟨Y, hY, φ, 𝟙 Y, (Category.comp_id φ).symm⟩

theorem of_retract {Y Y' : C} (e : Retract Y Y') (h : CompactlyFactorsThrough.{w} P Y') :
    CompactlyFactorsThrough.{w} P Y := by
  intro K hK φ
  obtain ⟨L, hL, a, b, hab⟩ := h hK (φ ≫ e.i)
  exact ⟨L, hL, a, b ≫ e.r, by rw [← Category.assoc, ← hab, Category.assoc, e.retract,
    Category.comp_id]⟩

end CompactlyFactorsThrough

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace CompactlyFactorsThrough

variable {P : ObjectProperty C}

/-- A morphism from a compact object to a coproduct of objects of a thick property `P` factors
through an object of `P`: it factors through a finite subcoproduct. -/
theorem coproduct (hP : IsThick P) {ι : Type w} (Y : ι → C) [HasCoproduct Y]
    (hY : ∀ i, P (Y i)) : CompactlyFactorsThrough.{w} P (∐ Y) := by
  classical
  intro K hK φ
  obtain ⟨a, rfl⟩ := (hK ι Y).2 φ
  induction a using DirectSum.induction_on with
  | zero => exact ⟨0, hP.zero, 0, 0, by simp⟩
  | of i x => exact ⟨Y i, hY i, x, Sigma.ι Y i, by simp⟩
  | add x y hx hy =>
    obtain ⟨L₁, h₁, a₁, b₁, e₁⟩ := hx
    obtain ⟨L₂, h₂, a₂, b₂, e₂⟩ := hy
    exact ⟨L₁ ⊞ L₂, hP.biprod h₁ h₂, biprod.lift a₁ a₂, biprod.desc b₁ b₂, by simp [e₁, e₂]⟩

/-- The shift `(∐ Y)⟦1⟧` of a coproduct of objects of a thick property `P`: morphisms from
compact objects factor through `P`. -/
theorem coproduct_shift [HasCoproducts.{w} C] (hP : IsThick P) {ι : Type w} (Y : ι → C)
    (hY : ∀ i, P (Y i)) (n : ℤ) : CompactlyFactorsThrough.{w} P ((∐ Y)⟦n⟧) := by
  let e := sigmaComparison (shiftFunctor C n) Y
  exact of_retract ⟨inv e, e, by simp⟩ (coproduct hP _ fun i => hP.shift _ n (hY i))

/-- The inductive step of the cellular construction. Let `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a
distinguished triangle in a triangulated category, and `P` a thick property consisting of
compact objects. If morphisms from compact objects to `X₁⟦1⟧` and to `X₂` factor through `P`,
so do morphisms from compact objects to `X₃`. -/
theorem ext₃ [IsTriangulated C] [HasCoproducts.{w} C] (hP : IsThick P)
    (hPc : P ≤ IsCompact.{w}) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : CompactlyFactorsThrough.{w} P (T.obj₁⟦(1 : ℤ)⟧))
    (h₂ : CompactlyFactorsThrough.{w} P T.obj₂) : CompactlyFactorsThrough.{w} P T.obj₃ := by
  intro K hK φ
  -- `φ ≫ T.mor₃` factors through an object `M` of `P`.
  obtain ⟨M, hM, c, j, hcj⟩ := h₁ hK (φ ≫ T.mor₃)
  -- The fibre `K'` of `c : K ⟶ M` is compact, and `K' ⟶ K ⟶ X₃` lifts to `X₂`.
  obtain ⟨K', k, d, hkcd⟩ := distinguished_cocone_triangle₁ c
  have hK' : IsCompact.{w} K' := IsCompact.ext₁ _ hkcd hK (hPc _ hM)
  have hkc : k ≫ c = 0 := comp_distTriang_mor_zero₁₂ _ hkcd
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT (k ≫ φ) (by
    rw [Category.assoc, hcj, ← Category.assoc, hkc, Limits.zero_comp])
  -- By hypothesis `g : K' ⟶ X₂` factors through an object `L` of `P`.
  obtain ⟨L, hL, u, v, huv⟩ := h₂ hK' g
  -- The homotopy pushout `N` of `K ← K' → L` is an extension of `M` by `L`, hence in `P`.
  let u₁₂ : K' ⟶ L ⊞ K := biprod.lift (-u) k
  obtain ⟨N, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle u₁₂
  have h₂₃ : Triangle.mk (biprod.snd : L ⊞ K ⟶ K) (0 : K ⟶ L⟦(1 : ℤ)⟧)
      (-(biprod.inl : L ⟶ L ⊞ K)⟦(1 : ℤ)⟧') ∈ distTriang C :=
    rot_of_distTriang _ (binaryBiproductTriangle_distinguished L K)
  have comm : u₁₂ ≫ biprod.snd = k := biprod.lift_snd _ _
  have oct := Triangulated.someOctahedron comm h₁₂ h₂₃ hkcd
  have hN : P N := hP.ext₁ _ oct.mem hM (hP.shift _ 1 hL)
  -- The morphism `(v ≫ T.mor₂, φ) : L ⊞ K ⟶ X₃` vanishes on `K'`, hence factors through `N`.
  obtain ⟨n, hn⟩ := Triangle.yoneda_exact₂ _ h₁₂ (biprod.desc (v ≫ T.mor₂) φ) (by
    change u₁₂ ≫ _ = 0
    rw [biprod.lift_desc, hg, huv, Preadditive.neg_comp, Category.assoc, neg_add_cancel])
  refine ⟨N, hN, biprod.inr ≫ v₁₂, n, ?_⟩
  rw [Category.assoc]
  change φ = biprod.inr ≫ (Triangle.mk u₁₂ v₁₂ w₁₂).mor₂ ≫ n
  rw [← hn, biprod.inr_desc]

end CompactlyFactorsThrough

section Generation

variable {ι : Type w} (G : ι → C)

/-- A family `G` of objects *compactly generates* `C` if every `G i` is compact (relative to
coproducts indexed by types in `Type (max w v)`) and an object `Y` with `Hom(G i⟦n⟧, Y) = 0` for
all `i` and all `n : ℤ` is zero ([Stacks, Def. 13.37.5, Tag 09SQ]; [Ne96, §1]). -/
structure CompactlyGenerates : Prop where
  /-- The generators are compact. -/
  isCompact (i : ι) : IsCompact.{max w v} (G i)
  /-- The generators detect zero objects. -/
  isZero_of_forall_eq_zero (Y : C) : (∀ (i : ι) (n : ℤ) (φ : (G i)⟦n⟧ ⟶ Y), φ = 0) → IsZero Y

namespace CellTower

variable {X : C}

/-- The cells of the first stage of the cellular tower of `X`: all morphisms `G i⟦n⟧ ⟶ X`. -/
def Cells (X : C) : Type (max w v) :=
  Σ (i : ι) (n : ℤ), ((G i)⟦n⟧ ⟶ X)

/-- The cells attached to a stage `A ⟶ X` of the cellular tower: the morphisms
`G i⟦n⟧ ⟶ A.left` whose composition with `A.hom` vanishes. -/
def KerCells (A : Over X) : Type (max w v) :=
  Σ (i : ι) (n : ℤ), {φ : (G i)⟦n⟧ ⟶ A.left // φ ≫ A.hom = 0}

variable [HasCoproducts.{max w v} C]

/-- The first stage of the cellular tower: `∐ G i⟦n⟧ ⟶ X`, over all morphisms `G i⟦n⟧ ⟶ X`. -/
noncomputable def base (X : C) : Over X :=
  Over.mk (Sigma.desc (f := fun c : Cells G X => (G c.1)⟦c.2.1⟧) fun c => c.2.2)

/-- The morphism `∐ G i⟦n⟧ ⟶ A.left` from the coproduct of the cells in the kernel. -/
noncomputable def kerMap (A : Over X) : (∐ fun c : KerCells G A => (G c.1)⟦c.2.1⟧) ⟶ A.left :=
  Sigma.desc fun c => c.2.2.1

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
theorem kerMap_comp_hom (A : Over X) : kerMap G A ≫ A.hom = 0 := by
  ext c
  simp [kerMap, c.2.2.2]

/-- A chosen distinguished triangle `∐ G i⟦n⟧ ⟶ A.left ⟶ Z ⟶ (∐ G i⟦n⟧)⟦1⟧` on `kerMap G A`. -/
noncomputable def nextTriangle (A : Over X) : Triangle C :=
  Triangle.mk (kerMap G A) (distinguished_cocone_triangle (kerMap G A)).choose_spec.choose
    (distinguished_cocone_triangle (kerMap G A)).choose_spec.choose_spec.choose

theorem nextTriangle_distinguished (A : Over X) : nextTriangle G A ∈ distTriang C :=
  (distinguished_cocone_triangle (kerMap G A)).choose_spec.choose_spec.choose_spec

/-- The next stage of the cellular tower: the cone of `kerMap G A`, with its morphism to `X`. -/
noncomputable def next (A : Over X) : Over X :=
  Over.mk (Triangle.yoneda_exact₂ _ (nextTriangle_distinguished G A) A.hom
    (kerMap_comp_hom G A)).choose

/-- The morphism from a stage of the cellular tower to the next one. -/
noncomputable def toNext (A : Over X) : A ⟶ next G A :=
  Over.homMk (nextTriangle G A).mor₂ (Triangle.yoneda_exact₂ _ (nextTriangle_distinguished G A)
    A.hom (kerMap_comp_hom G A)).choose_spec.symm

variable (X) in
/-- The cellular tower `P 0 ⟶ P 1 ⟶ ⋯` of objects over `X`. -/
noncomputable def tower : ℕ → Over X
  | 0 => base G X
  | n + 1 => next G (tower n)

variable (X) in
/-- The transition morphisms of the cellular tower. -/
noncomputable def towerMap (n : ℕ) : (tower G X n).left ⟶ (tower G X (n + 1)).left :=
  (toNext G (tower G X n)).left

@[reassoc (attr := simp)]
theorem towerMap_comp_hom (n : ℕ) :
    towerMap G X n ≫ (tower G X (n + 1)).hom = (tower G X n).hom :=
  Over.w (toNext G (tower G X n))

/-- Every morphism `G i⟦m⟧ ⟶ X` lifts to the first stage. -/
theorem exists_lift_base {i : ι} {m : ℤ} (φ : (G i)⟦m⟧ ⟶ X) :
    ∃ ψ : (G i)⟦m⟧ ⟶ (tower G X 0).left, ψ ≫ (tower G X 0).hom = φ :=
  ⟨Sigma.ι (fun c : Cells G X => (G c.1)⟦c.2.1⟧) ⟨i, m, φ⟩, by simp [tower, base]⟩

/-- A morphism `G i⟦m⟧ ⟶ P n` which vanishes in `X` vanishes in `P (n + 1)`. -/
theorem comp_towerMap_eq_zero {n : ℕ} {i : ι} {m : ℤ} (ψ : (G i)⟦m⟧ ⟶ (tower G X n).left)
    (hψ : ψ ≫ (tower G X n).hom = 0) : ψ ≫ towerMap G X n = 0 := by
  have h : ψ = Sigma.ι (fun c : KerCells G (tower G X n) => (G c.1)⟦c.2.1⟧) ⟨i, m, ψ, hψ⟩ ≫
      kerMap G (tower G X n) := by
    simp [kerMap]
  rw [h, Category.assoc]
  change _ ≫ (nextTriangle G _).mor₁ ≫ (nextTriangle G _).mor₂ = 0
  rw [comp_distTriang_mor_zero₁₂ _ (nextTriangle_distinguished G _), Limits.comp_zero]

/-- Morphisms from compact objects to each stage of the cellular tower factor through the
thick closure of `G` (in fact, through objects built from finitely many cells). -/
theorem compactlyFactorsThrough_tower [IsTriangulated C] (hG : ∀ i, IsCompact.{max w v} (G i))
    (n : ℕ) :
    CompactlyFactorsThrough.{max w v} (ThickClosure fun Y => ∃ i, G i = Y) (tower G X n).left := by
  have hP := isThick_thickClosure (fun Y => ∃ i, G i = Y)
  have hPc : ThickClosure (fun Y => ∃ i, G i = Y) ≤ IsCompact.{max w v} :=
    thickClosure_le_isCompact (by rintro _ ⟨i, rfl⟩; exact hG i)
  have hGP : ∀ (i : ι) (m : ℤ), ThickClosure (fun Y => ∃ i, G i = Y) ((G i)⟦m⟧) :=
    fun i m => hP.shift _ m (le_thickClosure _ _ ⟨i, rfl⟩)
  induction n with
  | zero => exact CompactlyFactorsThrough.coproduct hP _ fun c => hGP _ _
  | succ n ih =>
    exact CompactlyFactorsThrough.ext₃ hP hPc _ (nextTriangle_distinguished G _)
      (CompactlyFactorsThrough.coproduct_shift hP _ (fun c => hGP _ _) 1) ih

end CellTower

open CellTower in
/-- **Neeman's theorem** ([Ne96, §2]; [Stacks, Prop. 13.37.6, Tag 09SR]). Let `C` be a
triangulated category with coproducts, compactly generated by a family `G` of objects indexed
by a small type. Then every compact object of `C` lies in the thick closure of `G`. -/
theorem thickClosure_of_isCompact [IsTriangulated C] [HasCoproducts.{max w v} C]
    (hG : CompactlyGenerates G) {X : C} (hX : IsCompact.{max w v} X) :
    ThickClosure (fun Y => ∃ i, G i = Y) X := by
  haveI : HasCoproducts.{0} C := hasCoproducts_shrink.{0, max w v}
  let P : ℕ → C := fun n => (tower G X n).left
  let H := hocolim P (towerMap G X)
  -- The compatible morphisms `P n ⟶ X` induce `h : hocolim P ⟶ X`.
  obtain ⟨h, hh⟩ := hocolim_exists_desc P (towerMap G X) (fun n => (tower G X n).hom)
    (towerMap_comp_hom G)
  have hcpt : ∀ (i : ι) (m : ℤ), IsCompact.{0} ((G i)⟦m⟧) :=
    fun i m => ((hG.isCompact i).shift m).down
  -- `h` is injective on morphisms from shifted generators.
  have inj : ∀ (i : ι) (m : ℤ) (a : (G i)⟦m⟧ ⟶ H), a ≫ h = 0 → a = 0 := by
    intro i m a ha
    obtain ⟨k, b, rfl⟩ := hocolim_exists_factor P (towerMap G X) (hcpt i m) a
    have hb : b ≫ (tower G X k).hom = 0 := by rw [← hh k, ← Category.assoc, ha]
    rw [← f_comp_hocolimι, ← Category.assoc, comp_towerMap_eq_zero G b hb, Limits.zero_comp]
  -- `h` is an isomorphism: its cone has no nonzero morphisms from shifted generators.
  obtain ⟨Z, g₂, g₃, hT⟩ := distinguished_cocone_triangle h
  have hZ : IsZero Z := by
    refine hG.isZero_of_forall_eq_zero Z fun i m φ => ?_
    let adj : shiftFunctor C (-1 : ℤ) ⊣ shiftFunctor C (1 : ℤ) :=
      (shiftEquiv C (1 : ℤ)).symm.toAdjunction
    have h₁ : φ ≫ g₃ = 0 := by
      have h₃₁ : g₃ ≫ h⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      set ψ := (adj.homEquiv _ _).symm (φ ≫ g₃)
      have hψ : ψ ≫ h = 0 := by
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc, h₃₁,
          Limits.comp_zero, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
      let e := (shiftFunctorAdd' C m (-1) (m + -1) rfl).app (G i)
      have : e.hom ≫ ψ = 0 := inj i (m + -1) _ (by rw [Category.assoc, hψ, Limits.comp_zero])
      rw [← Equiv.apply_symm_apply (adj.homEquiv _ _) (φ ≫ g₃)]
      change adj.homEquiv _ _ ψ = 0
      rw [(cancel_epi e.hom).1 (this.trans (Limits.comp_zero).symm), Adjunction.homEquiv_unit,
        Functor.map_zero, Limits.comp_zero]
    obtain ⟨x, rfl⟩ := Triangle.coyoneda_exact₃ _ hT φ h₁
    obtain ⟨y, rfl⟩ := exists_lift_base G x
    have h₁₂ : h ≫ g₂ = 0 := comp_distTriang_mor_zero₁₂ _ hT
    change (y ≫ (tower G X 0).hom) ≫ g₂ = 0
    rw [← hh 0, Category.assoc, Category.assoc, h₁₂, Limits.comp_zero, Limits.comp_zero]
  have : IsIso h := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ
  -- Since `X` is compact, `inv h` factors through a stage `P n`, so `X` is a retract of `P n`;
  -- the section `X ⟶ P n` factors through an object of the thick closure.
  obtain ⟨n, s, hs⟩ := hocolim_exists_factor P (towerMap G X) hX.down (inv h)
  obtain ⟨L, hL, a, b, rfl⟩ := compactlyFactorsThrough_tower G hG.isCompact n hX s
  refine ThickClosure.retract ⟨a, b ≫ (tower G X n).hom, ?_⟩ hL
  rw [← hh n, ← Category.assoc, ← Category.assoc, ← hs, IsIso.inv_hom_id]

/-- **Compact objects of a compactly generated triangulated category** [Ne96, §2]: if `C`
has coproducts and is compactly generated by a family `G` indexed by a small type, the compact
objects of `C` are exactly the objects of the thick closure of `G`. -/
theorem thickClosure_eq_isCompact [IsTriangulated C] [HasCoproducts.{max w v} C]
    (hG : CompactlyGenerates G) :
    ThickClosure (fun Y => ∃ i, G i = Y) = IsCompact.{max w v} := by
  funext X
  apply propext
  constructor
  · exact thickClosure_le_isCompact (by rintro _ ⟨i, rfl⟩; exact hG.isCompact i) X
  · exact thickClosure_of_isCompact G hG

end Generation

end DG
