import DG.Category.Tensor.Basic
import DG.Category.Homotopy.Hom
import DG.Homotopy.KProjective
import Mathlib.Algebra.Exact.Basic

/-!
# Graded split filtrations of dg coends

Over a degree-zero dg category, the coend preserves exactness of sequences
with graded splittings. If an exhaustive increasing sequence of stages
is graded split inside the full module, acyclicity of the stages gives
acyclicity of the full coend.
-/

noncomputable section

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite
open scoped CatModule

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (N : CatModule (DGOpposite C)) {A B D : CatModule C}
  (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

include h₀ in
private theorem balanced_cochain (r : CatModule.Cochain B A 0) :
    Balanced fun X => (tmulAddHom N A X).compl₂ (r.app X) := by
  intro X Y f n m
  change tmul X (n <• f) (r.app X m) = tmul Y n (r.app Y (f • m))
  rw [ract_tmul, r.map_smul (h₀ f), zero_mul, koszulSign_zero, one_smul]

/-- A degree-zero graded module map induces an additive map on the coend. -/
def mapRightCochain (r : CatModule.Cochain B A 0) :
    CatTensorProduct N B →+ CatTensorProduct N A :=
  lift _ (balanced_cochain N h₀ r)

include h₀ in
@[simp]
theorem mapRightCochain_tmul (r : CatModule.Cochain B A 0) (X : C)
    (n : N.obj (op X)) (b : B.obj X) :
    mapRightCochain N h₀ r (tmul X n b) = tmul X n (r.app X b) :=
  lift_tmul _ (balanced_cochain N h₀ r) X n b

include h₀ in
/-- A short exact sequence with a graded splitting stays short exact after taking the coend. -/
theorem exact_of_graded_split (i : A ⟶ B) (p : B ⟶ D)
    (r : CatModule.Cochain B A 0) (s : CatModule.Cochain D B 0)
    (hri : ∀ X a, r.app X (i.app X a) = a)
    (hps : ∀ X a, p.app X (s.app X a) = a)
    (hpi : ∀ X a, p.app X (i.app X a) = 0)
    (hsplit : ∀ X b, i.app X (r.app X b) + s.app X (p.app X b) = b) :
    Function.Injective (map (𝟙 N) i) ∧
    Function.Exact (map (𝟙 N) i) (map (𝟙 N) p) ∧
    Function.Surjective (map (𝟙 N) p) := by
  let ri : CatTensorProduct N B →+ CatTensorProduct N A := mapRightCochain N h₀ r
  let sp : CatTensorProduct N D →+ CatTensorProduct N B := mapRightCochain N h₀ s
  have hleft : ri.comp (map (𝟙 N) i) = AddMonoidHom.id _ := by
    apply addHom_ext
    intro X n a
    simp [ri, hri]
  have hright : (map (𝟙 N) p).comp sp = AddMonoidHom.id _ := by
    apply addHom_ext
    intro X n a
    simp [sp, hps]
  have hzero : (map (𝟙 N) p).comp (map (𝟙 N) i) = 0 := by
    apply addHom_ext
    intro X n a
    simp [hpi]
  have hadd : (map (𝟙 N) i).comp ri + sp.comp (map (𝟙 N) p) = AddMonoidHom.id _ := by
    apply addHom_ext
    intro X n b
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      ri, sp, mapRightCochain_tmul, map_tmul, CatModule.id_app]
    rw [← tmul_add, hsplit]
  refine ⟨(fun x y h => ?_), (fun b => ?_), (fun d => ⟨sp d, ?_⟩)⟩
  · exact (DFunLike.congr_fun hleft x).symm.trans
      ((congrArg ri h).trans (DFunLike.congr_fun hleft y))
  · constructor
    · intro hb
      exact ⟨ri b, by simpa [hb] using DFunLike.congr_fun hadd b⟩
    · rintro ⟨a, rfl⟩
      exact DFunLike.congr_fun hzero a
  · exact DFunLike.congr_fun hright d

end DG.CatTensorProduct

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (N : CatModule (DGOpposite C))
  (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

include h₀ in
/-- Tensor cycles in a union of graded split submodules already bound in a finite stage
when each stage has acyclic coend. -/
theorem isAcyclic_of_graded_split_union {M : CatModule C}
    (S : ℕ → CatModule C) (i : ∀ n, S n ⟶ M)
    (r : ∀ n, CatModule.Cochain M (S n) 0)
    (hri : ∀ n X x, (r n).app X ((i n).app X x) = x)
    (inc : ∀ m n, m ≤ n → (S m ⟶ S n))
    (hinc : ∀ m n h, inc m n h ≫ i n = i m)
    (hcover : ∀ X (x : M.obj X), ∃ n y, (i n).app X y = x)
    (hS : ∀ n, DG.IsAcyclic (CatTensorProduct N (S n))) :
    DG.IsAcyclic (CatTensorProduct N M) := by
  have hleft (n : ℕ) :
      (mapRightCochain N h₀ (r n)).comp (map (𝟙 N) (i n)) = AddMonoidHom.id _ := by
    apply addHom_ext
    intro X x y
    simp [hri]
  have hcover' (x : CatTensorProduct N M) : ∃ n y, map (𝟙 N) (i n) y = x := by
    induction x using induction_on with
    | zero => exact ⟨0, 0, map_zero _⟩
    | tmul X a b =>
      obtain ⟨m, b', hb⟩ := hcover X b
      exact ⟨m, tmul X a b', by simp [hb]⟩
    | add a b ha hb =>
      obtain ⟨m, a', ha'⟩ := ha
      obtain ⟨n, b', hb'⟩ := hb
      let k := max m n
      let a'' := map (𝟙 N) (inc m k (le_max_left m n)) a'
      let b'' := map (𝟙 N) (inc n k (le_max_right m n)) b'
      refine ⟨k, a'' + b'', ?_⟩
      simp only [map_add, a'', b'', ← map_comp_apply, Category.id_comp, hinc, ha', hb']
  refine DG.isAcyclic_iff.mpr fun j x hx hdx => ?_
  obtain ⟨n, y, hy⟩ := hcover' x
  let F := map (𝟙 N) (i n)
  have hF : Function.Injective F :=
    fun a b h => (DFunLike.congr_fun (hleft n) a).symm.trans
      ((congrArg (mapRightCochain N h₀ (r n)) h).trans (DFunLike.congr_fun (hleft n) b))
  let yj := (DirectSum.decompose (grading (M := CatTensorProduct N (S n))) y j).val
  have hyj : yj ∈ grading j :=
    (DirectSum.decompose (grading (M := CatTensorProduct N (S n))) y j).property
  have hFy : F yj = x := by
    have hh := coe_decompose_map_of_map_mem F (fun h => map_mem _ _ h) y j
    change _ = F yj at hh
    rw [show F y = x from hy, DirectSum.decompose_of_mem_same _ hx] at hh
    exact hh.symm
  have hdy : d yj = 0 := hF (by rw [map_d, hFy, hdx, map_zero])
  obtain ⟨z, hz, hdz⟩ := (hS n).exists_d_eq hyj hdy
  exact ⟨F z, map_mem _ _ hz, by rw [← map_d, hdz, hFy]⟩

end DG.CatTensorProduct

namespace DG

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DGAddCommGroup A] [DGAddCommGroup B] [DGAddCommGroup C]

private theorem exists_homogeneous_preimage (f : A →+ B)
    (hf : ∀ {j : ℤ} {x : A}, x ∈ grading j → f x ∈ grading j)
    {j : ℤ} {y : B} (hy : y ∈ grading j) (h : ∃ x, f x = y) :
    ∃ x ∈ grading j, f x = y := by
  obtain ⟨x, hx⟩ := h
  refine ⟨(DirectSum.decompose (grading (M := A)) x j).val,
    (DirectSum.decompose (grading (M := A)) x j).property, ?_⟩
  have hm := coe_decompose_map_of_map_mem f hf x j
  rw [hx, DirectSum.decompose_of_mem_same _ hy] at hm
  exact hm.symm

/-- In a short exact sequence of dg abelian groups, acyclicity of both ends
implies acyclicity of the middle. -/
theorem isAcyclic_of_shortExact_addHom (i : A →+ B) (p : B →+ C)
    (hi : ∀ {j : ℤ} {x : A}, x ∈ grading j → i x ∈ grading j)
    (hp : ∀ {j : ℤ} {x : B}, x ∈ grading j → p x ∈ grading j)
    (hid : ∀ x, i (d x) = d (i x)) (hpd : ∀ x, p (d x) = d (p x))
    (hinj : Function.Injective i) (hex : Function.Exact i p) (hsurj : Function.Surjective p)
    (hA : IsAcyclic A) (hC : IsAcyclic C) : IsAcyclic B := by
  refine isAcyclic_iff.mpr fun n y hy hdy => ?_
  have hpy : d (p y) = 0 := by rw [← hpd, hdy, map_zero]
  obtain ⟨c, hc, hdc⟩ := hC.exists_d_eq (hp hy) hpy
  obtain ⟨z, hz, hpz⟩ := exists_homogeneous_preimage p hp hc (hsurj c)
  have hker : p (y - d z) = 0 := by rw [map_sub, hpd, hpz, hdc, sub_self]
  have hres : y - d z ∈ grading n := sub_mem hy (by simpa using d_mem hz)
  obtain ⟨a, ha, hia⟩ := exists_homogeneous_preimage i hi hres ((hex _).mp hker)
  have hda : d a = 0 := by
    apply hinj
    rw [hid, hia, map_sub, d_d, hdy, sub_zero, map_zero]
  obtain ⟨b, hb, hdb⟩ := hA.exists_d_eq ha hda
  refine ⟨z + i b, add_mem hz (hi hb), ?_⟩
  rw [map_add, ← hid, hdb, hia]
  abel

end DG
