import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
The claim follows from `(u.ker 0).mpr u.Λ.zero_mem`.
-/
theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

/- English proof (translation)
Establish `h` using `map_zpow (exHom u) (Multiplicative.ofAdd z) n`. Rewrite `h` using `[← ofAdd_zsmul]`. Simplify `h` using `[exHom]`.
-/
theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero]`. Conclude with `ex_zero u`. Consider the case `succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]`.
-/
theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

/- English proof (translation)
Establish `key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty]`. Conclude with `ex_zero u`.

Consider the case `@insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]`. Conclude with `key Finset.univ`.
-/
theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

/- English proof (translation)
Establish `e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1` using `fun B _ => by rw [Hom.one_def]; simp`. Establish `h2 : IsMonHom f'` using `laws.rigidity _ _ _ P.isAb P'.isAb f' (by`. Rewrite using `[e, e, ← ex_zero u, ← hf', map_zero, ex_zero])`. Use `(GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩` and prove the remaining obligations. Rewrite using `[← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]`.
-/
theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

/- English proof (translation)
Use `letI := P.isAb.comm`. Use `letI := P₀.isAb.comm`. Set `R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)` to `fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)`. Set `S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)` to `fun i => LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0`. Establish `hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0` using `fun i i' z => by`.

Use extensionality with `j`. Apply the tactic sequence `by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]`. Establish `hSR : ∀ z, ∑ i, S i (R i z) = z` using `fun z => by`. Use extensionality with `a`. Take `⟨⟨i, j⟩, rfl⟩` from `σ.surjective a`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Simplify using `[R, S, LinearMap.funLeft_apply]`. Introduce `b _ hb`. Simplify using `[S, hb.symm]`. Simplify using the standard rewrite rules.

Use `choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists`. Use `choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by`. Express the relevant statement in the definitionally equal form `R i' (S i z) ∈ _`. Rewrite using `[hRS]`. Use `split_ifs`.

Use `exacts [hz, u₀.Λ.zero_mem]).exists`. Use `haveI := fun i => (hpr i).1`. Use `haveI := fun i => (hinc i).1`. Establish `e1 : ∀ i, inc i ≫ pr i = 𝟙 _` using `fun i => hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by`. Rewrite using `[← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance`.

Establish `e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1` using `fun i i' hi => hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by`. Rewrite using `[← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]`. Simplify using `[hi.symm])`. Use the proof step `(fun z => by simp [ex_zero]) inferInstance`. Establish `e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i` using `hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by`.

Rewrite using `[PowMatrixLinear.comp_prod]`. Simplify using `only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]`. Rewrite using `[← ex_sum, hSR]`. Use the proof step `rfl) inferInstance`. Use `⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[PowMatrixLinear.prod_comp, Finset.prod_eq_single i]`. Rewrite using `[Category.assoc, e1, Category.comp_id]`. Introduce `b _ hb`. Rewrite using `[Category.assoc, e2 _ _ hb, MonObj.comp_one]`. Simplify using the standard rewrite rules.

Rewrite using `[← Category.comp_id x, e3, PowMatrixLinear.comp_prod]`. Simplify using `only [← Category.assoc, hx]`.
-/
theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
