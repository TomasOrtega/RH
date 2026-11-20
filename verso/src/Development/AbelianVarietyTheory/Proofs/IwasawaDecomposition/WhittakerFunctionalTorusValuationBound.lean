import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Topology

noncomputable section
namespace GlobalTheory.RootUp

variable {k : Type} [Field k]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs with h1 h2 <;> first | rfl | exact absurd (h2.2.trans h1.1.symm) h.symm | exact absurd (h2.1.trans h1.2.symm) h | simp`.
-/
theorem single_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    Matrix.single i j y * Matrix.single i j y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2 <;> first | rfl | exact absurd (h2.2.trans h1.1.symm) h.symm | exact absurd (h2.1.trans h1.2.symm) h | simp

def elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) : GL (Fin n) k :=
  ⟨1 + Matrix.single i j y, 1 - Matrix.single i j y, by
    rw [add_mul, one_mul, mul_sub, mul_one, single_sq h]; abel,
   by
    rw [sub_mul, one_mul, mul_add, mul_one, single_sq h]; abel⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    (elem h y : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j y := rfl

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, val_elem, Matrix.add_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> fun_prop`. Use `continuous_matrix fun a b => ?_ show Continuous fun y => (1 - Matrix.single i j y : Matrix (Fin n) (Fin n) k) a b` and prove the remaining obligations.

Simplify using `only [Matrix.sub_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem continuous_elem [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Continuous (elem (k := k) h) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun a b => ?_
    simp only [Function.comp_apply, val_elem, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · refine continuous_matrix fun a b => ?_
    show Continuous fun y => (1 - Matrix.single i j y : Matrix (Fin n) (Fin n) k) a b
    simp only [Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, val_elem]`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using `only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Establish `: ¬ (i = a ∧ j = a)` using `fun h' => h (h'.1.trans h'.2.symm)`. Simplify using `[this]`. Distinguish the cases in `hh : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `hh`.

Simplify using `[hab]`. Clear the denominators using the available nonvanishing facts. Simplify using `[hab, hh]`.
-/
theorem val_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (h : i ≠ j) (y : k) :
    ((diagT k (Fin n) t * elem h y * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + Matrix.single i j ((t i : k) / t j * y) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, val_elem]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h' => h (h'.1.trans h'.2.symm)
    simp [this]
  · by_cases hh : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hh
      simp [hab]
      field_simp
    · simp [hab, hh]

/- English proof (translation)
Use `(mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[val_conj_elem]`. Establish `hab : a ≠ b` using `(ne_of_lt hba).symm`. Establish `: ¬ (i = a ∧ j = b)`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `absurd hij (not_lt.2 hba.le)`. Simplify using `[Matrix.one_apply, Matrix.single_apply, hab, this]`. Rewrite using `[val_conj_elem]`. Establish `: ¬ (i = a ∧ j = a)` using `fun h' => hij.ne (h'.1.trans h'.2.symm)`. Simplify using `[Matrix.single_apply, this]`.
-/
theorem elem_conj_mem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : i < j) (y : k) :
    diagT k (Fin n) t * elem hij.ne y * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
  refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [val_conj_elem]
    have hab : a ≠ b := (ne_of_lt hba).symm
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩; exact absurd hij (not_lt.2 hba.le)
    simp [Matrix.one_apply, Matrix.single_apply, hab, this]
  · rw [val_conj_elem]
    have : ¬ (i = a ∧ j = a) := fun h' => hij.ne (h'.1.trans h'.2.symm)
    simp [Matrix.single_apply, this]

/- English proof (translation)
Rewrite using `[superDiag, val_conj_elem]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[Matrix.one_apply, hne]`. Introduce `b hb hbj`.

Establish `hib : i ≠ b`. Introduce and unpack `rfl`. Simplify using `at hb`. Simplify using `[Matrix.one_apply, Matrix.single_apply, hib, Ne.symm hbj]`. Introduce `hj`.

Simplify using `[hij] at hj`. Introduce `a _ hai`. Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Establish `hab : a ≠ b`. Introduce and unpack `rfl`.

Simplify using `at hb`. Simplify using `[Matrix.one_apply, Matrix.single_apply, hab, Ne.symm hai]`. Simplify using the standard rewrite rules.
-/
theorem superDiag_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : j.val = i.val + 1) (hne : i ≠ j) (y : k) :
    superDiag (diagT k (Fin n) t * elem hne y * (diagT k (Fin n) t)⁻¹) = (t i : k) / t j * y := by
  rw [superDiag, val_conj_elem]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.one_apply, hne]
    · intro b hb hbj
      have hib : i ≠ b := by
        rintro rfl; simp at hb
      simp [Matrix.one_apply, Matrix.single_apply, hib, Ne.symm hbj]
    · intro hj; simp [hij] at hj
  · intro a _ hai
    refine Finset.sum_eq_zero fun b hb => ?_
    have hab : a ≠ b := by
      rintro rfl; simp at hb
    simp [Matrix.one_apply, Matrix.single_apply, hab, Ne.symm hai]
  · simp

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ l hl x`. Take `⟨c, hc⟩` from `exists_hasConductor_of_continuous ψ hψ hψ1`. Establish `hU : {g : GL (Fin n) k | ρ g x = x} ∈ 𝓝 (1 : GL (Fin n) k)` using `(hρ x).mem_nhds (by simp)`. Establish `hall : ∀ᶠ y in 𝓝 (0 : k), ∀ i j : Fin n, ∀ h : i ≠ j, ρ (elem h y) x = x`. Use `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun h => ?_` and prove the remaining obligations.

Establish `hc0 : elem h (0 : k) = 1` using `Units.ext (by simp [val_elem])`. Conclude with `(continuous_elem h).continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU)`. Take `⟨s, hs⟩` from `exists_cball_subset hall`. Use `⟨c * s⁻¹, fun t i j hij hne0 => ?_⟩` and prove the remaining obligations. Establish `hlt : i < j` using `by rw [Fin.lt_iff_val_lt_val]; omega`.

Establish `key : ∀ y ∈ cball s, ψ (y * ((t i : k) / t j)) = 1`. Introduce `y hy`. Establish `hfix : ρ (elem hlt.ne y) x = x` using `hs hy i j hlt.ne`. Establish `h1` using `hl _ (elem_conj_mem t hlt y) (ρ (diagT k (Fin n) t) x)`. Rewrite `h1` using `[superDiag_conj_elem t hij hlt.ne, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hfix]`.

Establish `h2 : ((ψ ((t i : k) / t j * y) : Circle) : ℂ) = 1` using `(mul_eq_right₀ hne0).1 h1.symm`. Rewrite using `[mul_comm]`. Conclude with `Circle.coe_eq_one.1 h2`. Assume the negation of the conclusion as `hv`. Take `⟨y, hy, hne⟩` from `hc.exists_ne_one s (x := (t i : k) / t j) hv`.

Conclude with `hne (key y hy)`.
-/
theorem whittaker_torus_root_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ l hl x
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hU : {g : GL (Fin n) k | ρ g x = x} ∈ 𝓝 (1 : GL (Fin n) k) := (hρ x).mem_nhds (by simp)
  have hall : ∀ᶠ y in 𝓝 (0 : k), ∀ i j : Fin n, ∀ h : i ≠ j, ρ (elem h y) x = x := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun h => ?_
    have hc0 : elem h (0 : k) = 1 := Units.ext (by simp [val_elem])
    exact (continuous_elem h).continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU)
  obtain ⟨s, hs⟩ := exists_cball_subset hall
  refine ⟨c * s⁻¹, fun t i j hij hne0 => ?_⟩
  have hlt : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  have key : ∀ y ∈ cball s, ψ (y * ((t i : k) / t j)) = 1 := by
    intro y hy
    have hfix : ρ (elem hlt.ne y) x = x := hs hy i j hlt.ne
    have h1 := hl _ (elem_conj_mem t hlt y) (ρ (diagT k (Fin n) t) x)
    rw [superDiag_conj_elem t hij hlt.ne, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right,
      map_mul, Module.End.mul_apply, hfix] at h1
    have h2 : ((ψ ((t i : k) / t j * y) : Circle) : ℂ) = 1 := (mul_eq_right₀ hne0).1 h1.symm
    rw [mul_comm]
    exact Circle.coe_eq_one.1 h2
  by_contra hv
  obtain ⟨y, hy, hne⟩ := hc.exists_ne_one s (x := (t i : k) / t j) hv
  exact hne (key y hy)
end GlobalTheory.RootUp
