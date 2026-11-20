import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ σ h M hM`. Establish `hsp : Submodule.span K (Set.range M) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Apply `hf0` to reduce the goal to its premises.

Establish `ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0`. Apply `hM` to reduce the goal to its premises. Introduce `s`. Establish `h1 : f (M s) = 0` using `hf (Submodule.subset_span ⟨s, rfl⟩)`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ]`.

Use `(Finset.sum_congr rfl fun j _ => ?_).trans h1` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Use `congrFun ha j` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Rewrite using `[this, smul_zero]`. Take `⟨b, hbS, hbsp, hli⟩` from `exists_linearIndependent K (Set.range M)`. Establish `hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K))`.

Rewrite using `[Subtype.range_coe, hbsp, hsp]`. Set `B` to `Module.Basis.mk hli hsp'`. Set `e : Fin h ≃ b` to `(Pi.basisFun K (Fin h)).indexEquiv B`. Establish `hmem : ∀ i, ∃ s, M s = (e i : Fin h → K)` using `fun i => hbS (e i).2`. Use `choose s hs using hmem`.

Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row`. Establish `: (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e`. Use function extensionality and compare the values at `i j`. Simplify using `[Matrix.row, hs]`.

Rewrite using `[this]`. Conclude with `hli.comp e e.injective`. Establish `hu` using `Matrix.linearIndependent_rows_iff_isUnit.mp hrows`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`.
-/
theorem exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
