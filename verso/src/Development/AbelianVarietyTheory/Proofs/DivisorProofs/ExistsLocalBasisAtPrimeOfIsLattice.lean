import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Take `⟨s, rfl⟩` from `hL`. Use `⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Introduce `i`. Conclude with `Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2)) (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)`. Consider the case `zero => intro i`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro i`.

Conclude with `Valuation.map_add_le _ (hx i) (hy i)`. Consider the case `smul a x _ hx`. Introduce `i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul]`. Conclude with `(mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)`.
-/
theorem exists_valuation_bound_of_fg {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) :
    ∃ C : WithZero (Multiplicative ℤ), ∀ x ∈ L, ∀ i, w.valuation E (x i) ≤ C := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2))
      (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; exact Valuation.map_add_le _ (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `Valuation.map_sum_le _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_prod]`. Establish `h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Use `(mul_le_of_le_one_left' h1).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_det_le_pow_of_entry_le {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (X : Matrix (Fin n) (Fin n) E)
    {C : WithZero (Multiplicative ℤ)} (h : ∀ i j, w.valuation E (X i j) ≤ C) :
    w.valuation E X.det ≤ C ^ n := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  have h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (mul_le_of_le_one_left' h1).trans ?_
  calc ∏ i, w.valuation E (X (σ i) i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod' fun i _ => h _ _
    _ = C ^ n := by simp

/- English proof (translation)
Take `⟨t, htS, hspan, hli⟩` from `exists_linearIndependent E S`. Rewrite `hspan` using `[hS]`. Set `b : Module.Basis t E (Fin n → E)` to `Module.Basis.mk hli (by simp [hspan])`. Establish `hfin : Finite t` using `Module.Finite.finite_basis b`. Use `Fintype.ofFinite t` as an intermediate fact.

Establish `hc : Fintype.card t = n`. Rewrite using `[← Module.finrank_eq_card_basis b]`. Simplify using the standard rewrite rules. Set `e : t ≃ Fin n` to `Fintype.equivFinOfCardEq hc`. Set `b'` to `b.reindex e`.

Use `⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col` using `b'.linearIndependent`. Use `Matrix.linearIndependent_cols_iff_isUnit.1 hli'` as an intermediate fact. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero`. Establish `: (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E)`.

Use function extensionality and compare the values at `i`. Simplify using `[b', b]`. Rewrite using `[this]`. Conclude with `htS (e.symm j).2`.
-/
theorem exists_det_ne_zero_col_mem_of_span_eq_top {E : Type} [Field E] {n : ℕ}
    {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤) :
    ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ ∀ j, (fun i => X i j) ∈ S := by
  classical
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent E S
  rw [hS] at hspan
  let b : Module.Basis t E (Fin n → E) := Module.Basis.mk hli (by simp [hspan])
  have hfin : Finite t := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  have hc : Fintype.card t = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  refine ⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩
  · have hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col := b'.linearIndependent
    have := Matrix.linearIndependent_cols_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  · have : (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E) := by
      funext i; simp [b', b]
    rw [this]
    exact htS (e.symm j).2

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_valuation_bound_of_fg w hL.fg`. Take `⟨X₀, hX₀, hX₀L⟩` from `exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top`. Establish `hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) → w.valuation E X.det ≤ C ^ n` using `fun X hX => valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i`. Take `⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩` from `Int.exists_greatest_of_bdd (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧ WithZero.log (w.valuation E X.det) = m) ⟨WithZero.log (C ^ n), by`. Introduce and unpack `_ ⟨X, hX, hXL, rfl⟩`.

Establish `h0 : w.valuation E X.det ≠ 0` using `by simpa using hX`. Establish `h1` using `hbd X hXL`. Establish `h2 : C ^ n ≠ 0` using `fun h => h0 (le_antisymm (h ▸ h1) zero_le')`. Conclude with `(WithZero.log_le_log h0 h2).2 h1⟩`. Use the proof step `⟨_, X₀, hX₀, hX₀L, rfl⟩`.

Establish `h0 : w.valuation E X.det ≠ 0` using `by simpa using hX`. Use `⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det`. Use `congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i` as an intermediate fact. Simplify `this` using `[Matrix.cramer_apply]`.

Establish `hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det`. Distinguish the cases in `hY : (X.updateCol i x).det = 0`. Simplify using `[hY]`. Establish `h1 : w.valuation E (X.updateCol i x).det ≠ 0` using `by simpa using hY`. Use `(WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`. Simplify `hXL j` using `[Matrix.updateCol_ne hj]`. Rewrite `hle` using `[← hcr, map_mul]`.

Establish `hpos : 0 < w.valuation E X.det` using `zero_lt_iff.2 h0`. Conclude with `(mul_le_iff_le_one_right hpos).1 hle`.
-/
theorem exists_local_basis_of_isLattice (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) :
    ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_valuation_bound_of_fg w hL.fg
  obtain ⟨X₀, hX₀, hX₀L⟩ := exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top
  have hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) →
      w.valuation E X.det ≤ C ^ n := fun X hX =>
    valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i
  obtain ⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      WithZero.log (w.valuation E X.det) = m)
    ⟨WithZero.log (C ^ n), by
      rintro _ ⟨X, hX, hXL, rfl⟩
      have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
      have h1 := hbd X hXL
      have h2 : C ^ n ≠ 0 := fun h => h0 (le_antisymm (h ▸ h1) zero_le')
      exact (WithZero.log_le_log h0 h2).2 h1⟩
    ⟨_, X₀, hX₀, hX₀L, rfl⟩
  have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
  refine ⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩
  have hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det := by
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i
    simpa [Matrix.cramer_apply] using this
  have hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det := by
    by_cases hY : (X.updateCol i x).det = 0
    · simp [hY]
    · have h1 : w.valuation E (X.updateCol i x).det ≠ 0 := by simpa using hY
      refine (WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simpa [Matrix.updateCol_ne hj] using hXL j
  rw [← hcr, map_mul] at hle
  have hpos : 0 < w.valuation E X.det := zero_lt_iff.2 h0
  exact (mul_le_iff_le_one_right hpos).1 hle

end GlobalTheory
