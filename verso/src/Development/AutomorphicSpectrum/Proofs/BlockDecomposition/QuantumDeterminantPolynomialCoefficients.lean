import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.QdetCoeff

/- English proof (translation)
Use `set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv`. Establish `hinj : Function.Injective v`. Introduce `i j h`. Simplify using `only [hv, Nat.cast_inj] at h`. Conclude with `Fin.ext h`.

Use `set V := Matrix.vandermonde v`. Establish `hdet : IsUnit V.det` using `(Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit`. Establish `hWV : V⁻¹ * V = 1` using `Matrix.nonsing_inv_mul V hdet`. Use `set k' : Fin (n + 1) := ⟨k, by omega⟩`. Establish `key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k`.

Repeatedly rewrite using `[hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Establish `: ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j`. Introduce `j`.

Rewrite using `[← hWV, Matrix.mul_apply]`. Both sides reduce to the same expression. Repeatedly rewrite using `[this, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[k']`.

Rewrite using `[← key]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)`.
-/
theorem coeff_mem_span_values {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) (a : ℕ → M)
    (f : ℂ → M) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range (n + 1), u ^ k • a k) (k : ℕ) (hk : k ≤ n) :
    a k ∈ Submodule.span ℂ (Set.range f) := by
  set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    simp only [hv, Nat.cast_inj] at h
    exact Fin.ext h
  set V := Matrix.vandermonde v
  have hdet : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set k' : Fin (n + 1) := ⟨k, by omega⟩
  have key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k := by
    simp_rw [hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j := by
      intro j
      rw [← hWV, Matrix.mul_apply]
      rfl
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [k']
  rw [← key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in

/- English proof (translation)
Rewrite using `[← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]`.
-/
theorem qdet_eq_sum_coeff {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (w : ℂ) :
    Formalism.REAL.qdet E w = ∑ j ∈ Finset.range (n + 1), w ^ j • (qdetPoly E).coeff j := by
  rw [← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
/- English proof (translation)
Rewrite using `[coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]`.
-/
theorem qdetPoly_coeff_top {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    (qdetPoly E).coeff n = 1 := by
  rw [coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]

/- English proof (translation)
Introduce `A _ _ n X c`. Use `set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb`. Use `set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha`. Establish `hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k`. Introduce `u`.

Rewrite using `[qdet_eq_sum_coeff]`. Establish `hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j = ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ))`. Introduce `j hj`. Rewrite using `[add_pow]`. Establish `hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1)`.

Establish `hj'` using `Finset.mem_range.mp hj`. Introduce `m hm`. Establish `hm'` using `Finset.mem_range.mp hm`. Conclude with `Finset.mem_range.mpr (by omega)`. Rewrite using `[← Finset.sum_subset hsub]`.

Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Introduce `m _ hm`. Simplify using `only [Finset.mem_range, not_lt] at hm`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]`. Repeatedly rewrite using `[ha, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Conclude with `Finset.sum_comm`. Use `⟨a, ?_, ?_, hexp⟩` and prove the remaining obligations. Simplify using `only [ha]`.

Rewrite using `[Finset.sum_eq_single n]`. Simplify using `[hb, qdetPoly_coeff_top]`. Introduce `j hj hjn`. Simplify using `only [Finset.mem_range] at hj`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`.

Simplify using the standard rewrite rules. Introduce `h`. Simplify using `at h`. Introduce `k`. Distinguish the cases in `hk : k ≤ n`.

Conclude with `coeff_mem_span_values n a _ hexp k hk`. Establish `: a k = 0`. Simplify using `only [ha]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_range] at hj`.

Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.
-/
theorem qdet_shift_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ),
    ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  intro A _ _ n X c
  set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb
  set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
    intro u
    rw [qdet_eq_sum_coeff]
    have hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j =
        ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ)) := by
      intro j hj
      rw [add_pow]
      have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        have hj' := Finset.mem_range.mp hj
        intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]
    simp_rw [ha, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine ⟨a, ?_, ?_, hexp⟩
  · simp only [ha]
    rw [Finset.sum_eq_single n]
    · simp [hb, qdetPoly_coeff_top]
    · intro j hj hjn
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · intro k
    by_cases hk : k ≤ n
    · exact coeff_mem_span_values n a _ hexp k hk
    · have : a k = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [this]; exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.CTFin.QdetCoeff
