import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

/- English proof (translation)
Introduce `p hp n`. Use `set pC : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hpC`. Establish `hpC0 : pC ≠ 0` using `(hp.map (Int.castRingHom ℂ)).ne_zero`. Use `set B : ℝ := ∑ x ∈ pC.roots.toFinset, ‖x‖ with hB`. Establish `hB0 : 0 ≤ B` using `Finset.sum_nonneg fun x _ => norm_nonneg x`.

Use `⟨n * B, fun M hM => ?_⟩` and prove the remaining obligations. Use `set A : Matrix (Fin n) (Fin n) ℂ := M.map (Int.castRingHom ℂ) with hA`. Establish `hAp : Polynomial.aeval A pC = 0`. Establish `e` using `Polynomial.aeval_algHom_apply ((Int.castRingHom ℂ).mapMatrix (m := Fin n)).toIntAlgHom M p`. Rewrite `e` using `[hM, map_zero]`.

Rewrite using `[hpC, show Int.castRingHom ℂ = algebraMap ℤ ℂ from rfl, Polynomial.aeval_map_algebraMap]`. Conclude with `e`. Establish `htr : ((M.trace : ℤ) : ℂ) = A.trace`. Simplify using `[hA, Matrix.trace, Matrix.map_apply]`. Establish `hroot : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ B`.

Introduce `μ hμ`. Break down `isEmpty_or_nonempty (Fin n) with hn | hn` into its components or cases. It suffices to derive a contradiction. Establish `hc` using `Polynomial.card_roots' A.charpoly`. Rewrite `hc` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_eq_zero]`.

Use `Multiset.card_pos_iff_exists_mem.2 ⟨μ, hμ⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsp : μ ∈ spectrum ℂ A` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)`. Establish `h1` using `spectrum.subset_polynomial_aeval A pC ⟨μ, hsp, rfl⟩`. Rewrite `h1` using `[hAp, spectrum.zero_eq, Set.mem_singleton_iff]`.

Establish `hmem : μ ∈ pC.roots.toFinset`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hpC0]`. Conclude with `h1`. Conclude with `Finset.single_le_sum (f := fun x => ‖x‖) (fun x _ => norm_nonneg x) hmem`. Establish `hsum : ‖A.trace‖ ≤ n * B`.

Rewrite using `[Matrix.trace_eq_sum_roots_charpoly]`. Use `(norm_multiset_sum_le _).trans ?_` and prove the remaining obligations. Use `(Multiset.sum_le_card_nsmul _ B (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hx; exact hroot μ hμ)).trans ?_` and prove the remaining obligations. Rewrite using `[Multiset.card_map, nsmul_eq_mul]`. Use `mul_le_mul_of_nonneg_right ?_ hB0` and prove the remaining obligations.

Use `Polynomial.card_roots' A.charpoly` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Conclude with `this` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem trace_le_of_aeval_monic_eq_zero :
    ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ,
      Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  intro p hp n
  set pC : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hpC
  have hpC0 : pC ≠ 0 := (hp.map (Int.castRingHom ℂ)).ne_zero
  set B : ℝ := ∑ x ∈ pC.roots.toFinset, ‖x‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => norm_nonneg x
  refine ⟨n * B, fun M hM => ?_⟩
  set A : Matrix (Fin n) (Fin n) ℂ := M.map (Int.castRingHom ℂ) with hA
  have hAp : Polynomial.aeval A pC = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Int.castRingHom ℂ).mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hM, map_zero] at e
    rw [hpC, show Int.castRingHom ℂ = algebraMap ℤ ℂ from rfl, Polynomial.aeval_map_algebraMap]
    exact e
  have htr : ((M.trace : ℤ) : ℂ) = A.trace := by
    simp [hA, Matrix.trace, Matrix.map_apply]
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ B := by
    intro μ hμ
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exfalso
      have hc := Polynomial.card_roots' A.charpoly
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_eq_zero] at hc
      have := Multiset.card_pos_iff_exists_mem.2 ⟨μ, hμ⟩
      omega
    have hsp : μ ∈ spectrum ℂ A :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
    have h1 := spectrum.subset_polynomial_aeval A pC ⟨μ, hsp, rfl⟩
    rw [hAp, spectrum.zero_eq, Set.mem_singleton_iff] at h1
    have hmem : μ ∈ pC.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpC0]; exact h1
    exact Finset.single_le_sum (f := fun x => ‖x‖) (fun x _ => norm_nonneg x) hmem
  have hsum : ‖A.trace‖ ≤ n * B := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine (norm_multiset_sum_le _).trans ?_
    refine (Multiset.sum_le_card_nsmul _ B (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hx; exact hroot μ hμ)).trans ?_
    rw [Multiset.card_map, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have := Polynomial.card_roots' A.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  calc ((M.trace : ℤ) : ℝ) = (((M.trace : ℤ) : ℂ)).re := by simp
    _ ≤ ‖((M.trace : ℤ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ n * B := by rw [htr]; exact hsum

end GlobalTheory.RedTh
