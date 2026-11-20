import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Introduce `O K _ _ _ hinj k ν F hF hco`. Choose the witnesses or unpack the hypotheses as in `⟨G, hG⟩ : F ∈ Set.range (map (algebraMap O K) : MvPolynomial (Fin k × Fin k) O →+* _) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `c hc`. Take `⟨u, hu, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp hc`.

Conclude with `hco u`. Substitute `hG` using the available equality. Establish `hcomm : ∀ (l j : Fin k) (p : MvPolynomial (Fin k × Fin k) O), map (algebraMap O K) (colAddGen O l j p) = colAddGen K l j (map (algebraMap O K) p)`. Introduce `l j p`. Proceed by induction on `p using MvPolynomial.induction_on`.

Use `next a => simp [colAddGen]`. Use `next p q hp hq => simp only [map_add, hp, hq]`. Use `next p x hp =>`. Simplify using `only [map_mul, hp, map_X]`. Use `congr 1`.

Simplify using `only [colAddGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`. Use `Submodule.mem_map.mpr ⟨G, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply, mem_weightedHomogeneousSubmodule] at hF ⊢`. Take `⟨h1, h2⟩` from `hF`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Conclude with `h1 (by rw [coeff_map]; exact fun h0 => hd ((map_eq_zero_iff _ hinj).mp h0))`. Introduce `l j hlj`. Apply `MvPolynomial.map_injective _ hinj` to reduce the goal to its premises.

Rewrite using `[hcomm, map_rename, h2 l j hlj]`. Use `first`. Consider the case `rfl`. Consider the case `simp [MvPolynomial.mapAlgHom]`.
-/
theorem intCapP : IntCapP := by
  intro O K _ _ _ hinj k ν F hF hco
  obtain ⟨G, hG⟩ : F ∈ Set.range (map (algebraMap O K) : MvPolynomial (Fin k × Fin k) O →+* _) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨u, hu, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact hco u
  subst hG
  have hcomm : ∀ (l j : Fin k) (p : MvPolynomial (Fin k × Fin k) O),
      map (algebraMap O K) (colAddGen O l j p) = colAddGen K l j (map (algebraMap O K) p) := by
    intro l j p
    induction p using MvPolynomial.induction_on
    next a => simp [colAddGen]
    next p q hp hq => simp only [map_add, hp, hq]
    next p x hp =>
      simp only [map_mul, hp, map_X]
      congr 1
      simp only [colAddGen, aeval_X]
      split_ifs <;> simp
  refine Submodule.mem_map.mpr ⟨G, ?_, ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero, AlgHom.toLinearMap_apply, mem_weightedHomogeneousSubmodule] at hF ⊢
    obtain ⟨h1, h2⟩ := hF
    refine ⟨?_, ?_⟩
    · intro d hd
      exact h1 (by rw [coeff_map]; exact fun h0 => hd ((map_eq_zero_iff _ hinj).mp h0))
    · intro l j hlj
      apply MvPolynomial.map_injective _ hinj
      rw [hcomm, map_rename, h2 l j hlj]
  · first
      | rfl
      | simp [MvPolynomial.mapAlgHom]

/- English proof (translation)
Unfold `nuNext`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem qa_nuNext_add {n : ℕ} (ν ν' : Fin n → ℕ) (s : Fin n) : nuNext (ν + ν') s = nuNext ν s + nuNext ν' s := by
  unfold nuNext
  split_ifs <;> simp

/- English proof (translation)
Unfold `nuNext`. Use `split_ifs with hs`. Conclude with `h (Fin.le_def.2 (Nat.le_succ _))`. Conclude with `Nat.zero_le _`.
-/
theorem qa_nuNext_le {n : ℕ} (ν : Fin n → ℕ) (h : Antitone ν) (s : Fin n) : nuNext ν s ≤ ν s := by
  unfold nuNext
  split_ifs with hs
  · exact h (Fin.le_def.2 (Nat.le_succ _))
  · exact Nat.zero_le _

/- English proof (translation)
Introduce `A _ k ν ν' hν hν'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hw, ← Finset.prod_mul_distrib, ← pow_add]`. Use `Finset.prod_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[qa_nuNext_add, Pi.add_apply]`. Establish `h1` using `qa_nuNext_le ν hν s`. Establish `h2` using `qa_nuNext_le ν' hν' s`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ (m : ℕ) (h1 : m ≤ k) (h2 : m ≤ k), eval (idPoint A k k) (lpMinor A m h1 h2) = 1`.

Introduce `m h1 h2`. Rewrite using `[lpMinor, RingHom.map_det]`. Use `(Matrix.det_one : (1 : Matrix (Fin m) (Fin m) A).det = 1)` and compare the differences between its conclusion and the goal. Use extensionality with `p q`. Simplify using `[idPoint, Matrix.one_apply, Fin.ext_iff]`.

Simplify using `only [hw, map_prod, map_pow, key, one_pow, Finset.prod_const_one]`.
-/
theorem hwMulP : HwMulP := by
  intro A _ k ν ν' hν hν'
  refine ⟨?_, ?_⟩
  · simp only [hw, ← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    congr 1
    rw [qa_nuNext_add, Pi.add_apply]
    have h1 := qa_nuNext_le ν hν s
    have h2 := qa_nuNext_le ν' hν' s
    omega
  · have key : ∀ (m : ℕ) (h1 : m ≤ k) (h2 : m ≤ k), eval (idPoint A k k) (lpMinor A m h1 h2) = 1 := by
      intro m h1 h2
      rw [lpMinor, RingHom.map_det]
      convert (Matrix.det_one : (1 : Matrix (Fin m) (Fin m) A).det = 1)
      ext p q
      simp [idPoint, Matrix.one_apply, Fin.ext_iff]
    simp only [hw, map_prod, map_pow, key, one_pow, Finset.prod_const_one]

end Formalism.MainNotions.flipOneThree.Pf

end
