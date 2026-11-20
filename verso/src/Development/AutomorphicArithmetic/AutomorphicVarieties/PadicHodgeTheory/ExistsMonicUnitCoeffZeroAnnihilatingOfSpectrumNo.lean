import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[l] a` using `Algebra.IsIntegral.isIntegral a`. Establish `hm : (minpoly ℚ_[l] a).Monic` using `minpoly.monic hint`. Establish `hs : spectralNorm ℚ_[l] (Om l) a = 1` using `ha`. Establish `hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1` using `(spectralValue_le_one_iff hm).1 (le_of_eq hs)`. Establish `h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1`.

Establish `h` using `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a`. Rewrite `h` using `[hs]`. Establish `hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree`. Conclude with `minpoly.natDegree_pos hint` after adjusting the coercions. Establish `h2` using `congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h`.

Simplify using `only [Real.one_rpow] at h2`. Rewrite `h2` using `[← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]`. Conclude with `h2.symm`. Establish `hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `n`. Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨Q, hQ, -, hQm⟩` from `lifts_and_natDegree_eq_and_monic hl hm`. Use `⟨Q, hQm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.isUnit_iff]`.

Rewrite `h0` using `[← hQ, coeff_map]`. Conclude with `h0`. Rewrite using `[← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]`. Conclude with `minpoly.aeval _ _`.
-/
private theorem exists_monic_integral_unit_root {l : ℕ} [Fact l.Prime] (a : Om l) (ha : ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (X - C a) ∣ Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have hm : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
  have hs : spectralNorm ℚ_[l] (Om l) a = 1 := ha
  have hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).1 (le_of_eq hs)
  have h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1 := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a
    rw [hs] at h
    have hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree := by
      exact_mod_cast minpoly.natDegree_pos hint
    have h2 := congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h
    simp only [Real.one_rpow] at h2
    rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one] at h2
    exact h2.symm
  have hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨Q, hQm, ?_, ?_⟩
  · rw [PadicInt.isUnit_iff]
    rw [← hQ, coeff_map] at h0
    exact h0
  · rw [← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval _ _

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => exact ⟨1, monic_one, by simp, by simp⟩`. Consider the case `cons a s ih`. Take `⟨Q, h1, h2, h3⟩` from `ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))`. Take `⟨R, g1, g2, g3⟩` from `exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))`.

Use `⟨R * Q, g1.mul h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_coeff_zero]`. Conclude with `g2.mul h2`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]`. Conclude with `mul_dvd_mul g3 h3`.
-/
private theorem aux_mul {l : ℕ} [Fact l.Prime] (s : Multiset (Om l)) (hs : ∀ a ∈ s, ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (s.map (fun a => X - C a)).prod ∣
        Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, monic_one, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨Q, h1, h2, h3⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    obtain ⟨R, g1, g2, g3⟩ := exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))
    refine ⟨R * Q, g1.mul h1, ?_, ?_⟩
    · rw [mul_coeff_zero]; exact g2.mul h2
    · rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]
      exact mul_dvd_mul g3 h3

/- English proof (translation)
Introduce `l _ L d F hF`. Use `set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ`. Establish `hχm : χ.Monic` using `Matrix.charpoly_monic _`. Take `⟨Q, h1, h2, h3⟩` from `aux_mul χ.roots (fun a ha => hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))`. Use `⟨Q, h1, h2, ?_⟩` and prove the remaining obligations.

Rewrite `h3` using `[← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map, IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map, map_dvd_map']`. Take `⟨R, hR⟩` from `h3`. Rewrite using `[hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]`.
-/
theorem UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), (∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ‖a‖ = 1) → ∃ P : ℤ_[l][X], P.Monic ∧ IsUnit (P.coeff 0) ∧ aeval F (P.map ((algebraMap ℚ_[l] ↥L).comp (algebraMap ℤ_[l] ℚ_[l]))) = 0 := by
  intro l _ L d F hF
  set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ
  have hχm : χ.Monic := Matrix.charpoly_monic _
  obtain ⟨Q, h1, h2, h3⟩ := aux_mul χ.roots (fun a ha =>
    hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))
  refine ⟨Q, h1, h2, ?_⟩
  rw [← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map,
    IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map,
    map_dvd_map'] at h3
  obtain ⟨R, hR⟩ := h3
  rw [hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]
