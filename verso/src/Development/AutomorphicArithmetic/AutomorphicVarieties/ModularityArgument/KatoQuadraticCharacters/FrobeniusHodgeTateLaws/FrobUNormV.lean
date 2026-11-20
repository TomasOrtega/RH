import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Establish `hN : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Establish `hspan : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p`. Rewrite using `[Ideal.absNorm_span_singleton]`.

Establish `h1 : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ)` using `by simp`. Rewrite using `[h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]`. Simplify using the standard rewrite rules. Establish `hle : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).2 hv`. Establish `hd` using `Ideal.absNorm_dvd_absNorm_of_le hle`.

Rewrite `hd` using `[hspan]`. Break down `hp.eq_one_or_self_of_dvd _ hd with h1 | h1` into its components or cases. Conclude with `absurd (Ideal.absNorm_eq_one_iff.1 h1) v.isPrime.ne_top`. Rewrite using `[hN, h1]`.
-/
private theorem frobU_normV {p : ℕ} (hp : p.Prime) {v : Pl} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = p := by
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hspan : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_singleton]
    have h1 : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
    simp
  have hle : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hv
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [hspan] at hd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact absurd (Ideal.absNorm_eq_one_iff.1 h1) v.isPrime.ne_top
  · rw [hN, h1]

/- English proof (translation)
Introduce `l hl Ω _ _ _ e S A W hW`. Use `⟨?_, fun s hs => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨v, hA, hv⟩` from `hW.atL`. Take `⟨σ, hσ⟩` from `exists_isFrob (F := ℚ) hA`. Rewrite `hσ` using `[frobU_normV hl.out hv]`.

Conclude with `⟨σ, mem_Dec.2 hσ.1, hσ⟩`. Take `⟨c, hc⟩` from `hW.int`. Establish `hm : mat W s * mat W s⁻¹ = 1`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Establish `h11 : mat W s 1 1 * mat W s⁻¹ 1 1 = 1`.

Establish `h` using `congrFun (congrFun hm 1) 1`. Rewrite `h` using `[Matrix.mul_apply, Fin.sum_univ_two, hW.upper s hs, zero_mul, zero_add, Matrix.one_apply_eq]`. Conclude with `h`. Establish `ha` using `GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s 1 1)`. Establish `hb` using `GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s⁻¹ 1 1)`.

Establish `hn : ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ = 1` using `by rw [← norm_mul, h11, norm_one]`. Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])` using `rfl`. Rewrite using `[h, norm_algebraMap']`.

Conclude with `PadicInt.norm_units _`.
-/
theorem UpperTheory.V.Z.Kato.Joint.frobU :
    UpperTheory.V.Z.Kato.Joint.FrobU := by
  intro l hl Ω _ _ _ e S A W hW
  refine ⟨?_, fun s hs => ?_, fun s => ?_⟩
  · obtain ⟨v, hA, hv⟩ := hW.atL
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hA
    rw [frobU_normV hl.out hv] at hσ
    exact ⟨σ, mem_Dec.2 hσ.1, hσ⟩
  · obtain ⟨c, hc⟩ := hW.int
    have hm : mat W s * mat W s⁻¹ = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h11 : mat W s 1 1 * mat W s⁻¹ 1 1 = 1 := by
      have h := congrFun (congrFun hm 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, hW.upper s hs, zero_mul, zero_add, Matrix.one_apply_eq] at h
      exact h
    have ha := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s 1 1)
    have hb := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s⁻¹ 1 1)
    have hn : ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ = 1 := by rw [← norm_mul, h11, norm_one]
    refine le_antisymm ha ?_
    calc (1 : ℝ) = ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ := hn.symm
      _ ≤ ‖mat W s 1 1‖ := mul_le_of_le_one_right (norm_nonneg _) hb
  · have h : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    rw [h, norm_algebraMap']
    exact PadicInt.norm_units _
