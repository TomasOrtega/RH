import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hdvd : P ∣ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)` using `Ideal.dvd_iff_le.mpr hle`. Use `haveI : P.IsPrime := hP.isPrime`. Establish `hU : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P`.

Unfold `Algebra.IsUnramifiedAt`. Use `haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := inferInstance`. Conclude with `Algebra.FormallyUnramified.comp (𝓞 (maximalRealSubfield E)) (𝓞 E) (Localization.AtPrime P)`. Conclude with `(not_dvd_differentIdeal_iff.mpr hU) hdvd`.
-/
theorem differentIdeal_eq_top_of_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    [h : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] :
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hdvd : P ∣ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
  haveI : P.IsPrime := hP.isPrime
  have hU : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P := by
    unfold Algebra.IsUnramifiedAt
    haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := inferInstance
    exact Algebra.FormallyUnramified.comp (𝓞 (maximalRealSubfield E)) (𝓞 E) (Localization.AtPrime P)
  exact (not_dvd_differentIdeal_iff.mpr hU) hdvd

/- English proof (translation)
Introduce `E _ _ _ hU p`. Use `set F := maximalRealSubfield E`. Establish `hD : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E))`. Rewrite using `[differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E), differentIdeal_eq_top_of_unramified E, Ideal.top_mul]`. Establish `hD0 : differentIdeal ℤ (𝓞 F) ≠ ⊥` using `differentIdeal_ne_bot`.

Take `⟨δ, hδI, hδ0, ⟨n, hn, hnI⟩, -⟩` from `ideal_padic_generator_log_norm F (differentIdeal ℤ (𝓞 F)) p hD0`. Use `set δ' : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) δ`. Establish `hδ'I : δ' ∈ differentIdeal ℤ (𝓞 E)` using `by rw [hD]; exact Ideal.mem_map_of_mem _ hδI`. Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`. Use `⟨δ', hδ'I, fun h => hδ0 (hinj (h.trans (map_zero _).symm)), ?_, fun j => ?_⟩` and prove the remaining obligations.

Establish `: ((δ' : 𝓞 E) : E) = ((δ : F) : E)` using `rfl`. Rewrite using `[this]`. Conclude with `IsCMField.complexConj_apply_eq_self E (δ : F)`. Use `set j' : 𝓞 E →+* ℂ_[p] := j.comp (algebraMap (𝓞 E) E) with hj'`. Establish `hmax : ∀ b ∈ differentIdeal ℤ (𝓞 E), ‖j' b‖ ≤ ‖j' δ'‖`.

Introduce `b hb`. Rewrite `hb` using `[hD]`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp (hnI a ha)`. Establish `e` using `congrArg (fun z : 𝓞 F => j' (algebraMap (𝓞 F) (𝓞 E) z)) hy`. Simplify using `only [map_mul, map_natCast] at e`. Establish `h1` using `congrArg norm e`. Simplify using `only [norm_mul] at h1`.

Rewrite `h1` using `[LocGen.norm_natCast_cp p n hn, one_mul]`. Rewrite using `[← h1]`. Establish `: ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ ≤ 1` using `NI.norm_int_le j' _`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `smul c x _ hx`. Rewrite using `[smul_eq_mul, map_mul, norm_mul]`.

Establish `: ‖j' c‖ ≤ 1` using `NI.norm_int_le j' c`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(NI.logIdeal_eq (j.comp (algebraMap (𝓞 E) E)) _ hδ'I hmax).symm`.
-/
theorem exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ hU p
  set F := maximalRealSubfield E
  have hD : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E), differentIdeal_eq_top_of_unramified E, Ideal.top_mul]
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδI, hδ0, ⟨n, hn, hnI⟩, -⟩ := ideal_padic_generator_log_norm F (differentIdeal ℤ (𝓞 F)) p hD0
  set δ' : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) δ
  have hδ'I : δ' ∈ differentIdeal ℤ (𝓞 E) := by rw [hD]; exact Ideal.mem_map_of_mem _ hδI
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  refine ⟨δ', hδ'I, fun h => hδ0 (hinj (h.trans (map_zero _).symm)), ?_, fun j => ?_⟩
  · have : ((δ' : 𝓞 E) : E) = ((δ : F) : E) := rfl
    rw [this]
    exact IsCMField.complexConj_apply_eq_self E (δ : F)
  ·
    set j' : 𝓞 E →+* ℂ_[p] := j.comp (algebraMap (𝓞 E) E) with hj'
    have hmax : ∀ b ∈ differentIdeal ℤ (𝓞 E), ‖j' b‖ ≤ ‖j' δ'‖ := by
      intro b hb
      rw [hD] at hb
      induction hb using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hnI a ha)
        have e := congrArg (fun z : 𝓞 F => j' (algebraMap (𝓞 F) (𝓞 E) z)) hy
        simp only [map_mul, map_natCast] at e
        have h1 := congrArg norm e
        simp only [norm_mul] at h1
        rw [LocGen.norm_natCast_cp p n hn, one_mul] at h1
        rw [← h1]
        have : ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ ≤ 1 := NI.norm_int_le j' _
        calc ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ * ‖j' δ'‖ ≤ 1 * ‖j' δ'‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = ‖j' δ'‖ := one_mul _
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul c x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        have : ‖j' c‖ ≤ 1 := NI.norm_int_le j' c
        calc ‖j' c‖ * ‖j' x‖ ≤ 1 * ‖j' δ'‖ := mul_le_mul this hx (norm_nonneg _) zero_le_one
          _ = ‖j' δ'‖ := one_mul _
    exact (NI.logIdeal_eq (j.comp (algebraMap (𝓞 E) E)) _ hδ'I hmax).symm

end PositivityTheory.Xgf

end
