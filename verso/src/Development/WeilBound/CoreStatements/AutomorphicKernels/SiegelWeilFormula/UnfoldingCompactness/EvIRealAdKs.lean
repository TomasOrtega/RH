import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

/- English proof (translation)
Introduce `u hu`. Establish `hu1 : u.1 = 0` using `(RingEquiv.map_eq_zero_iff _).mp hu`. Take `⟨a, b⟩` from `u`. Simplify using `only at hu1`. Substitute `hu1` using the available equality.

Use `show ((0 : Ainf F) * _, b * 0) = ((0 : Ainf F), (0 : Af F))`. Simplify using the standard rewrite rules.
-/
theorem at_realAd_ks {F : Type} [Field F] [NumberField F] (t : ℝ) : At (evI F) (realAd F t) := by
  intro u hu
  have hu1 : u.1 = 0 := (RingEquiv.map_eq_zero_iff _).mp hu
  obtain ⟨a, b⟩ := u
  simp only at hu1
  subst hu1
  show ((0 : Ainf F) * _, b * 0) = ((0 : Ainf F), (0 : Af F))
  simp

/- English proof (translation)
Simplify using `[evI, realAd]`.
-/
theorem evI_realAd_ks {F : Type} [Field F] [NumberField F] (t : ℝ) :
    evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

/- English proof (translation)
Use `set c : ℝ := (Module.finrank ℚ F : ℝ) with hc`. Establish `hcpos : 0 < c`. Rewrite using `[hc]`. Conclude with `Module.finrank_pos` after adjusting the coercions. Use `set t : ℝ := 1 / (2 * c) with ht`.

Use `⟨-(realAd F t) * algebraMap F (AF F) x⁻¹, ?_⟩` and prove the remaining obligations. Establish `hl : -(-(realAd F t) * algebraMap F (AF F) x⁻¹ * algebraMap F (AF F) x) = realAd F t`. Rewrite using `[neg_mul, neg_mul, neg_neg, mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, mul_one]`. Rewrite using `[hl, hψ.2.2 _ (at_realAd_ks t), evI_realAd_ks, Algebra.trace_algebraMap, mixedEmbedding.finrank]`. Establish `: ((Module.finrank ℚ F • t : ℝ) : ℂ) = 1 / 2`.

Rewrite using `[nsmul_eq_mul, ← hc, ht]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Conclude with `div_self (by exact_mod_cast hcpos.ne')`. Rewrite using `[this]`.

Establish `h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I)` using `by ring`. Rewrite using `[h2, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions.
-/
theorem psi_moves_pf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) (hx : x ≠ 0) :
    ∃ l : AF F, ψ (-(l * algebraMap F (AF F) x)) ≠ 1 := by
  set c : ℝ := (Module.finrank ℚ F : ℝ) with hc
  have hcpos : 0 < c := by
    rw [hc]; exact_mod_cast Module.finrank_pos
  set t : ℝ := 1 / (2 * c) with ht
  refine ⟨-(realAd F t) * algebraMap F (AF F) x⁻¹, ?_⟩
  have hl : -(-(realAd F t) * algebraMap F (AF F) x⁻¹ * algebraMap F (AF F) x) = realAd F t := by
    rw [neg_mul, neg_mul, neg_neg, mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, mul_one]
  rw [hl, hψ.2.2 _ (at_realAd_ks t), evI_realAd_ks, Algebra.trace_algebraMap, mixedEmbedding.finrank]
  have : ((Module.finrank ℚ F • t : ℝ) : ℂ) = 1 / 2 := by
    rw [nsmul_eq_mul, ← hc, ht]; push_cast; field_simp
    exact div_self (by exact_mod_cast hcpos.ne')
  rw [this]
  have h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end PositivityTheory.SiegelWeilFormula.kunf

end
