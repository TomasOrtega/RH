import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.IsCompactDbox

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

/- English proof (translation)
Rewrite using `[Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, ENNReal.coe_toReal]`.
-/
theorem real_box (ι : Type) [Fintype ι] (lam : Measure (Fv F v ⊗[F] E)) [SigmaFinite lam]
    (s : NNReal) (S : Set (Fv F v ⊗[F] E)) :
    ((s • Measure.pi (fun _ : ι => lam)) (Set.univ.pi fun _ => S)).toReal =
      (s : ℝ) * (lam S).toReal ^ Fintype.card ι := by
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, ENNReal.coe_toReal]

/- English proof (translation)
Distinguish the cases in `hK : OpenKer v ψ`. Distinguish the cases in `hnt : ∃ r, psiV F ψ v r ≠ 1`. Use `right set lam : Measure (Fv F v ⊗[F] E) := Measure.addHaar set a : ℝ := lam.real (OEv (E := E) v) set d : ℝ := lam.real (D1 (E := E) v ψ)`. Establish `ha : 0 < a` using `ENNReal.toReal_pos ((isOpen_oev (E := E) v).measure_ne_zero lam ⟨0, oev_zero (E := E) v⟩) (isCompact_oev (E := E) v).measure_lt_top.ne`. Establish `hd : 0 < d` using `ENNReal.toReal_pos ((conductor_isOpen (E := E) v ψ hK).measure_ne_zero lam ⟨0, diagonal_phase_first_vector (E := E) v ψ⟩) (conductor_isCompact (E := E) v ψ hK hnt).measure_lt_top.ne`.

Use `⟨Real.sqrt (a / d), Real.sqrt_pos.2 (div_pos ha hd), fun ι _ => ?_⟩` and prove the remaining obligations. Establish `hex` using `exists_sd (E := E) v ψ hK hnt ι`. Establish `hs : sdE (E` using `E) ψ v ι = hex.choose := by`. Rewrite using `[sdE_eq, dif_pos hex]`. Establish `hμ` using `hex.choose_spec`.

Use `hμ.1` as an intermediate fact. Use `⟨by rw [hs]; exact hμ.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Take `⟨s, hsμ⟩ : ∃ s : NNReal, hex.choose = s • Measure.pi (fun _ : ι => lam)` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Establish `h1` using `sd_test (E := E) v ψ ι hex.choose hμ (isOpen_dbox (E := E) v ψ hK ι).measurableSet (isCompact_dbox (E := E) v ψ hK hnt ι).measure_lt_top`.

Establish `hO : hex.choose.real (Obox (E` using `E) v ι) = (s : ℝ) * a ^ Fintype.card ι := by`. Rewrite using `[Measure.real, hsμ, Obox, real_box]`. Both sides reduce to the same expression. Establish `hD : hex.choose.real (Dbox (E` using `E) v ψ ι) = (s : ℝ) * d ^ Fintype.card ι := by`. Rewrite using `[Measure.real, hsμ, Dbox, real_box]`.

Both sides reduce to the same expression. Rewrite `h1` using `[hO, hD]`. Use `show (hex.choose (Obox (E := E) v ι)).toReal = _`. Rewrite using `[← Measure.real, hO]`. Establish `hsq : ((s : ℝ) * a ^ Fintype.card ι) ^ 2 = (Real.sqrt (a / d) ^ Fintype.card ι) ^ 2`.

Rewrite using `[← pow_mul, mul_comm _ 2, pow_mul, Real.sq_sqrt (div_pos ha hd).le, div_pow]`. Establish `hdn : d ^ Fintype.card ι ≠ 0` using `pow_ne_zero _ hd.ne'`. Rewrite using `[eq_div_iff hdn]`. Take the linear combination `(a ^ Fintype.card ι) * h1`. Conclude with `(pow_left_inj₀ (mul_nonneg s.2 (pow_nonneg ha.le _)) (pow_nonneg (Real.sqrt_nonneg _) _) two_ne_zero).1 hsq`.

Use `left push Not at hnt`. Introduce `ι _ _`. Rewrite using `[sdE_eq, dif_neg (no_sd_triv (E := E) v ψ ι hnt)]`. Use `left`. Introduce `ι _ _`.

Rewrite using `[sdE_eq, dif_neg (no_sd_noKer (E := E) v ψ ι hK)]`.
-/
theorem sdNorm_holds : SdNorm (E := E) ψ v := by
  by_cases hK : OpenKer v ψ
  · by_cases hnt : ∃ r, psiV F ψ v r ≠ 1
    · right
      set lam : Measure (Fv F v ⊗[F] E) := Measure.addHaar
      set a : ℝ := lam.real (OEv (E := E) v)
      set d : ℝ := lam.real (D1 (E := E) v ψ)
      have ha : 0 < a := ENNReal.toReal_pos
        ((isOpen_oev (E := E) v).measure_ne_zero lam ⟨0, oev_zero (E := E) v⟩) (isCompact_oev (E := E) v).measure_lt_top.ne
      have hd : 0 < d := ENNReal.toReal_pos
        ((conductor_isOpen (E := E) v ψ hK).measure_ne_zero lam ⟨0, diagonal_phase_first_vector (E := E) v ψ⟩)
        (conductor_isCompact (E := E) v ψ hK hnt).measure_lt_top.ne
      refine ⟨Real.sqrt (a / d), Real.sqrt_pos.2 (div_pos ha hd), fun ι _ => ?_⟩
      have hex := exists_sd (E := E) v ψ hK hnt ι
      have hs : sdE (E := E) ψ v ι = hex.choose := by
        rw [sdE_eq, dif_pos hex]
      have hμ := hex.choose_spec
      have := hμ.1
      refine ⟨by rw [hs]; exact hμ.1, ?_⟩
      rw [hs]
      obtain ⟨s, hsμ⟩ : ∃ s : NNReal, hex.choose = s • Measure.pi (fun _ : ι => lam) :=
        ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
      have h1 := sd_test (E := E) v ψ ι hex.choose hμ (isOpen_dbox (E := E) v ψ hK ι).measurableSet
        (isCompact_dbox (E := E) v ψ hK hnt ι).measure_lt_top
      have hO : hex.choose.real (Obox (E := E) v ι) = (s : ℝ) * a ^ Fintype.card ι := by
        rw [Measure.real, hsμ, Obox, real_box]; rfl
      have hD : hex.choose.real (Dbox (E := E) v ψ ι) = (s : ℝ) * d ^ Fintype.card ι := by
        rw [Measure.real, hsμ, Dbox, real_box]; rfl
      rw [hO, hD] at h1
      show (hex.choose (Obox (E := E) v ι)).toReal = _
      rw [← Measure.real, hO]
      have hsq : ((s : ℝ) * a ^ Fintype.card ι) ^ 2 = (Real.sqrt (a / d) ^ Fintype.card ι) ^ 2 := by
        rw [← pow_mul, mul_comm _ 2, pow_mul, Real.sq_sqrt (div_pos ha hd).le, div_pow]
        have hdn : d ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hd.ne'
        rw [eq_div_iff hdn]
        linear_combination (a ^ Fintype.card ι) * h1
      exact (pow_left_inj₀ (mul_nonneg s.2 (pow_nonneg ha.le _))
        (pow_nonneg (Real.sqrt_nonneg _) _) two_ne_zero).1 hsq
    · left
      push Not at hnt
      intro ι _ _
      rw [sdE_eq, dif_neg (no_sd_triv (E := E) v ψ ι hnt)]
  · left
    intro ι _ _
    rw [sdE_eq, dif_neg (no_sd_noKer (E := E) v ψ ι hK)]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
