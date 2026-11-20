import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TsubValInjective
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

/- English proof (translation)
Introduce `n ε H _ _ σ D E hσ hD Z _ hZK γ W _ _ _ T hT Φ hΦ hint`. Take `⟨-, -, hTy⟩` from `hT`. Take `⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩` from `hTy`. Establish `hker : LinearMap.ker Φ = ⊥`. Break down `hirr (LinearMap.ker Φ) le_top (fun g hg w hw => by` into its components or cases.

Rewrite `hw`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hint g hg w, hw, map_zero]) with h | h`. Conclude with `h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) hΦ`. Establish `hinj : Function.Injective Φ` using `LinearMap.ker_eq_bot.1 hker`.

Set `ι : W →ₗ[ℂ] TensorProduct ℂ D (Fock n)` to `tsubVal Z ∘ₗ Φ`. Establish `hιinj : Function.Injective ι` using `tsubVal_injective.comp hinj`. Establish `hιK : ∀ (k : Mat n) (hk : k ∈ Kset ε) (w : W), wK hD hk (ι w) = ι (T k w)`. Introduce `k hk w`. Use `show wK hD hk (tsubVal Z (Φ w)) = tsubVal Z (Φ (T k w))`.

Rewrite using `[hint k (by rw [mir_Kset_eq]; exact hk) w, tOp_apply hD hZK hk]`. Set `S' : Submodule ℂ (TensorProduct ℂ D (Fock n))` to `LinearMap.range ι`. Establish `hS'fin : FiniteDimensional ℂ S'` using `LinearMap.finiteDimensional_range ι`. Establish `hS'K : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S'`. Introduce and unpack `k hk _ ⟨w, rfl⟩`.

Conclude with `⟨T k w, (hιK k hk w).symm⟩`. Establish `hwt : ∀ (μ : Fin n → ℝ) (w : W), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w → ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w`. Introduce `μ w hw θ`. Rewrite using `[hιK _ _ w, hw θ (by rw [mir_Kset_eq]; exact diag_mem_Kset' ε θ), map_smul]`. Establish `hwt' : ∀ (μ : Fin n → ℝ) (w : W), (∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w) → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w`.

Introduce `μ w hw θ _`. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[map_smul, ← hιK _ (diag_mem_Kset' ε θ) w, hw θ]`. Use `set z := ι v with hz`. Establish `hz0 : z ≠ 0` using `fun h => hv0 (hιinj (h.trans (map_zero ι).symm))`.

Establish `hzd : ∀ a, diagE ε (eT E) cpT cmT a a z = ((γ a : ℝ) : ℂ) • z` using `diagE_wt_of_wK hσ hD (hwt γ v hvw)`. Use `⟨z, tsubVal_mem (Φ v), hz0, hzd, fun a b hab hε => ?_⟩` and prove the remaining obligations. Use `set y := diagE ε (eT E) cpT cmT a b z with hy`. Establish `hyS : y ∈ S'` using `diagE_mem_of_wK hσ hD S' hS'fin hS'K hε ⟨v, rfl⟩`. Take `⟨w', hw'⟩` from `hyS`.

Establish `hyd : ∀ c, diagE ε (eT E) cpT cmT c c y = (((γ + root a b) c : ℝ) : ℂ) • y`. Introduce `c`. Establish `hc` using `congrArg (fun F => F z) (diagAction_commutator (eT_isGlRep hD.glRep) cpT_cmT_isCAR (eT_commutesCAR E) ε c c a b rfl hε)`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply] at hc`. Rewrite `hc` using `[hzd c, map_smul]`.

Establish `e1 : diagE ε (eT E) cpT cmT c c y = ((γ c : ℝ) : ℂ) • y + ((if c = a then diagE ε (eT E) cpT cmT c b else 0) - (if b = c then diagE ε (eT E) cpT cmT a c else 0)) z`. Rewrite using `[hy, LinearMap.sub_apply, ← hc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Distinguish the cases in `hca : c = a`.

Substitute `hca` using the available equality. Establish `hcb : ¬ b = c` using `fun h => (ne_of_lt hab) h.symm`. Simplify using `only [if_neg hcb, sub_zero, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]`. Rewrite using `[Pi.single_eq_of_ne (ne_of_lt hab)]`. Simplify using `only [sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]`.

Both sides reduce to the same expression. Distinguish the cases in `hcb : b = c`. Substitute `hcb` using the available equality. Simplify using `only [if_neg hca, zero_sub, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, LinearMap.neg_apply, ↓reduceIte]`. Rewrite using `[Pi.single_eq_of_ne hca]`.

Simplify using `only [zero_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, add_smul, neg_smul, one_smul]`. Both sides reduce to the same expression. Simplify using `only [if_neg hca, if_neg hcb, sub_zero, LinearMap.zero_apply, add_zero, Pi.add_apply, root, Pi.sub_apply]`. Rewrite using `[Pi.single_eq_of_ne hca, Pi.single_eq_of_ne (Ne.symm hcb)]`. Simplify using the standard rewrite rules.

Establish `hw'w : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T (γ + root a b) w'`. Apply `hwt'` to reduce the goal to its premises. Introduce `θ`. Rewrite using `[hw']`. Conclude with `wK_diag_wt hσ hD hyd θ`.

Assume the negation of the conclusion as `hne`. Establish `hw'0 : w' ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hw', h, map_zero]`.

Conclude with `not_cdom_add_root ε γ hab (hdom _ w' (Submodule.mem_top) hw'0 hw'w)`.
-/
theorem intertwiner_preserves_highestWeight : HWVec := by
  intro n ε H _ _ σ D E hσ hD Z _ hZK γ W _ _ _ T hT Φ hΦ hint
  obtain ⟨-, -, hTy⟩ := hT
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hTy

  have hker : LinearMap.ker Φ = ⊥ := by
    rcases hirr (LinearMap.ker Φ) le_top (fun g hg w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hint g hg w, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hΦ
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  let ι : W →ₗ[ℂ] TensorProduct ℂ D (Fock n) := tsubVal Z ∘ₗ Φ
  have hιinj : Function.Injective ι := tsubVal_injective.comp hinj
  have hιK : ∀ (k : Mat n) (hk : k ∈ Kset ε) (w : W), wK hD hk (ι w) = ι (T k w) := by
    intro k hk w
    show wK hD hk (tsubVal Z (Φ w)) = tsubVal Z (Φ (T k w))
    rw [hint k (by rw [mir_Kset_eq]; exact hk) w, tOp_apply hD hZK hk]
  let S' : Submodule ℂ (TensorProduct ℂ D (Fock n)) := LinearMap.range ι
  have hS'fin : FiniteDimensional ℂ S' := LinearMap.finiteDimensional_range ι
  have hS'K : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S' := by
    rintro k hk _ ⟨w, rfl⟩
    exact ⟨T k w, (hιK k hk w).symm⟩

  have hwt : ∀ (μ : Fin n → ℝ) (w : W), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w →
      ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w := by
    intro μ w hw θ
    rw [hιK _ _ w, hw θ (by rw [mir_Kset_eq]; exact diag_mem_Kset' ε θ), map_smul]
  have hwt' : ∀ (μ : Fin n → ℝ) (w : W),
      (∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w := by
    intro μ w hw θ _
    apply hιinj
    rw [map_smul, ← hιK _ (diag_mem_Kset' ε θ) w, hw θ]
  set z := ι v with hz
  have hz0 : z ≠ 0 := fun h => hv0 (hιinj (h.trans (map_zero ι).symm))
  have hzd : ∀ a, diagE ε (eT E) cpT cmT a a z = ((γ a : ℝ) : ℂ) • z :=
    diagE_wt_of_wK hσ hD (hwt γ v hvw)
  refine ⟨z, tsubVal_mem (Φ v), hz0, hzd, fun a b hab hε => ?_⟩
  set y := diagE ε (eT E) cpT cmT a b z with hy
  have hyS : y ∈ S' := diagE_mem_of_wK hσ hD S' hS'fin hS'K hε ⟨v, rfl⟩
  obtain ⟨w', hw'⟩ := hyS
  have hyd : ∀ c, diagE ε (eT E) cpT cmT c c y = (((γ + root a b) c : ℝ) : ℂ) • y := by
    intro c
    have hc := congrArg (fun F => F z)
      (diagAction_commutator (eT_isGlRep hD.glRep) cpT_cmT_isCAR (eT_commutesCAR E) ε c c a b rfl hε)
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
    rw [hzd c, map_smul] at hc
    have e1 : diagE ε (eT E) cpT cmT c c y =
        ((γ c : ℝ) : ℂ) • y + ((if c = a then diagE ε (eT E) cpT cmT c b else 0) -
          (if b = c then diagE ε (eT E) cpT cmT a c else 0)) z := by
      rw [hy, LinearMap.sub_apply, ← hc]; abel
    rw [e1]
    by_cases hca : c = a
    · subst hca
      have hcb : ¬ b = c := fun h => (ne_of_lt hab) h.symm
      simp only [if_neg hcb, sub_zero, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      rw [Pi.single_eq_of_ne (ne_of_lt hab)]
      simp only [sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rfl
    · by_cases hcb : b = c
      · subst hcb
        simp only [if_neg hca, zero_sub, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same,
          LinearMap.neg_apply, ↓reduceIte]
        rw [Pi.single_eq_of_ne hca]
        simp only [zero_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, add_smul, neg_smul,
          one_smul]
        rfl
      · simp only [if_neg hca, if_neg hcb, sub_zero, LinearMap.zero_apply, add_zero, Pi.add_apply, root,
          Pi.sub_apply]
        rw [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne (Ne.symm hcb)]
        simp
  have hw'w : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T (γ + root a b) w' := by
    apply hwt'
    intro θ
    rw [hw']
    exact wK_diag_wt hσ hD hyd θ
  by_contra hne
  have hw'0 : w' ≠ 0 := by
    intro h; apply hne; rw [← hw', h, map_zero]
  exact not_cdom_add_root ε γ hab (hdom _ w' (Submodule.mem_top) hw'0 hw'w)

end GlobalTheory.PsCo.PcEF
