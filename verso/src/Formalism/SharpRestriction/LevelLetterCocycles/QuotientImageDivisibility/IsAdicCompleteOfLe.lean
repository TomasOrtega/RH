import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.OLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
Establish `hpow : ∀ n, I ^ (a * n) ≤ J ^ n` using `fun n => by`. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_right_mono h1 n`. Establish `hJI : ∀ n, J ^ n ≤ I ^ n` using `fun n => Ideal.pow_right_mono h2 n`. Establish `hsm : ∀ (K L : Ideal R), K ≤ L → K • (⊤ : Submodule R R) ≤ L • ⊤` using `fun K L h => Submodule.smul_mono_left h`.

Establish `hH : IsHausdorff I R` using `⟨fun x hx => by`. Apply `IsHausdorff.haus hJ.toIsHausdorff x` to reduce the goal to its premises. Introduce `n`. Conclude with `(hx (a * n)).mono (hsm _ _ (hpow n))⟩`. Establish `hP : IsPrecomplete I R` using `⟨fun f hf => by`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec hJ.toIsPrecomplete (f := fun k => f (a * k)) (fun {m n} hmn => (hf (Nat.mul_le_mul_left a hmn)).mono (hsm _ _ (hpow m)))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h3 : f n ≡ f (a * n) [SMOD I ^ n • (⊤ : Submodule R R)]` using `hf (by nlinarith)`. Conclude with `h3.trans ((hL n).mono (hsm _ _ (hJI n)))⟩`. Conclude with `⟨⟩`.
-/
theorem isAdicComplete_of_le {R : Type} [CommRing R] (I J : Ideal R) (a : ℕ) (ha : 1 ≤ a)
    (h1 : I ^ a ≤ J) (h2 : J ≤ I) [hJ : IsAdicComplete J R] : IsAdicComplete I R := by
  have hpow : ∀ n, I ^ (a * n) ≤ J ^ n := fun n => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 n
  have hJI : ∀ n, J ^ n ≤ I ^ n := fun n => Ideal.pow_right_mono h2 n
  have hsm : ∀ (K L : Ideal R), K ≤ L → K • (⊤ : Submodule R R) ≤ L • ⊤ := fun K L h =>
    Submodule.smul_mono_left h
  have hH : IsHausdorff I R := ⟨fun x hx => by
    apply IsHausdorff.haus hJ.toIsHausdorff x
    intro n
    exact (hx (a * n)).mono (hsm _ _ (hpow n))⟩
  have hP : IsPrecomplete I R := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun k => f (a * k)) (fun {m n} hmn =>
      (hf (Nat.mul_le_mul_left a hmn)).mono (hsm _ _ (hpow m)))
    refine ⟨L, fun n => ?_⟩
    have h3 : f n ≡ f (a * n) [SMOD I ^ n • (⊤ : Submodule R R)] := hf (by nlinarith)
    exact h3.trans ((hL n).mono (hsm _ _ (hJI n)))⟩
  exact ⟨⟩

/- English proof (translation)
Use `Formalism.MainNotions.WachCoordinates.Br.complete_OL LL` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`. Establish `hlm` using `Formalism.BasicNotions.Examples₂.LB.l_mem_max LL`. Establish `hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0`. Introduce `h`.

Establish `h' : ((((l : ℕ) : ↥(OL LL)) : ↥LL.1) : Om l) = 0` using `by rw [h]; rfl`. Normalize the coercions in `at h'`. Conclude with `(Fact.out : l.Prime).ne_zero h'`. Take `⟨e, u, hle⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`.

Establish `he : 1 ≤ e`. Assume the negation of the conclusion as `h0`. Use `push Not at h0`. Establish `: e = 0` using `by omega`. Rewrite `hle` using `[this, pow_zero, mul_one]`.

Rewrite `hlm` using `[hle]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hlm u.isUnit`. Use `isAdicComplete_of_le _ (Ideal.span {((l : ℕ) : ↥(OL LL))}) e he ?_ ?_` and prove the remaining obligations. Rewrite using `[hmax, Ideal.span_singleton_pow, hle, Ideal.span_singleton_mul_left_unit u.isUnit]`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ rfl`. Conclude with `hlm`.
-/
theorem complete_max {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  have := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : ↥(OL LL)) : ↥LL.1) : Om l) = 0 := by rw [h]; rfl
    norm_cast at h'
    exact (Fact.out : l.Prime).ne_zero h'
  obtain ⟨e, u, hle⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have he : 1 ≤ e := by
    by_contra h0
    push Not at h0
    have : e = 0 := by omega
    rw [this, pow_zero, mul_one] at hle
    rw [hle] at hlm
    exact (IsLocalRing.mem_maximalIdeal _).mp hlm u.isUnit
  refine isAdicComplete_of_le _ (Ideal.span {((l : ℕ) : ↥(OL LL))}) e he ?_ ?_
  · rw [hmax, Ideal.span_singleton_pow, hle, Ideal.span_singleton_mul_left_unit u.isUnit]
  · rw [Ideal.span_le]; rintro _ rfl; exact hlm

end Formalism.MainNotions.N.Pv.LocalLengthBound.OLC

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
The claim follows from `expCrit_D D HW F Cm CR CA CB CK hA hL hB fun l _ LL _ => by convert OLC.complete_max LL`.
-/
theorem expCrit_D' (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F)
    (hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL h.2.2) :=
  expCrit_D D HW F Cm CR CA CB CK hA hL hB fun l _ LL _ => by
    convert OLC.complete_max LL

end Formalism.MainNotions.N.Pv.LocalLengthBound
