import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamilyStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyBound

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `h0 : 0 ≤ x ^ i` using `by positivity`.

Establish `: 2 * x ^ i ≤ x ^ (i + 1)` using `by rw [pow_succ]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geom_le (x : ℝ) (hx : 2 ≤ x) (i : ℕ) : ∑ m ∈ Finset.range (i + 1), x ^ m ≤ 2 * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 ≤ x ^ i := by positivity
    have : 2 * x ^ i ≤ x ^ (i + 1) := by rw [pow_succ]; nlinarith
    linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Unfold `Frames.mass`. Use `ENNReal.tsum_le_tsum fun o => ?_` and prove the remaining obligations. Distinguish the cases in `ho : S.IsTerm d o.out ∧ P o.out`. Rewrite using `[if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]`. Rewrite using `[if_neg ho]`.

Conclude with `bot_le`.
-/
theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  unfold Frames.mass
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · rw [if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]
  · rw [if_neg ho]; exact bot_le

/- English proof (translation)
Unfold `Frames.mass`. Rewrite using `[← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`. Use `ENNReal.tsum_le_tsum fun o => ?_` and prove the remaining obligations. Distinguish the cases in `ho : S.IsTerm d o.out ∧ P o.out`. Take `⟨m, hm, hq⟩` from `h _ ho.1 ho.2`.

Rewrite using `[if_pos ho]`. Use `le_trans ?_ (Finset.single_le_sum (f := fun m => if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)` and prove the remaining obligations. Rewrite using `[if_pos ⟨ho.1, hq⟩]`. Rewrite using `[if_neg ho]`. Conclude with `bot_le`.
-/
theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ m ∈ s, Q m Λ) : S.mass d P ≤ ∑ m ∈ s, S.mass d (Q m) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨m, hm, hq⟩ := h _ ho.1 ho.2
    rw [if_pos ho]
    refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)
    rw [if_pos ⟨ho.1, hq⟩]
  · rw [if_neg ho]; exact bot_le

/- English proof (translation)
Unfold `Frames.sumData`. Conclude with `ENNReal.tsum_le_tsum fun o => by gcongr; exact h _`.
-/
theorem sumData_mono (φ ψ : S.Datum → ℝ≥0∞) (h : ∀ d, φ d ≤ ψ d) : S.sumData φ ≤ S.sumData ψ := by
  unfold Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => by gcongr; exact h _

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S hk β J βJ`. Distinguish the cases in `hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ`. Use `swap`. Establish `h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0`. Introduce `d`.

Unfold `Frames.amp`. Establish `: ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out)` using `fun o ho => hex ⟨d, _, ho⟩`. Simplify using `[this]`. Establish `: S.ampSq (S.InFF β J βJ) = 0`. Unfold `Frames.ampSq Frames.sumData`.

Simplify using `[h0]`. Rewrite using `[this]`. Conclude with `bot_le`. Take `⟨d₀, Λ₀, ht, hF⟩` from `hex`. Take `⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩` from `GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht`.

Establish `hβ : β = S.q ^ i` using `by rw [← hF.2.1, hi]`. Establish `hq0 : 0 < S.q` using `GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr`. Establish `hq1 : S.q ≠ 1`. Introduce `h`. Conclude with `hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))`.

Establish `hq : 2 ≤ S.q` using `by omega`. Establish `hβ1 : 1 ≤ β` using `by rw [hβ]; exact Nat.one_le_pow _ _ hq0`. Establish `hk1 : 1 ≤ k` using `by omega`. Use `set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0`. Use `set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1`.

Use `set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he`. Establish `hA0p : 0 ≤ A0` using `by positivity`. Establish `hA1p : 0 ≤ A1` using `by positivity`. Establish `hep : 0 ≤ e` using `by positivity`. Establish `hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1))`.

Introduce `d`. Use `(mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_` and prove the remaining obligations. Introduce `Λ hΛ hP`. Take `⟨⟨m, hm⟩, hle, -⟩` from `GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ`. Use `⟨m, ?_, hm⟩` and prove the remaining obligations.

Rewrite `hle` using `[hm, hP.2.1, hβ]`. Use `(Nat.pow_le_pow_iff_right (by omega)).1 hle` as an intermediate fact. Conclude with `Finset.mem_range.2 (by omega)`. Use `(Finset.sum_le_sum fun m _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1)`. Establish `h2 : (2 : ℝ) ≤ S.q` using `by exact_mod_cast hq`. Conclude with `h2.trans (le_self_pow₀ (by linarith) (by omega))`. Establish `hg` using `geom_le _ hx i`.

Establish `hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m`. Introduce `m`. Use `push_cast`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Rewrite using `[← Finset.mul_sum, hβ]`.

Simplify using `only [hc]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hg hA0p]`. Establish `h1` using `(GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity) hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)`. Establish `h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤ ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn` using `(sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk β hβ1)`. Use `h1.trans ?_` and prove the remaining obligations.

Use `(mul_le_mul_right h2 _).trans ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Establish `hb : (β : ℝ) ^ (k - 1) ≠ 0`. Establish `: (0 : ℝ) < β` using `by exact_mod_cast hβ1`. Check the signs of the components of the expression.

Establish `: (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.
-/
theorem family_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β J βJ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ
  swap
  · have h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0 := by
      intro d
      unfold Frames.amp
      have : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
          ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out) := fun o ho => hex ⟨d, _, ho⟩
      simp [this]
    have : S.ampSq (S.InFF β J βJ) = 0 := by
      unfold Frames.ampSq Frames.sumData
      simp [h0]
    rw [this]; exact bot_le
  obtain ⟨d₀, Λ₀, ht, hF⟩ := hex
  obtain ⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht
  have hβ : β = S.q ^ i := by rw [← hF.2.1, hi]
  have hq0 : 0 < S.q := GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  have hq1 : S.q ≠ 1 := by
    intro h
    exact hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))
  have hq : 2 ≤ S.q := by omega
  have hβ1 : 1 ≤ β := by rw [hβ]; exact Nat.one_le_pow _ _ hq0
  have hk1 : 1 ≤ k := by omega
  set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1
  set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he
  have hA0p : 0 ≤ A0 := by positivity
  have hA1p : 0 ≤ A1 := by positivity
  have hep : 0 ≤ e := by positivity
  have hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1)) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_
    · intro Λ hΛ hP
      obtain ⟨⟨m, hm⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ
      refine ⟨m, ?_, hm⟩
      rw [hm, hP.2.1, hβ] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      exact Finset.mem_range.2 (by omega)
    · refine (Finset.sum_le_sum fun m _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1) := by
        have h2 : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
        exact h2.trans (le_self_pow₀ (by linarith) (by omega))
      have hg := geom_le _ hx i
      have hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m := by
        intro m; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
      rw [← Finset.mul_sum, hβ]
      simp only [hc]
      nlinarith [mul_le_mul_of_nonneg_left hg hA0p]
  have h1 := (GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity)
    hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)
  have h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤
      ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn :=
    (sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk β hβ1)
  refine h1.trans ?_
  refine (mul_le_mul_right h2 _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (β : ℝ) ^ (k - 1) ≠ 0 := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ1
    positivity
  have : (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2 := by
    field_simp
    ring
  rw [this]

end GlobalTheory.HL.FamilyBound
