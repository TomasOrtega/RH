import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruence
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomial
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovGmin.PrismSpan

section Sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `|(laOf Dw a n τ k : ℝ)| ≤ sizeK Dw a n := by unfold sizeK refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Psi H => ∑ k, |(laOf Dw a n τ k : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) exact Finset.single_le_sum (f := fun k => |(laOf Dw …`.
-/
theorem abs_laOf_le_sizeK (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(laOf Dw a n τ k : ℝ)| ≤ sizeK Dw a n := by
  unfold sizeK
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Psi H => ∑ k, |(laOf Dw a n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact Finset.single_le_sum (f := fun k => |(laOf Dw a n τ k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

/- English proof (translation)
Distinguish the cases in `h : τ (H.rt : E) = H.rt0`. Establish `hm : Dw.mult τ = Dw.p` using `by simp [Datum.mult, h]`. Establish `hip : i < Dw.p` using `hm ▸ hi`. Establish `e : laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩ = (a (τ, i) : ℤ) + ((n / 2 : ℕ) : ℤ)`. Simplify using `[laOf, GlobalTheory.AllWt.weightOf, hip]`.

Establish `h1` using `abs_laOf_le_sizeK Dw a n ⟨τ, h⟩ ⟨i, by omega⟩`. Establish `h4 : (a (τ, i) : ℤ) ≤ |laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩|`. Rewrite using `[e]; exact le_trans (by omega) (le_abs_self _)`. Establish `h5 : ((a (τ, i) : ℤ) : ℝ) ≤ ((|laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩| : ℤ) : ℝ)` using `by exact_mod_cast h4`. Rewrite `h5` using `[Int.cast_abs]`.

Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : Dw.mult τ = Dw.q` using `by simp [Datum.mult, h]`. Establish `hiq : i < Dw.q` using `hm ▸ hi`. Establish `hc` using `GlobalTheory.AllWt.conj_mem (H := H) h`.

Establish `hk : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p)` using `by omega`. Establish `e : laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ = -(a (τ, i) : ℤ) - ((n / 2 : ℕ) : ℤ)`. Establish `e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i` using `by omega`. Simplify using `only [laOf, GlobalTheory.AllWt.weightOf, hk, if_false, e2, GlobalTheory.AllWt.conjEmb_conjEmb]`. Establish `h1` using `abs_laOf_le_sizeK Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩`.

Establish `h4 : (a (τ, i) : ℤ) ≤ |laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩|`. Rewrite using `[e]; exact le_trans (by omega) (neg_le_abs _)`. Establish `h5 : ((a (τ, i) : ℤ) : ℝ) ≤ ((|laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩| : ℤ) : ℝ)` using `by exact_mod_cast h4`. Rewrite `h5` using `[Int.cast_abs]`. Move the coercions through the operations in `at h5`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_le_sizeK (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) :
    (a (τ, i) : ℝ) ≤ sizeK Dw a n := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hm : Dw.mult τ = Dw.p := by simp [Datum.mult, h]
    have hip : i < Dw.p := hm ▸ hi
    have e : laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩ = (a (τ, i) : ℤ) + ((n / 2 : ℕ) : ℤ) := by
      simp [laOf, GlobalTheory.AllWt.weightOf, hip]
    have h1 := abs_laOf_le_sizeK Dw a n ⟨τ, h⟩ ⟨i, by omega⟩
    have h4 : (a (τ, i) : ℤ) ≤ |laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩| := by
      rw [e]; exact le_trans (by omega) (le_abs_self _)
    have h5 : ((a (τ, i) : ℤ) : ℝ) ≤ ((|laOf Dw a n ⟨τ, h⟩ ⟨i, by omega⟩| : ℤ) : ℝ) := by exact_mod_cast h4
    rw [Int.cast_abs] at h5
    push_cast at h5
    linarith
  · have hm : Dw.mult τ = Dw.q := by simp [Datum.mult, h]
    have hiq : i < Dw.q := hm ▸ hi
    have hc := GlobalTheory.AllWt.conj_mem (H := H) h
    have hk : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
    have e : laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ =
        -(a (τ, i) : ℤ) - ((n / 2 : ℕ) : ℤ) := by
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, GlobalTheory.AllWt.weightOf, hk, if_false, e2, GlobalTheory.AllWt.conjEmb_conjEmb]
    have h1 := abs_laOf_le_sizeK Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
    have h4 : (a (τ, i) : ℤ) ≤ |laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩| := by
      rw [e]; exact le_trans (by omega) (neg_le_abs _)
    have h5 : ((a (τ, i) : ℤ) : ℝ) ≤
        ((|laOf Dw a n ⟨conjEmb τ, hc⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩| : ℤ) : ℝ) := by exact_mod_cast h4
    rw [Int.cast_abs] at h5
    push_cast at h5
    linarith

/- English proof (translation)
Unfold `DF`. Simplify using `only [Nat.cast_sum]`. Establish `hK` using `sizeK_nonneg Dw a n`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ hK` and prove the remaining obligations. Apply the tactic sequence `have : Dw.mult τ ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega`. Conclude with `this` after adjusting the coercions. Use `_ = Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) : ℝ) * sizeK Dw a n := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card E ℂ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DF_le_sizeK (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (DF Dw a : ℝ) ≤ Module.finrank ℚ E * (Dw.p + Dw.q : ℕ) * sizeK Dw a n := by
  unfold DF
  simp only [Nat.cast_sum]
  have hK := sizeK_nonneg Dw a n
  calc ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, (i : ℕ)) : ℝ)
      ≤ ∑ τ : E →+* ℂ, ((Dw.p + Dw.q : ℕ) : ℝ) * sizeK Dw a n := by
        refine Finset.sum_le_sum fun τ _ => ?_
        calc ∑ i : Fin (Dw.mult τ), (a (τ, (i : ℕ)) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), sizeK Dw a n :=
              Finset.sum_le_sum fun i _ => exp_le_sizeK Dw a n τ i i.2
          _ = (Dw.mult τ : ℝ) * sizeK Dw a n := by simp
          _ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) * sizeK Dw a n := by
              refine mul_le_mul_of_nonneg_right ?_ hK
              have : Dw.mult τ ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
              exact_mod_cast this
    _ = Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) : ℝ) * sizeK Dw a n := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card E ℂ, nsmul_eq_mul]
        ring

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by`. Distinguish the cases in `h : φ (H.rt : E) = H.rt0`. Conclude with `⟨φ, h⟩`. Conclude with `⟨conjEmb φ, GlobalTheory.AllWt.conj_mem h⟩`.

Establish `h0` using `hpos ⟨τ, hτ⟩ ⟨0, by omega⟩ (by simp; omega)`. Establish `h1` using `abs_laOf_le_sizeK Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩`. Establish `h0' : ((n / 2 : ℕ) : ℤ) + 1 ≤ laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩` using `h0`. Establish `h2 : ((n / 2 : ℕ) : ℝ) + 1 ≤ (laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩ : ℝ)`. Use `(Int.cast_le (R := ℝ)).2 h0'` as an intermediate fact.

Rewrite `this` using `[Int.cast_add, Int.cast_natCast, Int.cast_one]`. Then use the resulting hypothesis. Establish `h3` using `le_abs_self (laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩ : ℝ)`. Take `⟨m, hm⟩` from `hev`. Establish `hn2 : n / 2 = m` using `by omega`. Rewrite `h2` using `[hn2]`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `hnm : (n : ℝ) = m + m` using `by exact_mod_cast hm`. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Rewrite using `[hnm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_sizeK (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hp : 1 ≤ Dw.p) (hev : Even n)
    (hpos : ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) < laOf Dw a n τ k) :
    1 ≤ sizeK Dw a n ∧ (n : ℝ) ≤ 2 * sizeK Dw a n := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    by_cases h : φ (H.rt : E) = H.rt0
    · exact ⟨φ, h⟩
    · exact ⟨conjEmb φ, GlobalTheory.AllWt.conj_mem h⟩
  have h0 := hpos ⟨τ, hτ⟩ ⟨0, by omega⟩ (by simp; omega)
  have h1 := abs_laOf_le_sizeK Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩
  have h0' : ((n / 2 : ℕ) : ℤ) + 1 ≤ laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩ := h0
  have h2 : ((n / 2 : ℕ) : ℝ) + 1 ≤ (laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩ : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 h0'
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_one] at this
  have h3 := le_abs_self (laOf Dw a n ⟨τ, hτ⟩ ⟨0, by omega⟩ : ℝ)
  obtain ⟨m, hm⟩ := hev
  have hn2 : n / 2 = m := by omega
  rw [hn2] at h2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnm : (n : ℝ) = m + m := by exact_mod_cast hm
  refine ⟨by linarith, ?_⟩
  rw [hnm]
  linarith

end Sizes

end GlobalTheory.CovGmin.PrismSpan

namespace GlobalTheory.CovGmin.PrismSpan

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm`. Rewrite using `[← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg _)]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations. Establish `hs : ∀ s : c.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ^ 2 ≤ B ^ 2`. Introduce `s`.

Use `set S := ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ with hSdef`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun m hm => ?_` and prove the remaining obligations. Rewrite using `[sq]`.

Conclude with `mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun m => ‖s (Q.coeff m)‖) (fun _ _ => norm_nonneg _) hm) (norm_nonneg _)`. Use `_ = S * S := by rw [← Finset.sum_mul]`. Use `_ ≤ B * B := mul_le_mul (h s) (h s) hS0 hB`. Use `_ = B ^ 2 := (sq B).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card c.F ℂ, nsmul_eq_mul]`.
-/
theorem polynomialCoefficientEmbeddingNorm_le_of_l1Bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Q : MvPolynomial (LtN Dw n) c.F) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ s : c.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ≤ B) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm c Q ≤ Real.sqrt (Module.finrank ℚ c.F) * B := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have hs : ∀ s : c.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ^ 2 ≤ B ^ 2 := by
    intro s
    set S := ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ^ 2 ≤ ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ * S := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun m => ‖s (Q.coeff m)‖) (fun _ _ => norm_nonneg _) hm) (norm_nonneg _)
      _ = S * S := by rw [← Finset.sum_mul]
      _ ≤ B * B := mul_le_mul (h s) (h s) hS0 hB
      _ = B ^ 2 := (sq B).symm
  calc ∑ s : c.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ^ 2 ≤ ∑ _s : c.F →+* ℂ, B ^ 2 := Finset.sum_le_sum fun s _ => hs s
    _ = (Module.finrank ℚ c.F : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card c.F ℂ, nsmul_eq_mul]

/- English proof (translation)
Break down `hx.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `(Real.exp_pos t).le`. Rewrite using `[← Real.exp_log h0]`. Conclude with `Real.exp_le_exp.2 h`.
-/
theorem le_exp_of_log_le {x t : ℝ} (hx : 0 ≤ x) (h : Real.log x ≤ t) : x ≤ Real.exp t := by
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos t).le
  · rw [← Real.exp_log h0]; exact Real.exp_le_exp.2 h

end GlobalTheory.CovGmin.PrismSpan

noncomputable section

namespace GlobalTheory.CovGmin.PrismSpan

open Formalism.L2.PjFree (Unf.ofPj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Establish `hC` using `GlobalTheory.chartIndependence_unconditional`. Establish `hL : Out.Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hB : Out.SecBaseChangeSt` using `hL.secBaseChange`. Establish `hpin` using `GlobalTheory.DeltaPinTest.noDelta_phiPin (n := m) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)`. Establish `hT` using `GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c`.

Establish `hW` using `(GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1`. Use `⟨RawSpan.idCover_isLev nab m, ⟨_, hnab⟩, RawSpan.idCover_unitC nab m, by show ¬ 3 ∣ 1; decide, fun _ => ⟨_, 1, _, hpin⟩, fun a _ => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c m (RawSpan.idCover nab m) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT (RawSpan.idCover_isLev nab m) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, RawSpan.idCover_psiTie nab m⟩) nab bad nV a`.
-/
theorem idCover_laws [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (bad nV : ℕ) (h1 : 1 ≤ Dw.p + Dw.q)
    (m : ℕ) : (RawSpan.idCover nab m).IsLev ∧
      (∃ _ : StarRing (𝓞 E), IsNab (RawSpan.idCover nab m).Xo₂ (RawSpan.idCover nab m).c₂ (RawSpan.idCover nab m).nab₂) ∧
      GlobalTheory.Dict.UnitC (RawSpan.idCover nab m) ∧ ¬ 3 ∣ (RawSpan.idCover nab m).pd ∧
      (Dw.p + Dw.q ≤ m → ∃ ph ψ x₀, (RawSpan.idCover nab m).PhiPin ph ψ x₀) ∧
      ∀ a, Dom a m → ShortValTot Xo c nab bad nV a m (RawSpan.idCover nab m) := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hpin := GlobalTheory.DeltaPinTest.noDelta_phiPin (n := m) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)
  have hT := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1
  refine ⟨RawSpan.idCover_isLev nab m, ⟨_, hnab⟩, RawSpan.idCover_unitC nab m, by show ¬ 3 ∣ 1; decide,
    fun _ => ⟨_, 1, _, hpin⟩, fun a _ => ?_⟩
  exact GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c m (RawSpan.idCover nab m) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT
      (RawSpan.idCover_isLev nab m) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, RawSpan.idCover_psiTie nab m⟩) nab bad nV a

/- English proof (translation)
Establish `h1 : 1 ≤ Dw.p + Dw.q` using `(hU σ₀ hσ₀).1 ▸ hr`. Conclude with `GlobalTheory.cusp_le_span_shortGen GlobalTheory.chartIndependence_unconditional E H Dw l Xo c r (fun σ => Unf.ofPj (U σ)) σ₀ hσ₀ (hU σ₀ hσ₀) hr hA hG hP hχ nab bad n (fun m => RawSpan.idCover nab m) hbad (fun m => idCover_laws nab hnab bad n h1 m) a n hD hLP hn`.
-/
theorem cusp_sub_span {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ₀ : c.F →+* ℂ) (hσ₀ : GoodEmb c σ₀)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hr : 1 ≤ r) (hA : l.A = 1)
    (hG : ∀ k k', ((U σ₀).X k).Gm = ((U σ₀).X k').Gm ∧ ((U σ₀).X k).ξ0 = ((U σ₀).X k').ξ0)
    (hP : ∀ k, GlobalTheory.Dict.HasPrinc ((U σ₀).X k) l.M)
    (hχ : ∀ a n, Dom a n → ∀ k, GlobalTheory.Dict.ChiOne ((U σ₀).X k) (laU (U σ₀) a n k))
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (bad : ℕ) (hbad : 0 < bad)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hLP : LastPos Dw a)
    (hn : 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n) :
    (cusp Xo c U a n : Set (Rul Xo c)) ⊆
      Submodule.span c.F (shortGen Xo c nab bad n a n (RawSpan.idCover nab n)) := by
  have h1 : 1 ≤ Dw.p + Dw.q := (hU σ₀ hσ₀).1 ▸ hr
  exact GlobalTheory.cusp_le_span_shortGen GlobalTheory.chartIndependence_unconditional E H Dw l Xo c r (fun σ => Unf.ofPj (U σ)) σ₀
    hσ₀ (hU σ₀ hσ₀) hr hA hG hP hχ nab bad n (fun m => RawSpan.idCover nab m) hbad
    (fun m => idCover_laws nab hnab bad n h1 m) a n hD hLP hn

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hC` using `GlobalTheory.chartIndependence_unconditional`. Establish `h1 : 1 ≤ Dw.p + Dw.q` using `(hU σ₀ hσ₀).1 ▸ hr`. Establish `hlaws` using `idCover_laws nab hnab bad n h1 n`. Introduce `f hf`. Use `Submodule.span_le.2 ?_ (cusp_sub_span U σ₀ hσ₀ hU hr hA hG hP hχ nab hnab bad hbad a n hD hLP hn hf)` and prove the remaining obligations.

Introduce and unpack `g ⟨hgs, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩`. Take `⟨m, cf, Q, hsum⟩` from `Submodule.mem_span_set'.1 (hshort Λ hΛ hb P hPm)`. Use `choose gs hgs1 hgs2 using fun i => (hlaws.2.2.2.2.2 a hD Λ N x0 (Q i).1 hΛ hb hM hO hX (Q i).2.1).2`. Establish `hlin` using `GlobalTheory.ShortRuleLinear.eq_sum_of_isShortRule hC Xo c (RawSpan.idCover nab n) (RawSpan.idCover_isLev nab n) hnab a Λ N x0 hΛ hM hO m cf (fun i => (Q i).1) g gs (fun i => (Q i).2.1) hgs hgs1 (by rw [hsum]; exact hrule) hgs2`. Establish `hX'` using `hX`.

Rewrite `hX'` using `[decide_eq_true (rfl : n = n)]`. Establish `hcusp` using `GlobalTheory.Dict.shortInCusp_cusp hC E H Dw l Xo c n (RawSpan.idCover nab n) r (fun σ => Unf.ofPj (U σ)) hr hU hlaws.1 hlaws.2.1 hlaws.2.2.1 hlaws.2.2.2.2.1 nab bad n a hD hLP`. Rewrite using `[hlin]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hβ` using `RawSpan.betaH_ne_zero (Dw := Dw) (c := c) Λ`.

Establish `hmem : betaH (Dw` using `Dw) c Λ • gs i ∈ {f | f ∈ cusp Xo c U a n ∧ ∃ (x0 : Fin n → LevQc Dw l) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), Submodule.span (𝓞 E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ GlobalTheory.IndefiniteRo …`. Use `⟨Submodule.smul_mem _ _ (hcusp ⟨hgs1 i, Λ, N, x0, (Q i).1, hΛ, hb, hM, hO, hX, (Q i).2.1, hgs2 i⟩), fun b => Submodule.Quotient.mk (x0 b), Λ, N, (Q i).1, RawSpan.span_mk_eq_top x0 hX', hΛ, hb, hM, hO, (Q i).2.1, (Q i).2.2, fun p y => ?_⟩` and prove the remaining obligations. Rewrite using `[RawSpan.phiHat_indPhi_mk]`. Conclude with `RawSpan.thLaValAt_of_isShortRule nab hnab hΛ hM hO (Q i).2.1 x0 (hgs1 i) (hgs2 i) p y`. Establish `e : gs i = (betaH (Dw` using `Dw) c Λ)⁻¹ • (betaH (Dw := Dw) c Λ • gs i) := by`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hβ, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem cusp_sub_span_short {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ₀ : c.F →+* ℂ) (hσ₀ : GoodEmb c σ₀)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hr : 1 ≤ r) (hA : l.A = 1)
    (hG : ∀ k k', ((U σ₀).X k).Gm = ((U σ₀).X k').Gm ∧ ((U σ₀).X k).ξ0 = ((U σ₀).X k').ξ0)
    (hP : ∀ k, GlobalTheory.Dict.HasPrinc ((U σ₀).X k) l.M)
    (hχ : ∀ a n, Dom a n → ∀ k, GlobalTheory.Dict.ChiOne ((U σ₀).X k) (laU (U σ₀) a n k))
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (bad : ℕ) (hbad : 0 < bad)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hLP : LastPos Dw a)
    (hn : 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n) (ρ : ℝ)
    (hshort : ∀ Λ : GenLat E n, Λ.Unimod → Λ.TrivAt bad → ∀ P ∈ harmL (Dw := Dw) c Λ a,
      P ∈ Submodule.span c.F {Q | Q ∈ harmL (Dw := Dw) c Λ a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm c Q ≤ ρ}) :
    (cusp Xo c U a n : Set (Rul Xo c)) ⊆ Submodule.span c.F {f | f ∈ cusp Xo c U a n ∧
      ∃ (x0 : Fin n → LevQc Dw l) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F),
        Submodule.span (𝓞 E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧
          La.LevOK N l.M ∧ P ∈ harmL c La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm c P ≤ ρ ∧
          ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have h1 : 1 ≤ Dw.p + Dw.q := (hU σ₀ hσ₀).1 ▸ hr
  have hlaws := idCover_laws nab hnab bad n h1 n
  intro f hf
  refine Submodule.span_le.2 ?_ (cusp_sub_span U σ₀ hσ₀ hU hr hA hG hP hχ nab hnab bad hbad a n hD hLP hn hf)
  rintro g ⟨hgs, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hshort Λ hΛ hb P hPm)
  choose gs hgs1 hgs2 using fun i =>
    (hlaws.2.2.2.2.2 a hD Λ N x0 (Q i).1 hΛ hb hM hO hX (Q i).2.1).2
  have hlin := GlobalTheory.ShortRuleLinear.eq_sum_of_isShortRule hC Xo c (RawSpan.idCover nab n)
    (RawSpan.idCover_isLev nab n) hnab a Λ N x0 hΛ hM hO m cf (fun i => (Q i).1) g gs (fun i => (Q i).2.1) hgs hgs1
    (by rw [hsum]; exact hrule) hgs2
  have hX' := hX
  rw [decide_eq_true (rfl : n = n)] at hX'
  have hcusp := GlobalTheory.Dict.shortInCusp_cusp hC E H Dw l Xo c n (RawSpan.idCover nab n) r (fun σ => Unf.ofPj (U σ)) hr hU
    hlaws.1 hlaws.2.1 hlaws.2.2.1 hlaws.2.2.2.2.1 nab bad n a hD hLP
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hβ := RawSpan.betaH_ne_zero (Dw := Dw) (c := c) Λ
  have hmem : betaH (Dw := Dw) c Λ • gs i ∈ {f | f ∈ cusp Xo c U a n ∧
      ∃ (x0 : Fin n → LevQc Dw l) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F),
        Submodule.span (𝓞 E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧
          La.LevOK N l.M ∧ P ∈ harmL c La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm c P ≤ ρ ∧
          ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} := by
    refine ⟨Submodule.smul_mem _ _ (hcusp ⟨hgs1 i, Λ, N, x0, (Q i).1, hΛ, hb, hM, hO, hX, (Q i).2.1, hgs2 i⟩),
      fun b => Submodule.Quotient.mk (x0 b), Λ, N, (Q i).1, RawSpan.span_mk_eq_top x0 hX', hΛ, hb, hM, hO, (Q i).2.1,
      (Q i).2.2, fun p y => ?_⟩
    rw [RawSpan.phiHat_indPhi_mk]
    exact RawSpan.thLaValAt_of_isShortRule nab hnab hΛ hM hO (Q i).2.1 x0 (hgs1 i) (hgs2 i) p y
  have e : gs i = (betaH (Dw := Dw) c Λ)⁻¹ • (betaH (Dw := Dw) c Λ • gs i) := by
    rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.CovGmin.PrismSpan

namespace GlobalTheory.CovGmin.PrismSpan

/- English proof (translation)
Take `⟨k, hk, hle, -⟩` from `h`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hk` using `[Nat.coprime_zero_left]`. Use linear arithmetic over natural numbers and integers.

Establish `hstd : (stdLat E n).FG`. Unfold `stdLat`. Conclude with `Submodule.fg_pi fun _ => Submodule.fg_unit 1`. Establish `hkO : (k : 𝓞 E) ≠ 0` using `by exact_mod_cast hk0`. Establish `hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E))` using `LinearMap.lsmul_injective hkO`.

Use `Submodule.fg_of_fg_map_injective _ hinj ?_` and prove the remaining obligations. Establish `hN` using `isNoetherian_of_fg_of_noetherian _ hstd`. Use `isNoetherian_submodule.1 hN _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)`.
-/
theorem fg_of_trivAt_two {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

/- English proof (translation)
Establish `hF0 : 0 ≤ F` using `by linarith`. Establish `hR0 : 0 ≤ R` using `by linarith`. Establish `hLb0 : 0 ≤ Lb` using `by linarith`. Establish `hK0 : 0 ≤ K` using `by linarith`. Establish `h0 : 0 ≤ F * R * R * Lb` using `by positivity`.

Establish `hXX : F * R * R * Lb ≤ (F * R * Lb) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `t1 : 140 * R * L * DFr ≤ 140 * R * (50 * Lb) * (2 * F * R * K)`. Establish `hR0' : 0 ≤ 140 * R` using `by positivity`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left hLb hR0') hDF hDF0 (by positivity)`.

Establish `t3 : 140 * R * (50 * Lb) * (2 * F * R * K) ≤ 14000 * ((F * R * Lb) ^ 2 * K)`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : 0 ≤ (F * R * Lb) ^ 2` using `sq_nonneg _`. Establish `h2 : (F * R * Lb) ^ 2 ≤ (F * R * Lb) ^ 2 * K` using `le_mul_of_one_le_right h1 hK1`. Establish `e : 20000 * (F * R * Lb) ^ 2 * K = 20000 * ((F * R * Lb) ^ 2 * K)` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponent_le (o L Lb K F R DFr : ℝ) (hF1 : 1 ≤ F) (hR1 : 1 ≤ R) (hL1 : 1 ≤ Lb) (hK1 : 1 ≤ K)
    (hLb : L ≤ 50 * Lb) (hL0 : 0 ≤ L) (hDF0 : 0 ≤ DFr) (hDF : DFr ≤ 2 * F * R * K)
    (ho : o ≤ 391 * (F * R * Lb) ^ 2) : o / 2 + 140 * R * L * DFr ≤ 20000 * (F * R * Lb) ^ 2 * K := by
  have hF0 : 0 ≤ F := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hLb0 : 0 ≤ Lb := by linarith
  have hK0 : 0 ≤ K := by linarith
  have h0 : 0 ≤ F * R * R * Lb := by positivity
  have hXX : F * R * R * Lb ≤ (F * R * Lb) ^ 2 := by
    calc F * R * R * Lb = (F * R * R * Lb) * 1 * 1 := by ring
      _ ≤ (F * R * R * Lb) * F * Lb := mul_le_mul (mul_le_mul_of_nonneg_left hF1 h0) hL1 zero_le_one (by positivity)
      _ = (F * R * Lb) ^ 2 := by ring
  have t1 : 140 * R * L * DFr ≤ 140 * R * (50 * Lb) * (2 * F * R * K) := by
    have hR0' : 0 ≤ 140 * R := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hLb hR0') hDF hDF0 (by positivity)
  have t3 : 140 * R * (50 * Lb) * (2 * F * R * K) ≤ 14000 * ((F * R * Lb) ^ 2 * K) := by
    calc 140 * R * (50 * Lb) * (2 * F * R * K) = 14000 * ((F * R * R * Lb) * K) := by ring
      _ ≤ 14000 * ((F * R * Lb) ^ 2 * K) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXX hK0) (by norm_num)
  have h1 : 0 ≤ (F * R * Lb) ^ 2 := sq_nonneg _
  have h2 : (F * R * Lb) ^ 2 ≤ (F * R * Lb) ^ 2 * K := le_mul_of_one_le_right h1 hK1
  have e : 20000 * (F * R * Lb) ^ 2 * K = 20000 * ((F * R * Lb) ^ 2 * K) := by ring
  rw [e]
  linarith

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T j Y e o Lb a n hH Λ hΛ hb P hP`. Take `⟨hJ, hp, hq, hE, hj, hG, hL1, hM, hfs, hfr, ho, hD, hev, hn, hpos, hκ⟩` from `hH`. Establish `hU0` using `hG.unf _ (rfl : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom)`. Establish `hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r` using `hU0.1.symm`. Establish `hf1 : 1 ≤ D.R.f` using `MeanTop.Inhab.f_pos D`.

Establish `hfg : Λ.La.FG` using `fg_of_trivAt_two Λ (by`. Unfold `badC`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right (((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd).mul_right _) _) _) hb`. Establish `hrn : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n`. Establish `h1 : D.R.r ≤ D.R.f * D.R.r` using `Nat.le_mul_of_pos_left _ hf1`.

Establish `h8 : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r)` using `by ring`. Use linear arithmetic over natural numbers and integers. Take `⟨hK1, hKn⟩` from `one_le_sizeK (T.Q.Dw j) a n hp hev hpos`. Establish `hDF` using `DF_le_sizeK (T.Q.Dw j) a n`. Use `set K := sizeK (T.Q.Dw j) a n with hKdef`.

Establish `hdegE : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f` using `by exact_mod_cast StandardLattice.finrank_host D`. Establish `hrR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r` using `by exact_mod_cast hr`. Rewrite `hDF` using `[hdegE, hrR]`. Establish `hF1 : (1 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast hf1`. Establish `hR1 : (1 : ℝ) ≤ (D.R.r : ℝ)`.

Establish `: 1 ≤ D.R.r` using `by omega`. Conclude with `this` after adjusting the coercions. Use `set L : ℝ := 2 + 3 * Lb + Real.log (1 + DF (T.Q.Dw j) a) + Real.log n with hLdef`. Establish `hl1 : 0 ≤ Real.log (1 + (DF (T.Q.Dw j) a : ℝ))` using `Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (DF (T.Q.Dw j) a); linarith)`. Establish `hl2 : 0 ≤ Real.log (n : ℝ)` using `Real.log_natCast_nonneg n`.

Establish `hrd : Real.log (FD.rdE D.host.E) ≤ 2 * L`. Establish `hd : 0 < FD.dE D.host.E`. Unfold `FD.dE`. Conclude with `abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)`. Establish `h1 : Real.log (FD.rdE D.host.E) = Real.log |(NumberField.discr D.host.E : ℝ)| / (Module.finrank ℚ D.host.E : ℝ)`.

Unfold `FD.rdE`. Rewrite using `[Real.log_rpow hd]`. Unfold `FD.dE`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `log_rd_le_fieldSz D.host.E`.

Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfd : Real.log (FD.fdeg D.host.E : ℝ) ≤ 2 * L`. Establish `h0 : (0 : ℝ) < FD.fdeg D.host.E`. Establish `: 0 < FD.fdeg D.host.E` using `by unfold FD.fdeg; omega`.

Conclude with `this` after adjusting the coercions. Establish `h1 : (FD.fdeg D.host.E : ℝ) ≤ Module.finrank ℚ D.host.E`. Establish `: FD.fdeg D.host.E ≤ Module.finrank ℚ D.host.E` using `by unfold FD.fdeg; omega`. Conclude with `this` after adjusting the coercions. Establish `h2` using `(Real.log_le_log h0 h1).trans (log_finrank_le_fieldSz D.host.E)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdf : Real.log (1 + (DF (T.Q.Dw j) a : ℝ)) ≤ 2 * L` using `by linarith`. Establish `hln : Real.log (n : ℝ) ≤ L` using `by linarith`. Establish `hL2 : 2 ≤ L` using `by linarith`. Take `⟨S, hS1, hS2, -⟩` from `GlobalTheory.Harm.exists_short_harmL_family D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n Λ hΛ hfg hrn a L hL2 hrd hfd hdf hln`.

Use `Submodule.span_mono ?_ (hS2 P hP.1)` and prove the remaining obligations. Introduce `Q hQS`. Take `⟨hQh, hQb⟩` from `hS1 Q hQS`. Use `⟨hQh, ?_⟩` and prove the remaining obligations. Rewrite `hQb` using `[hrR]`.

Establish `hKpos : 0 < K` using `by linarith`. Establish `hFR : 1 ≤ (D.R.f : ℝ) * D.R.r` using `one_le_mul_of_one_le_of_one_le hF1 hR1`. Establish `hFRK : 1 ≤ (D.R.f : ℝ) * D.R.r * K` using `one_le_mul_of_one_le_of_one_le hFR hK1`. Establish `hlog1 : Real.log (1 + (DF (T.Q.Dw j) a : ℝ)) ≤ 3 + 21 * Lb`. Establish `h1 : 1 + (DF (T.Q.Dw j) a : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * K` using `by linarith`.

Establish `h2 : 0 < 1 + (DF (T.Q.Dw j) a : ℝ)` using `by linarith`. Establish `h3` using `Real.log_le_log h2 h1`. Rewrite `h3` using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]`. Establish `h4 : Real.log 4 ≤ 3`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith` as an intermediate fact.

Establish `h5 : Real.log ((D.R.f : ℝ) * D.R.r) ≤ Lb` using `hfr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog2 : Real.log (n : ℝ) ≤ 1 + 20 * Lb`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (0 : ℝ) < n` using `by exact_mod_cast h0`. Establish `h3` using `Real.log_le_log h1 hKn`. Rewrite `h3` using `[Real.log_mul (by norm_num) (by positivity)]`.

Establish `h4 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLb : L ≤ 50 * Lb` using `by linarith`. Establish `hL0 : 0 ≤ L` using `by linarith`.

Establish `hB : ∀ s : Y.d.c₂.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ≤ Real.exp (140 * (D.R.r : ℝ) * L * (DF (T.Q.Dw j) a : ℝ))` using `fun s => le_exp_of_log_le (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hQb s)`. Establish `hpn` using `polynomialCoefficientEmbeddingNorm_le_of_l1Bound Y.d.c₂ Q _ (Real.exp_pos _).le hB`. Establish `hsq : Real.sqrt (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ Real.exp (o / 2)`. Establish `h0 : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F` using `by exact_mod_cast Module.finrank_pos`. Establish `h1 : (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ Real.exp (o / 2) ^ 2`.

Rewrite using `[← Real.exp_nat_mul]`. Use `push_cast`. Rewrite using `[show (2 : ℝ) * (o / 2) = o by ring]`. Conclude with `le_exp_of_log_le h0.le hG.deg`. Combine the equalities or inequalities in the displayed calculation.

Use `hpn.trans ?_` and prove the remaining obligations. Use `(mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le).trans ?_` and prove the remaining obligations. Rewrite using `[← Real.exp_add]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Conclude with `exponent_le o L Lb K _ _ _ hF1 hR1 hL1 hK1 hLb hL0 (Nat.cast_nonneg _) hDF ho`.
-/
theorem harm_short : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ (Λ : GenLat D.host.E n),
    Λ.Unimod → Λ.TrivAt (badC Y) → ∀ P ∈ harmL (Dw := T.Q.Dw j) Y.d.c₂ Λ a,
      P ∈ Submodule.span Y.d.c₂.F {Q | Q ∈ harmL (Dw := T.Q.Dw j) Y.d.c₂ Λ a ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ Q ≤ Real.exp (20000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)} := by
  intro D T j Y e o Lb a n hH Λ hΛ hb P hP
  obtain ⟨hJ, hp, hq, hE, hj, hG, hL1, hM, hfs, hfr, ho, hD, hev, hn, hpos, hκ⟩ := hH
  have hU0 := hG.unf _ (rfl : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom)
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := hU0.1.symm
  have hf1 : 1 ≤ D.R.f := MeanTop.Inhab.f_pos D
  have hfg : Λ.La.FG := fg_of_trivAt_two Λ (by
    unfold badC
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd).mul_right _) _) _) hb
  have hrn : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h1 : D.R.r ≤ D.R.f * D.R.r := Nat.le_mul_of_pos_left _ hf1
    have h8 : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r) := by ring
    omega
  obtain ⟨hK1, hKn⟩ := one_le_sizeK (T.Q.Dw j) a n hp hev hpos
  have hDF := DF_le_sizeK (T.Q.Dw j) a n
  set K := sizeK (T.Q.Dw j) a n with hKdef
  have hdegE : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast StandardLattice.finrank_host D
  have hrR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r := by exact_mod_cast hr
  rw [hdegE, hrR] at hDF
  have hF1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hR1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have : 1 ≤ D.R.r := by omega
    exact_mod_cast this
  set L : ℝ := 2 + 3 * Lb + Real.log (1 + DF (T.Q.Dw j) a) + Real.log n with hLdef
  have hl1 : 0 ≤ Real.log (1 + (DF (T.Q.Dw j) a : ℝ)) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (DF (T.Q.Dw j) a); linarith)
  have hl2 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hrd : Real.log (FD.rdE D.host.E) ≤ 2 * L := by
    have hd : 0 < FD.dE D.host.E := by
      unfold FD.dE
      exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have h1 : Real.log (FD.rdE D.host.E) =
        Real.log |(NumberField.discr D.host.E : ℝ)| / (Module.finrank ℚ D.host.E : ℝ) := by
      unfold FD.rdE
      rw [Real.log_rpow hd]
      unfold FD.dE
      ring
    have h2 := log_rd_le_fieldSz D.host.E
    rw [h1]
    linarith
  have hfd : Real.log (FD.fdeg D.host.E : ℝ) ≤ 2 * L := by
    have h0 : (0 : ℝ) < FD.fdeg D.host.E := by
      have : 0 < FD.fdeg D.host.E := by unfold FD.fdeg; omega
      exact_mod_cast this
    have h1 : (FD.fdeg D.host.E : ℝ) ≤ Module.finrank ℚ D.host.E := by
      have : FD.fdeg D.host.E ≤ Module.finrank ℚ D.host.E := by unfold FD.fdeg; omega
      exact_mod_cast this
    have h2 := (Real.log_le_log h0 h1).trans (log_finrank_le_fieldSz D.host.E)
    linarith
  have hdf : Real.log (1 + (DF (T.Q.Dw j) a : ℝ)) ≤ 2 * L := by linarith
  have hln : Real.log (n : ℝ) ≤ L := by linarith
  have hL2 : 2 ≤ L := by linarith
  obtain ⟨S, hS1, hS2, -⟩ := GlobalTheory.Harm.exists_short_harmL_family D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n Λ hΛ hfg hrn
    a L hL2 hrd hfd hdf hln
  refine Submodule.span_mono ?_ (hS2 P hP.1)
  intro Q hQS
  obtain ⟨hQh, hQb⟩ := hS1 Q hQS
  refine ⟨hQh, ?_⟩
  rw [hrR] at hQb

  have hKpos : 0 < K := by linarith
  have hFR : 1 ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hF1 hR1
  have hFRK : 1 ≤ (D.R.f : ℝ) * D.R.r * K := one_le_mul_of_one_le_of_one_le hFR hK1
  have hlog1 : Real.log (1 + (DF (T.Q.Dw j) a : ℝ)) ≤ 3 + 21 * Lb := by
    have h1 : 1 + (DF (T.Q.Dw j) a : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * K := by linarith
    have h2 : 0 < 1 + (DF (T.Q.Dw j) a : ℝ) := by linarith
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)] at h3
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have h5 : Real.log ((D.R.f : ℝ) * D.R.r) ≤ Lb := hfr
    linarith
  have hlog2 : Real.log (n : ℝ) ≤ 1 + 20 * Lb := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; simp; linarith
    · have h1 : (0 : ℝ) < n := by exact_mod_cast h0
      have h3 := Real.log_le_log h1 hKn
      rw [Real.log_mul (by norm_num) (by positivity)] at h3
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith
  have hLb : L ≤ 50 * Lb := by linarith
  have hL0 : 0 ≤ L := by linarith

  have hB : ∀ s : Y.d.c₂.F →+* ℂ, ∑ m ∈ Q.support, ‖s (Q.coeff m)‖ ≤
      Real.exp (140 * (D.R.r : ℝ) * L * (DF (T.Q.Dw j) a : ℝ)) := fun s =>
    le_exp_of_log_le (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hQb s)
  have hpn := polynomialCoefficientEmbeddingNorm_le_of_l1Bound Y.d.c₂ Q _ (Real.exp_pos _).le hB
  have hsq : Real.sqrt (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ Real.exp (o / 2) := by
    have h0 : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
    have h1 : (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ Real.exp (o / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (o / 2) = o by ring]
      exact le_exp_of_log_le h0.le hG.deg
    calc Real.sqrt (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ Real.sqrt (Real.exp (o / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.exp (o / 2) := Real.sqrt_sq (Real.exp_pos _).le
  refine hpn.trans ?_
  refine (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  exact exponent_le o L Lb K _ _ _ hF1 hR1 hL1 hK1 hLb hL0 (Nat.cast_nonneg _) hDF ho

end GlobalTheory.CovGmin.PrismSpan

open GlobalTheory.CovGmin.PrismSpan in

/- English proof (translation)
Use `⟨20000, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `D T j Y e o Lb a n hH _ nab hnab`. Establish `hH'` using `hH`. Take `⟨hJ, hp, hq, hE, hj, hG, hL1, hM, hfs, hfr, ho, hD, hev, hn, hpos, hκ⟩` from `hH'`. Use `set σ₀ : Y.d.c₂.F →+* ℂ := Y.d.c₂.F.val.toRingHom with hσ₀def`.

Establish `hσ₀ : GoodEmb Y.d.c₂ σ₀` using `rfl`. Establish `hU0` using `hG.unf σ₀ hσ₀`. Establish `hr : 1 ≤ D.R.r` using `by have := hU0.1; omega`. Take `⟨hrk, hmod⟩` from `hG.modelW σ₀ hσ₀`. Establish `hGm : ∀ k k', ((Y.U σ₀).X k).Gm = ((Y.U σ₀).X k').Gm ∧ ((Y.U σ₀).X k).ξ0 = ((Y.U σ₀).X k').ξ0` using `fun k k' => ⟨(hmod k).1.trans (hmod k').1.symm, (hmod k).2.trans (hmod k').2.symm⟩`.

Establish `hlaws` using `(GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).1`. Establish `hPr` using `GlobalTheory.LevGeo.hasPrinc_laws D j _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hlaws σ₀ hσ₀`. Establish `hP : ∀ k, GlobalTheory.Dict.HasPrinc ((Y.U σ₀).X k) Y.d.l₂.M` using `fun k ga hst hc => hPr k ga hst fun v hv => by`. Take `⟨u, hu, e⟩` from `hc v hv`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, add_sub_cancel_left]`. Use `first`. Consider the case `rfl`. Consider the case `exact (Nat.cast_smul_eq_nsmul _ _ _).symm`. Consider the case `simp`.

Establish `hχ : ∀ a n, Dom a n → ∀ k, GlobalTheory.Dict.ChiOne ((Y.U σ₀).X k) (laU (Y.U σ₀) a n k)` using `fun a n hd k ga hga => hG.chiTriv σ₀ hσ₀ a n hd k ga hga`. Establish `hbad : 0 < badC Y`. Establish `h1` using `D.host.qd_big.1`. Establish `h2` using `d_pos D`. Establish `h3` using `Y.d.l₂.three_le`.

Establish `hq0 : 0 < D.host.q` using `by omega`. Establish `hM0 : 0 < Y.d.l₂.M` using `by omega`. Unfold `badC`. Conclude with `Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos hq0) h2) hM0`. Establish `hLP : LastPos (T.Q.Dw j) a`.

Introduce `τ hτ hm`. Establish `hτ' : τ ↑T.Q.H.rt = T.Q.H.rt0` using `hτ`. Establish `hmp : (T.Q.Dw j).mult τ = (T.Q.Dw j).p` using `by simp [Datum.mult, hτ']`. Use `hpos ⟨τ, hτ⟩ ⟨(T.Q.Dw j).p - 1, by omega⟩ (by simp; omega)` as an intermediate fact. Simplify using `only [laOf, GlobalTheory.AllWt.weightOf, show (T.Q.Dw j).p - 1 < (T.Q.Dw j).p by omega, if_true] at this`.

Rewrite using `[hmp]`. Use linear arithmetic over natural numbers and integers. Establish `hn' : 8 * (Module.finrank ℚ D.host.E / 2) * ((T.Q.Dw j).p + (T.Q.Dw j).q) + 4 ≤ n`. Rewrite using `[StandardLattice.finrank_host D, ← hU0.1]`. Simplify `hn` using `[Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]`.

Establish `key` using `cusp_sub_span_short Y.U σ₀ hσ₀ hG.unf hr hG.lev.2 hGm hP hχ nab hnab (badC Y) hbad a n hD hLP hn' _ (harm_short D T j Y e o Lb a n hH)`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hx : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n`. Establish `h0 : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtZ a n)` using `x.2`.

Rewrite `h0` using `[GlobalTheory.AllWt.cuspW_wtZ]`. Then use the resulting hypothesis. Establish `hsub : Submodule.span Y.d.c₂.F {f | f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.Tri …`. Rewrite using `[Submodule.map_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `g ⟨hg, x0, La, N, P, h1, h2, h3, h4, h5, h6, h7, h8⟩`.

Establish `hgV : g ∈ Y.V (wtZ a n)` using `by show g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtZ a n)`. Rewrite using `[GlobalTheory.AllWt.cuspW_wtZ]`. Conclude with `hg`. Conclude with `⟨⟨g, hgV⟩, ⟨x0, La, N, P, h1, h2, h3, h4, h5, h6, h7, h8⟩, rfl⟩`. Take `⟨z, hz, hzx⟩` from `hsub (key hx)`.

Establish `: z = x` using `Subtype.ext hzx`. Rewrite using `[← this]`. Conclude with `hz`.
-/
theorem GlobalTheory.CovGmin.span_thFam : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → Submodule.span Y.d.c₂.F (GlobalTheory.CovGmin.thFam Y nab a n (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n))) = ⊤ := by
  refine ⟨20000, by norm_num, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab
  have hH' := hH
  obtain ⟨hJ, hp, hq, hE, hj, hG, hL1, hM, hfs, hfr, ho, hD, hev, hn, hpos, hκ⟩ := hH'
  set σ₀ : Y.d.c₂.F →+* ℂ := Y.d.c₂.F.val.toRingHom with hσ₀def
  have hσ₀ : GoodEmb Y.d.c₂ σ₀ := rfl
  have hU0 := hG.unf σ₀ hσ₀
  have hr : 1 ≤ D.R.r := by have := hU0.1; omega
  obtain ⟨hrk, hmod⟩ := hG.modelW σ₀ hσ₀
  have hGm : ∀ k k', ((Y.U σ₀).X k).Gm = ((Y.U σ₀).X k').Gm ∧ ((Y.U σ₀).X k).ξ0 = ((Y.U σ₀).X k').ξ0 :=
    fun k k' => ⟨(hmod k).1.trans (hmod k').1.symm, (hmod k).2.trans (hmod k').2.symm⟩
  have hlaws := (GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).1
  have hPr := GlobalTheory.LevGeo.hasPrinc_laws D j _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hlaws σ₀ hσ₀
  have hP : ∀ k, GlobalTheory.Dict.HasPrinc ((Y.U σ₀).X k) Y.d.l₂.M := fun k ga hst hc =>
    hPr k ga hst fun v hv => by
      obtain ⟨u, hu, e⟩ := hc v hv
      refine ⟨u, hu, ?_⟩
      rw [e, add_sub_cancel_left]
      first
        | rfl
        | exact (Nat.cast_smul_eq_nsmul _ _ _).symm
        | simp
  have hχ : ∀ a n, Dom a n → ∀ k, GlobalTheory.Dict.ChiOne ((Y.U σ₀).X k) (laU (Y.U σ₀) a n k) :=
    fun a n hd k ga hga => hG.chiTriv σ₀ hσ₀ a n hd k ga hga
  have hbad : 0 < badC Y := by
    have h1 := D.host.qd_big.1
    have h2 := d_pos D
    have h3 := Y.d.l₂.three_le
    have hq0 : 0 < D.host.q := by omega
    have hM0 : 0 < Y.d.l₂.M := by omega
    unfold badC
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos hq0) h2) hM0
  have hLP : LastPos (T.Q.Dw j) a := by
    intro τ hτ hm
    have hτ' : τ ↑T.Q.H.rt = T.Q.H.rt0 := hτ
    have hmp : (T.Q.Dw j).mult τ = (T.Q.Dw j).p := by simp [Datum.mult, hτ']
    have := hpos ⟨τ, hτ⟩ ⟨(T.Q.Dw j).p - 1, by omega⟩ (by simp; omega)
    simp only [laOf, GlobalTheory.AllWt.weightOf, show (T.Q.Dw j).p - 1 < (T.Q.Dw j).p by omega, if_true] at this
    rw [hmp]
    omega
  have hn' : 8 * (Module.finrank ℚ D.host.E / 2) * ((T.Q.Dw j).p + (T.Q.Dw j).q) + 4 ≤ n := by
    rw [StandardLattice.finrank_host D, ← hU0.1]
    simpa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] using hn
  have key := cusp_sub_span_short Y.U σ₀ hσ₀ hG.unf hr hG.lev.2 hGm hP hχ nab hnab (badC Y) hbad a n hD hLP hn' _
    (harm_short D T j Y e o Lb a n hH)
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
    have h0 : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtZ a n) := x.2
    rwa [GlobalTheory.AllWt.cuspW_wtZ] at h0
  have hsub : Submodule.span Y.d.c₂.F {f | f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧
      ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
        Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
          La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧
          GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ Real.exp (20000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧
          ∀ (p : TRing Y.d.c₂.F) (y : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
            thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y (f p y)} ≤
      (Submodule.span Y.d.c₂.F (GlobalTheory.CovGmin.thFam Y nab a n
        (Real.exp (20000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)))).map (Y.V (wtZ a n)).subtype := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro g ⟨hg, x0, La, N, P, h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hgV : g ∈ Y.V (wtZ a n) := by
      show g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtZ a n)
      rw [GlobalTheory.AllWt.cuspW_wtZ]
      exact hg
    exact ⟨⟨g, hgV⟩, ⟨x0, La, N, P, h1, h2, h3, h4, h5, h6, h7, h8⟩, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hsub (key hx)
  have : z = x := Subtype.ext hzx
  rw [← this]
  exact hz
