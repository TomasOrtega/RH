import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJetsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivProdCoordAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ProdMeasure
variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Use `haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩`. Introduce `g`. Proceed by induction on `g with`. Consider the case `zero`. Introduce `u s _`.

Simplify using `using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))`. Consider the case `succ g ih`. Introduce `u s h`. Establish `h1` using `(h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)`. Rewrite using `[← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[Fin.consEquiv, Fin.prod_univ_succ]`.
-/
theorem hasSum_pi_prod : ∀ (g : ℕ) (u : Fin g → ℕ → ℂ_[q]) (s : Fin g → ℂ_[q]),
    (∀ i, HasSum (u i) (s i)) → HasSum (fun ν : Fin g → ℕ => ∏ i, u i (ν i)) (∏ i, s i) := by
  haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  intro g
  induction g with
  | zero =>
    intro u s _
    simpa using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))
  | succ g ih =>
    intro u s h
    have h1 := (h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)
    rw [← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
    convert h1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `n`. Rewrite using `[pow_zero, coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ a ih`. Use `((sup_norm_laws q).1 _ _ _ _ ih h).2` as an intermediate fact. Rewrite `this` using `[mul_one, ← pow_succ]`. Then use the resulting hypothesis.
-/
theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih h).2
    rwa [mul_one, ← pow_succ] at this

/- English proof (translation)
Establish `H` using `Shift.shift_laws q ζ hζ`. Proceed by induction on `a with`. Consider the case `zero => simpa using H.2.2.1 1`. Consider the case `succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]`.
-/
theorem shiftS_pow {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) :
    shiftS ζ (f ^ a) = shiftS ζ f ^ a := by
  have H := Shift.shift_laws q ζ hζ
  induction a with
  | zero => simpa using H.2.2.1 1
  | succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]

/- English proof (translation)
Establish `H` using `TaylorRead.hat_laws q ι ℓ hl`. Proceed by induction on `a with`. Consider the case `zero => simpa using H.2.1 1`. Consider the case `succ a ih`. Simplify using `only [pow_succ]`.

Rewrite using `[(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]`.
-/
theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hl : constantCoeff ℓ = 0) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) (a : ℕ) : hat ι ℓ (fun z => G z ^ a) = hat ι ℓ G ^ a := by
  have H := TaylorRead.hat_laws q ι ℓ hl
  induction a with
  | zero => simpa using H.2.1 1
  | succ a ih =>
    simp only [pow_succ]
    rw [(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]

/- English proof (translation)
Rewrite using `[← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_const]`. Conclude with `Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]`.
-/
theorem prod_fiber_pow {g k : ℕ} (σ : Fin k → Fin g) (x : Fin g → ℂ_[q]) :
    ∏ l, x (σ l) = ∏ i, x i ^ (Finset.univ.filter (fun l => σ l = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

/- English proof (translation)
Introduce `d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht`. Use `set ω : ℂ_[q] := Ω / ι δ with hω`. Establish `hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)` using `fun j i => bd_one_pow (hL.1 _ (ht j i)) _`. Take `⟨μ, hμ1, hμ2⟩` from `GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)) ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by`. Rewrite using `[norm_mul, norm_prod]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩`. Use `⟨μ, hμ1, ?_⟩` and prove the remaining obligations. Introduce `n s y hs hst hy k ys F hF`. Establish `hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0`. Simplify using `[logS, ← coeff_zero_eq_constantCoeff_apply]`.

Establish `hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ))` using `fun j i => ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2`. Establish `hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1` using `fun i => (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1`. Establish `hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]), (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧ ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) * (fwdDiff (1 : ℤ_[q]))^[r] f 0) (ω ^ e * ι (iteratedDeriv e (fun z => W1 d …`. Introduce `i e`. Take `⟨f, hf, -⟩` from `GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)`.

Use `⟨f, hf, fun j => ?_⟩` and prove the remaining obligations. Take `⟨f', hf', h⟩` from `GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q _ _ n e ⟨1, hS j i⟩ (hroot i)`. Take `rfl : f' = f` from `by ext A; rw [hf, hf']`. Establish `han` using `(hdiff j i).analyticAt 0`. Rewrite `h` using `[shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)), ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han, (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) (han.pow (a i))).2.1 e]`.

Conclude with `h`. Use `choose f hf1 hf2 using hf`. Set `P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q])` to `fun σ => ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩`. Establish `hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card * ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0))`. Introduce `σ`.

Use `(hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_` and prove the remaining obligations. Use `hasSum_sum (s := Finset.univ) fun j _ => (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))` as an intermediate fact. Simplify using `only [Finset.sum_mul, mul_assoc]`. Simplify using `only [Finset.prod_mul_distrib] at this ⊢`. Conclude with `this`.

Establish `hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ`. Use extensionality with `A`. Rewrite using `[hF]`. Simplify using `only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val), ← prod_fiber_pow σ (fun i => zc (A i))]`. Simplify using `only [← mul_assoc]`. Rewrite using `[Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i)` using `fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ ℂ i)).pow _`. Establish `hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 = ∑ j, c j • iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0`. Rewrite using `[iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt`.

Rewrite using `[hit, hFP, map_sum μ]`. Simplify using `only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]`.

Simplify using `only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card), ← prod_fiber_pow σ (fun _ => ω)]`. Establish `e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hω]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem measure_of_products : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ), 0 < d → δ ≠ 0 → Ω ≠ 0 → Differentiable ℂ θ → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j i, PrimeTo d q (t j i)) → ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ ν : Fin g → ℕ, ‖∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C (Ω / ι δ) * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B)) ∧ ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * t j i)) → (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) * ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * zc (A i))) → ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  intro d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  set ω : ℂ_[q] := Ω / ι δ with hω
  have hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) :=
    fun j i => bd_one_pow (hL.1 _ (ht j i)) _
  obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g
    (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, norm_prod]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩
  refine ⟨μ, hμ1, ?_⟩
  intro n s y hs hst hy k ys F hF
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    simp [logS, ← coeff_zero_eq_constantCoeff_apply]
  have hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ)) := fun j i =>
    ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2
  have hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1 := fun i =>
    (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1
  have hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]),
      (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧
      ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) *
        (fwdDiff (1 : ℤ_[q]))^[r] f 0)
        (ω ^ e * ι (iteratedDeriv e (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro i e
    obtain ⟨f, hf, -⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)
    refine ⟨f, hf, fun j => ?_⟩
    obtain ⟨f', hf', h⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q _ _ n e ⟨1, hS j i⟩ (hroot i)
    obtain rfl : f' = f := by ext A; rw [hf, hf']
    have han := (hdiff j i).analyticAt 0
    rw [shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)),
      ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han,
      (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i)
        (han.pow (a i))).2.1 e] at h
    exact h
  choose f hf1 hf2 using hf
  let P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q]) := fun σ =>
    ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩
  have hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card *
      ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro σ
    refine (hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_
    have := hasSum_sum (s := Finset.univ) fun j _ =>
      (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))
    simp only [Finset.sum_mul, mul_assoc]
    simp only [Finset.prod_mul_distrib] at this ⊢
    exact this
  have hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ := by
    ext A
    rw [hF]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val),
      ← prod_fiber_pow σ (fun i => zc (A i))]
    simp only [← mul_assoc]
    rw [Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]
    ring
  have hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) :=
    fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ ℂ i)).pow _
  have hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0
      = ∑ j, c j • iteratedFDeriv ℂ k
        (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 := by
    rw [iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt
  rw [hit, hFP, map_sum μ]
  simp only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k
    (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]
  simp only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card),
    ← prod_fiber_pow σ (fun _ => ω)]
  have e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hω]; field_simp
  rw [e]
  ring

end GlobalTheory.MomOne.ProdMeasure
