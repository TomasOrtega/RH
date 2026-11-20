import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightLeOfMemWtSpan

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.CycDense

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `m t _`. Simplify using `using hM m t`. Consider the case `succ k ih`.

Introduce `m t ht`. Establish `hB : ∀ s, 0 ≤ s → ‖f (m + 1) s‖ ≤ M (m + (k + 1)) * s ^ k / (k.factorial : ℝ)`. Introduce `s hs`. Establish `h` using `ih (m + 1) s hs`. Rewrite `h` using `[show m + 1 + k = m + (k + 1) by omega]`. Then use the resulting hypothesis.

Establish `hcont : ContinuousOn (f m) (Set.Icc 0 t)` using `fun s _ => (hd m s).continuousAt.continuousWithinAt`. Establish `hf : (k.factorial : ℝ) ≠ 0` using `by positivity`. Establish `hBd : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt (fun s => M (m + (k + 1)) * s ^ (k + 1) / ((k + 1).factorial : ℝ)) (M (m + (k + 1)) * s ^ k / (k.factorial : ℝ)) (Set.Ici s) s`. Introduce `s _`. Establish `h1` using `((hasDerivAt_pow (k + 1) s).const_mul (M (m + (k + 1)))).div_const ((k + 1).factorial : ℝ)`.

Establish `e : M (m + (k + 1)) * (((k + 1 : ℕ) : ℝ) * s ^ (k + 1 - 1)) / ((k + 1).factorial : ℝ) = M (m + (k + 1)) * s ^ k / (k.factorial : ℝ)`. Rewrite using `[Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, div_eq_div_iff (mul_ne_zero (by positivity) hf) hf]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h1.hasDerivWithinAt.congr_deriv e`. Establish `hBc : ContinuousOn (fun s : ℝ => M (m + (k + 1)) * s ^ (k + 1) / ((k + 1).factorial : ℝ)) (Set.Icc 0 t)` using `((continuous_const.mul (continuous_pow (k + 1))).div_const _).continuousOn`.

Conclude with `image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcont (fun s _ => (hd m s).hasDerivWithinAt) (by simp [h0]) hBc hBd (fun s hs => hB s hs.1) ⟨ht, le_rfl⟩`.
-/
theorem chain_bound (f : ℕ → ℝ → ℂ) (M : ℕ → ℝ)
    (hd : ∀ m t, HasDerivAt (f m) (f (m + 1) t) t) (h0 : ∀ m, f m 0 = 0)
    (hM : ∀ m t, ‖f m t‖ ≤ M m) (k : ℕ) :
    ∀ m, ∀ t, 0 ≤ t → ‖f m t‖ ≤ M (m + k) * t ^ k / (k.factorial : ℝ) := by
  induction k with
  | zero =>
    intro m t _
    simpa using hM m t
  | succ k ih =>
    intro m t ht
    have hB : ∀ s, 0 ≤ s → ‖f (m + 1) s‖ ≤ M (m + (k + 1)) * s ^ k / (k.factorial : ℝ) := by
      intro s hs
      have h := ih (m + 1) s hs
      rwa [show m + 1 + k = m + (k + 1) by omega] at h
    have hcont : ContinuousOn (f m) (Set.Icc 0 t) :=
      fun s _ => (hd m s).continuousAt.continuousWithinAt
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hBd : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt
        (fun s => M (m + (k + 1)) * s ^ (k + 1) / ((k + 1).factorial : ℝ))
        (M (m + (k + 1)) * s ^ k / (k.factorial : ℝ)) (Set.Ici s) s := by
      intro s _
      have h1 := ((hasDerivAt_pow (k + 1) s).const_mul (M (m + (k + 1)))).div_const
        ((k + 1).factorial : ℝ)
      have e : M (m + (k + 1)) * (((k + 1 : ℕ) : ℝ) * s ^ (k + 1 - 1)) / ((k + 1).factorial : ℝ) =
          M (m + (k + 1)) * s ^ k / (k.factorial : ℝ) := by
        rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
          div_eq_div_iff (mul_ne_zero (by positivity) hf) hf]
        ring
      exact h1.hasDerivWithinAt.congr_deriv e
    have hBc : ContinuousOn (fun s : ℝ => M (m + (k + 1)) * s ^ (k + 1) / ((k + 1).factorial : ℝ))
        (Set.Icc 0 t) :=
      ((continuous_const.mul (continuous_pow (k + 1))).div_const _).continuousOn
    exact image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcont
      (fun s _ => (hd m s).hasDerivWithinAt) (by simp [h0]) hBc hBd
      (fun s hs => hB s hs.1) ⟨ht, le_rfl⟩

/- English proof (translation)
Establish `hsum` using `taylorRadius C B t hC hB ht hlt`. Establish `hb : ∀ k : ℕ, ‖f 0 t‖ ≤ D * ((C * t) ^ k * (B + k) ^ k / (k.factorial : ℝ))`. Introduce `k`. Establish `h` using `chain_bound f (fun m => D * (C ^ m * (B + m) ^ m)) hd h0 hM k 0 t ht`. Simplify using `only [zero_add] at h`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlim : Filter.Tendsto (fun k : ℕ => D * ((C * t) ^ k * (B + k) ^ k / (k.factorial : ℝ))) Filter.atTop (nhds (D * 0))` using `hsum.tendsto_atTop_zero.const_mul D`. Establish `h` using `ge_of_tendsto' hlim hb`. Rewrite `h` using `[mul_zero]`. Conclude with `norm_le_zero_iff.mp h`.
-/
theorem chain_zero (f : ℕ → ℝ → ℂ) (C B D t : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hlt : C * t * Real.exp 1 < 1)
    (hd : ∀ m t, HasDerivAt (f m) (f (m + 1) t) t) (h0 : ∀ m, f m 0 = 0)
    (hM : ∀ m t, ‖f m t‖ ≤ D * (C ^ m * (B + m) ^ m)) : f 0 t = 0 := by
  have hsum := taylorRadius C B t hC hB ht hlt
  have hb : ∀ k : ℕ, ‖f 0 t‖ ≤ D * ((C * t) ^ k * (B + k) ^ k / (k.factorial : ℝ)) := by
    intro k
    have h := chain_bound f (fun m => D * (C ^ m * (B + m) ^ m)) hd h0 hM k 0 t ht
    simp only [zero_add] at h
    calc ‖f 0 t‖ ≤ _ := h
      _ = _ := by rw [mul_pow]; ring
  have hlim : Filter.Tendsto (fun k : ℕ => D * ((C * t) ^ k * (B + k) ^ k / (k.factorial : ℝ)))
      Filter.atTop (nhds (D * 0)) := hsum.tendsto_atTop_zero.const_mul D
  have h := ge_of_tendsto' hlim hb
  rw [mul_zero] at h
  exact norm_le_zero_iff.mp h

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}

def act (E : Fin n → Fin n → Module.End ℂ V) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, X a b • E a b

/- English proof (translation)
Simplify using `only [act, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
theorem act_apply (X : Matrix (Fin n) (Fin n) ℂ) (v : V) : act E X v = ∑ a, ∑ b, X a b • E a b v := by
  simp only [act, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Establish `hs : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε` using `expUJ n ε X hX s`. Establish `ht : NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε` using `expUJ n ε X hX t`. Rewrite using `[oneParam n X s t, hσ.1.2 _ hs _ ht]`. Both sides reduce to the same expression.
-/
theorem sigma_add (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s t : ℝ) :
    σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) =
      σ (NormedSpace.exp ((s : ℂ) • X)) * σ (NormedSpace.exp ((t : ℂ) • X)) := by
  have hs : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε := expUJ n ε X hX s
  have ht : NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := expUJ n ε X hX t
  rw [oneParam n X s t, hσ.1.2 _ hs _ ht]
  rfl

/- English proof (translation)
Establish `h0` using `hD.2.2.1 X hX v`. Rewrite `h0` using `[← act_apply]`. Establish `h2 : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) (σ (NormedSpace.exp ((s : ℂ) • X)) (act E X v : H)) (s - s)`. Rewrite using `[sub_self]`. Conclude with `((σ (NormedSpace.exp ((s : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0`.

Establish `h1` using `h2.comp_sub_const s s`. Establish `key : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) = fun t : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (σ (NormedSpace.exp (((t - s : ℝ) : ℂ) • X)) (v : H))`. Use function extensionality and compare the values at `t`. Establish `h` using `sigma_add hσ hX s (t - s)`. Establish `e : s + (t - s) = t` using `by ring`.

Rewrite `h` using `[e]`. Rewrite using `[h, ContinuousLinearMap.mul_apply]`. Rewrite using `[key]`. Conclude with `h1`.
-/
theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((s : ℂ) • X)) (act E X v : V)) s := by
  have h0 := hD.2.2.1 X hX v
  rw [← act_apply] at h0
  have h2 : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((s : ℂ) • X))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) (σ (NormedSpace.exp ((s : ℂ) • X)) (act E X v : H)) (s - s) := by
    rw [sub_self]
    exact ((σ (NormedSpace.exp ((s : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
  have h1 := h2.comp_sub_const s s
  have key : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (σ (NormedSpace.exp (((t - s : ℝ) : ℂ) • X)) (v : H)) := by
    funext t
    have h := sigma_add hσ hX s (t - s)
    have e : s + (t - s) = t := by ring
    rw [e] at h
    rw [h, ContinuousLinearMap.mul_apply]
  rw [key]
  exact h1

/- English proof (translation)
Establish `hc` using `abs_nonneg c`. Establish `e1 : 2 * n * T ^ 2 + |c| ≤ (2 * n + |c|) * (T + 1) ^ 2`. Use polynomial arithmetic with `[mul_nonneg hn hT, mul_nonneg hc hT, mul_nonneg hc (sq_nonneg T)]`. Establish `e2 : (2 * n + |c|) * (T + 1) ^ 2 ≤ (2 * n + |c| + 1) ^ 2 * (T + 1) ^ 2`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises.

Use polynomial arithmetic with `[sq_nonneg (2 * n + |c|)]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem two_mul_sq_add_abs_mul_sq_le_sq (n c T w : ℝ) (hn : 0 ≤ n) (hT : 0 ≤ T) :
    (2 * n * T ^ 2 + |c|) * w ^ 2 ≤ ((2 * n + |c| + 1) * (T + 1) * w) ^ 2 := by
  have hc := abs_nonneg c
  have e1 : 2 * n * T ^ 2 + |c| ≤ (2 * n + |c|) * (T + 1) ^ 2 := by
    nlinarith [mul_nonneg hn hT, mul_nonneg hc hT, mul_nonneg hc (sq_nonneg T)]
  have e2 : (2 * n + |c|) * (T + 1) ^ 2 ≤ (2 * n + |c| + 1) ^ 2 * (T + 1) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_nonneg (2 * n + |c|)]
  calc (2 * n * T ^ 2 + |c|) * w ^ 2 ≤ (2 * n + |c| + 1) ^ 2 * (T + 1) ^ 2 * w ^ 2 :=
        mul_le_mul_of_nonneg_right (e1.trans e2) (sq_nonneg _)
    _ = _ := by ring

/- English proof (translation)
Take `⟨hgl, hun, -, -⟩` from `hD`. Take `⟨-, -, -, hstep, -, -, -⟩` from `pfilFacts (↥V) n ε E u hgl`. Use `⟨Real.sqrt (ckv ε μ) + n + 1, (∑ a, ∑ b, ‖X a b‖) * (2 * (n : ℝ) + |c| + 1), by positivity, by positivity, fun j w hw => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[act_apply]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hstep j a b w hw)`.

Establish `hg` using `GlobalTheory.FilGrowth.uGrowth (↥V) n ε E μ c u hgl hun hu hc hfd j w hw`. Establish `hT : 0 ≤ Real.sqrt (ckv ε μ) + j + n` using `by positivity`. Establish `hone : ∀ a b, ‖E a b w‖ ≤ (2 * (n : ℝ) + |c| + 1) * (Real.sqrt (ckv ε μ) + j + n + 1) * ‖w‖`. Introduce `a b`. Establish `h1 : ‖E a b w‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b w‖ ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `h1.trans (hg.trans (two_mul_sq_add_abs_mul_sq_le_sq n c _ ‖w‖ (Nat.cast_nonneg n) hT))`. Establish `hy : 0 ≤ (2 * (n : ℝ) + |c| + 1) * (Real.sqrt (ckv ε μ) + j + n + 1) * ‖w‖`. Check the signs of the components of the expression. Use polynomial arithmetic with `[norm_nonneg (E a b w)]`.

Rewrite using `[act_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hone a b) (norm_nonneg _)`. Use `_ = _ := by simp only [← Finset.sum_mul]; ring`.
-/
theorem act_growth (hD : IsDer ε σ V E) {μ : Fin n → ℝ} {c : ℝ} {u : V} (hu : KHighest ε E μ u)
    (hfd : FiniteDimensional ℂ (kSpan ε E u)) (hc : Cas E u = (c : ℂ) • u)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ j : ℕ, ∀ w ∈ pfil ε E u j,
      act E X w ∈ pfil ε E u (j + 1) ∧ ‖act E X w‖ ≤ C * (B + j) * ‖w‖ := by
  obtain ⟨hgl, hun, -, -⟩ := hD
  obtain ⟨-, -, -, hstep, -, -, -⟩ := pfilFacts (↥V) n ε E u hgl
  refine ⟨Real.sqrt (ckv ε μ) + n + 1, (∑ a, ∑ b, ‖X a b‖) * (2 * (n : ℝ) + |c| + 1),
    by positivity, by positivity, fun j w hw => ⟨?_, ?_⟩⟩
  · rw [act_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (hstep j a b w hw)
  · have hg := GlobalTheory.FilGrowth.uGrowth (↥V) n ε E μ c u hgl hun hu hc hfd j w hw
    have hT : 0 ≤ Real.sqrt (ckv ε μ) + j + n := by positivity
    have hone : ∀ a b, ‖E a b w‖ ≤
        (2 * (n : ℝ) + |c| + 1) * (Real.sqrt (ckv ε μ) + j + n + 1) * ‖w‖ := by
      intro a b
      have h1 : ‖E a b w‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b w‖ ^ 2 :=
        calc ‖E a b w‖ ^ 2 ≤ ∑ b', ‖E a b' w‖ ^ 2 :=
              Finset.single_le_sum (f := fun b' => ‖E a b' w‖ ^ 2) (fun _ _ => by positivity)
                (Finset.mem_univ b)
          _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ b', ‖E a' b' w‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ a)
      have h3 := h1.trans (hg.trans (two_mul_sq_add_abs_mul_sq_le_sq n c _ ‖w‖ (Nat.cast_nonneg n) hT))
      have hy : 0 ≤ (2 * (n : ℝ) + |c| + 1) * (Real.sqrt (ckv ε μ) + j + n + 1) * ‖w‖ := by
        positivity
      nlinarith [norm_nonneg (E a b w)]
    rw [act_apply]
    calc ‖∑ a, ∑ b, X a b • E a b w‖ ≤ ∑ a, ∑ b, ‖X a b • E a b w‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a, ∑ b, ‖X a b‖ *
            ((2 * (n : ℝ) + |c| + 1) * (Real.sqrt (ckv ε μ) + j + n + 1) * ‖w‖) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
            rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hone a b) (norm_nonneg _)
      _ = _ := by simp only [← Finset.sum_mul]; ring

/- English proof (translation)
Take `⟨-, -, -, -, hle, hex, -⟩` from `pfilFacts (↥V) n ε E u hD.1`. Use `set M : Submodule ℂ H := (cyc E u).map V.subtype with hM`. Establish `hvan : ∀ y ∈ Mᗮ, ∀ x ∈ cyc E u, ⟪y, σ (NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ = 0`. Introduce `y hy x hx`. Take `⟨j, hj⟩` from `hex x hx`.

Establish `hmem : ∀ m : ℕ, ((act E X) ^ m) x ∈ pfil ε E u (j + m)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using hj`. Consider the case `succ m ihm`.

Rewrite using `[pow_succ', Module.End.mul_apply, ← add_assoc]`. Conclude with `(hgr (j + m) _ ihm).1`. Establish `hnorm : ∀ m : ℕ, ‖((act E X) ^ m) x‖ ≤ C ^ m * (B + j + m) ^ m * ‖x‖` using `fun m => growthIter (↥V) (act E X) (pfil ε E u) B C hB hC hgr j m x hj`. Establish `hd' : ∀ (m : ℕ) (s : ℝ), HasDerivAt (fun s : ℝ => ⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ) (⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ (m + 1)) x : V) : H)⟫_ℂ) s`. Introduce `m s`.

Establish `h` using `hasDerivAt_orbit hσ hD hX (((act E X) ^ m) x) s`. Establish `h2` using `((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h`. Establish `e : act E X (((act E X) ^ m) x) = ((act E X) ^ (m + 1)) x`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Rewrite using `[← e]`.

Conclude with `h2`. Establish `h0' : ∀ m : ℕ, ⟪y, σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ = 0`. Introduce `m`. Rewrite using `[Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply]`. Conclude with `Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem (hle _ (hmem m))) hy`.

Establish `hM' : ∀ (m : ℕ) (s : ℝ), ‖⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ‖ ≤ (‖y‖ * ‖x‖) * (C ^ m * (B + j + m) ^ m)`. Introduce `m s`. Establish `hg : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε` using `expUJ n ε X hX s`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `chain_zero (fun m s => ⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ) C (B + j) (‖y‖ * ‖x‖) t hC (by positivity) ht hlt hd' h0' hM'`.

Simplify using `only [pow_zero, Module.End.one_apply] at h`. Conclude with `h`. Establish `hMM : ∀ z ∈ M, σ (NormedSpace.exp ((t : ℂ) • X)) z ∈ M.topologicalClosure`. Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hz`.

Rewrite using `[← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]`. Introduce `y hy`. Conclude with `hvan y hy x hx`. Establish `hcl : M.topologicalClosure ≤ M.topologicalClosure.comap (σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap` using `Submodule.topologicalClosure_minimal M (fun z hz => hMM z hz) (M.isClosed_topologicalClosure.preimage (σ _).continuous)`. Introduce `v hv`.

Conclude with `hcl hv`.
-/
private theorem exp_smul_mem_closure_cyc_of_small [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E)
    {u : V} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgr : ∀ j : ℕ, ∀ w ∈ pfil ε E u j,
      act E X w ∈ pfil ε E u (j + 1) ∧ ‖act E X w‖ ≤ C * (B + j) * ‖w‖)
    {t : ℝ} (ht : 0 ≤ t) (hlt : C * t * Real.exp 1 < 1) :
    ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure,
      σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ ((cyc E u).map V.subtype).topologicalClosure := by
  obtain ⟨-, -, -, -, hle, hex, -⟩ := pfilFacts (↥V) n ε E u hD.1
  set M : Submodule ℂ H := (cyc E u).map V.subtype with hM
  have hvan : ∀ y ∈ Mᗮ, ∀ x ∈ cyc E u,
      ⟪y, σ (NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ = 0 := by
    intro y hy x hx
    obtain ⟨j, hj⟩ := hex x hx
    have hmem : ∀ m : ℕ, ((act E X) ^ m) x ∈ pfil ε E u (j + m) := by
      intro m
      induction m with
      | zero => simpa using hj
      | succ m ihm =>
        rw [pow_succ', Module.End.mul_apply, ← add_assoc]
        exact (hgr (j + m) _ ihm).1
    have hnorm : ∀ m : ℕ, ‖((act E X) ^ m) x‖ ≤ C ^ m * (B + j + m) ^ m * ‖x‖ :=
      fun m => growthIter (↥V) (act E X) (pfil ε E u) B C hB hC hgr j m x hj
    have hd' : ∀ (m : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ)
        (⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ (m + 1)) x : V) : H)⟫_ℂ) s := by
      intro m s
      have h := hasDerivAt_orbit hσ hD hX (((act E X) ^ m) x) s
      have h2 := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
      have e : act E X (((act E X) ^ m) x) = ((act E X) ^ (m + 1)) x := by
        rw [pow_succ', Module.End.mul_apply]
      rw [← e]
      exact h2
    have h0' : ∀ m : ℕ,
        ⟪y, σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ = 0 := by
      intro m
      rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem (hle _ (hmem m))) hy
    have hM' : ∀ (m : ℕ) (s : ℝ),
        ‖⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ‖ ≤
          (‖y‖ * ‖x‖) * (C ^ m * (B + j + m) ^ m) := by
      intro m s
      have hg : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε := expUJ n ε X hX s
      calc _ ≤ ‖y‖ * ‖σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)‖ :=
            norm_inner_le_norm _ _
        _ = ‖y‖ * ‖((act E X) ^ m) x‖ := by rw [hσ.2.1 _ hg]; rfl
        _ ≤ ‖y‖ * (C ^ m * (B + j + m) ^ m * ‖x‖) :=
            mul_le_mul_of_nonneg_left (hnorm m) (norm_nonneg _)
        _ = _ := by ring
    have h := chain_zero
      (fun m s => ⟪y, σ (NormedSpace.exp ((s : ℂ) • X)) ((((act E X) ^ m) x : V) : H)⟫_ℂ)
      C (B + j) (‖y‖ * ‖x‖) t hC (by positivity) ht hlt hd' h0' hM'
    simp only [pow_zero, Module.End.one_apply] at h
    exact h
  have hMM : ∀ z ∈ M, σ (NormedSpace.exp ((t : ℂ) • X)) z ∈ M.topologicalClosure := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro y hy
    exact hvan y hy x hx
  have hcl : M.topologicalClosure ≤
      M.topologicalClosure.comap (σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap :=
    Submodule.topologicalClosure_minimal M (fun z hz => hMM z hz)
      (M.isClosed_topologicalClosure.preimage (σ _).continuous)
  intro v hv
  exact hcl hv

/- English proof (translation)
Take `⟨B, C, hB, hC, hgr⟩` from `act_growth hD hu hfd hc X`. Take `⟨N, hN⟩ : ∃ N : ℕ, C * Real.exp 1 < N` from `exists_nat_gt _`. Establish `hNpos : (0 : ℝ) < N` using `lt_of_le_of_lt (mul_nonneg hC (Real.exp_pos 1).le) hN`. Establish `hδ : C * (1 / (N : ℝ)) * Real.exp 1 < 1`. Establish `e : C * (1 / (N : ℝ)) * Real.exp 1 = C * Real.exp 1 / N` using `by ring`.

Rewrite using `[e, div_lt_one hNpos]`. Conclude with `hN`. Establish `hstep` using `exp_smul_mem_closure_cyc_of_small hσ hD hX hB hC hgr (by positivity) hδ`. Establish `hk : ∀ k : ℕ, ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure, σ (NormedSpace.exp ((((k : ℝ) * (1 / (N : ℝ)) : ℝ) : ℂ) • X)) v ∈ ((cyc E u).map V.subtype).topologicalClosure`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `v hv`. Rewrite using `[Nat.cast_zero, zero_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply]`. Conclude with `hv`.

Consider the case `succ k ih`. Introduce `v hv`. Establish `e : ((k + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) = (k : ℝ) * (1 / (N : ℝ)) + 1 / (N : ℝ)` using `by push_cast; ring`. Rewrite using `[e, sigma_add hσ hX, ContinuousLinearMap.mul_apply]`. Conclude with `ih _ (hstep _ hv)`.

Introduce `v hv`. Establish `h` using `hk N v hv`. Establish `e : (N : ℝ) * (1 / (N : ℝ)) = 1` using `by field_simp`. Rewrite `h` using `[e, Complex.ofReal_one, one_smul]`. Conclude with `h`.
-/
theorem exp_stable [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E)
    {μ : Fin n → ℝ} {c : ℝ} {u : V} (hu : KHighest ε E μ u)
    (hfd : FiniteDimensional ℂ (kSpan ε E u)) (hc : Cas E u = (c : ℂ) • u)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure,
      σ (NormedSpace.exp X) v ∈ ((cyc E u).map V.subtype).topologicalClosure := by
  obtain ⟨B, C, hB, hC, hgr⟩ := act_growth hD hu hfd hc X
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C * Real.exp 1 < N := exists_nat_gt _
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (mul_nonneg hC (Real.exp_pos 1).le) hN
  have hδ : C * (1 / (N : ℝ)) * Real.exp 1 < 1 := by
    have e : C * (1 / (N : ℝ)) * Real.exp 1 = C * Real.exp 1 / N := by ring
    rw [e, div_lt_one hNpos]
    exact hN
  have hstep := exp_smul_mem_closure_cyc_of_small hσ hD hX hB hC hgr (by positivity) hδ
  have hk : ∀ k : ℕ, ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure,
      σ (NormedSpace.exp ((((k : ℝ) * (1 / (N : ℝ)) : ℝ) : ℂ) • X)) v ∈
        ((cyc E u).map V.subtype).topologicalClosure := by
    intro k
    induction k with
    | zero =>
      intro v hv
      rw [Nat.cast_zero, zero_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
        ContinuousLinearMap.one_apply]
      exact hv
    | succ k ih =>
      intro v hv
      have e : ((k + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) = (k : ℝ) * (1 / (N : ℝ)) + 1 / (N : ℝ) := by
        push_cast; ring
      rw [e, sigma_add hσ hX, ContinuousLinearMap.mul_apply]
      exact ih _ (hstep _ hv)
  intro v hv
  have h := hk N v hv
  have e : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp
  rw [e, Complex.ofReal_one, one_smul] at h
  exact h

/- English proof (translation)
Introduce `n ε H _ _ _ σ V E μ c u hσ hD hirr hu0 hu hfd hc`. Take `⟨hp0, -, -, -, hle, -, -⟩` from `pfilFacts (↥V) n ε E u hD.1`. Establish `hstab : ∀ g ∈ UJset ε, ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure, σ g v ∈ ((cyc E u).map V.subtype).topologicalClosure`. Introduce `g hg v hv`. Take `⟨Z, Y, hZ, hY, rfl⟩` from `genExp n ε g hg`.

Establish `hZ' : NormedSpace.exp Z ∈ UJset ε`. Establish `h1` using `expUJ n ε Z hZ.1 1`. Rewrite `h1` using `[Complex.ofReal_one, one_smul]`. Conclude with `h1`. Establish `hY' : NormedSpace.exp Y ∈ UJset ε`.

Establish `h1` using `expUJ n ε Y hY.1 1`. Rewrite `h1` using `[Complex.ofReal_one, one_smul]`. Conclude with `h1`. Rewrite using `[hσ.1.2 _ hZ' _ hY', ContinuousLinearMap.comp_apply]`. Conclude with `exp_stable hσ hD hu hfd hc hZ.1 _ (exp_stable hσ hD hu hfd hc hY.1 v hv)`.

Break down `hirr _ (Submodule.isClosed_topologicalClosure _) hstab with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hu1 : (u : H) ∈ ((cyc E u).map V.subtype).topologicalClosure`. Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Apply `Submodule.mem_map_of_mem` to reduce the goal to its premises.

Apply `hle 0` to reduce the goal to its premises. Rewrite using `[hp0]`. Conclude with `mem_compactSpan_self ε E u`. Rewrite `hu1` using `[h, Submodule.mem_bot]`. Conclude with `hu0 (Submodule.coe_eq_zero.mp hu1)`.

Conclude with `Submodule.dense_iff_topologicalClosure_eq_top.mpr h`.
-/
theorem cyc_dense : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (c : ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsIrredOn (UJset ε) σ → u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → Cas E u = (c : ℂ) • u → Dense (((cyc E u).map V.subtype : Submodule ℂ H) : Set H) := by
  intro n ε H _ _ _ σ V E μ c u hσ hD hirr hu0 hu hfd hc
  obtain ⟨hp0, -, -, -, hle, -, -⟩ := pfilFacts (↥V) n ε E u hD.1
  have hstab : ∀ g ∈ UJset ε, ∀ v ∈ ((cyc E u).map V.subtype).topologicalClosure,
      σ g v ∈ ((cyc E u).map V.subtype).topologicalClosure := by
    intro g hg v hv
    obtain ⟨Z, Y, hZ, hY, rfl⟩ := genExp n ε g hg
    have hZ' : NormedSpace.exp Z ∈ UJset ε := by
      have h1 := expUJ n ε Z hZ.1 1
      rw [Complex.ofReal_one, one_smul] at h1
      exact h1
    have hY' : NormedSpace.exp Y ∈ UJset ε := by
      have h1 := expUJ n ε Y hY.1 1
      rw [Complex.ofReal_one, one_smul] at h1
      exact h1
    rw [hσ.1.2 _ hZ' _ hY', ContinuousLinearMap.comp_apply]
    exact exp_stable hσ hD hu hfd hc hZ.1 _ (exp_stable hσ hD hu hfd hc hY.1 v hv)
  rcases hirr _ (Submodule.isClosed_topologicalClosure _) hstab with h | h
  · exfalso
    have hu1 : (u : H) ∈ ((cyc E u).map V.subtype).topologicalClosure := by
      apply Submodule.le_topologicalClosure
      apply Submodule.mem_map_of_mem
      apply hle 0
      rw [hp0]
      exact mem_compactSpan_self ε E u
    rw [h, Submodule.mem_bot] at hu1
    exact hu0 (Submodule.coe_eq_zero.mp hu1)
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr h

end GlobalTheory.CycDense
