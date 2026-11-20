import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

section SlopeTestRemainingChoices

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Establish `key : ∀ (k : ℕ), k = 0 → ∀ M : Matrix (Fin 0) (Fin k) E, degM x M = 0`. Introduce `k hk M`. Substitute `hk` using the available equality. Conclude with `degM_zero x M`. Establish `hr : ∀ W : Submodule E (Fin 0 → E), Module.finrank E W = 0` using `fun W => Module.finrank_zero_of_subsingleton`.

Use `⟨fun W => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[deg, key _ (hr W), hr W]`. Simplify using `[prof]`. Rewrite using `[deg, key _ (hr ⊤)]`. Simplify using `using hτ`.
-/
private theorem mem_cut_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {τ : ℝ} (hτ : 0 ≤ τ)
    (x : GA E 0) : x ∈ cutSet E 0 τ := by
  have key : ∀ (k : ℕ), k = 0 → ∀ M : Matrix (Fin 0) (Fin k) E, degM x M = 0 := by
    intro k hk M
    subst hk
    exact degM_zero x M
  have hr : ∀ W : Submodule E (Fin 0 → E), Module.finrank E W = 0 := fun W =>
    Module.finrank_zero_of_subsingleton
  refine ⟨fun W => ?_, ?_⟩
  · rw [deg, key _ (hr W), hr W]
    simp [prof]
  · rw [deg, key _ (hr ⊤)]
    simpa using hτ

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hρ0 : 0 ≤ ρ` using `by linarith`. Use `set l := max 0 (-Real.log ε) with hl`. Establish `hl0 : 0 ≤ l` using `le_max_left _ _`. Establish `hl1 : -Real.log ε ≤ l` using `le_max_right _ _`.

Establish `h1 : 1 + c * ρ ≤ (1 + c) * (1 + ρ)` using `by nlinarith`. Establish `h2 : (1 + ρ) ^ N ≤ N.factorial * Real.exp (1 + ρ)`. Use `Real.pow_div_factorial_le_exp (1 + ρ) (by linarith) N` as an intermediate fact. Rewrite `this` using `[div_le_iff₀' (by positivity)]`. Then use the resulting hypothesis. Establish `h3 : Real.exp (-(l * ρ)) ≤ ε ^ k`.

Establish `e : ε ^ k = Real.exp (k * Real.log ε)`. Rewrite using `[mul_comm, Real.exp_mul, Real.exp_log hε, Real.rpow_natCast]`. Rewrite using `[e]`. Use `Real.exp_le_exp.mpr ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ ρ - k), mul_le_mul_of_nonneg_right hl1 hk]`.

Establish `h4 : Real.exp (-((1 + l) * ρ)) = Real.exp (-ρ) * Real.exp (-(l * ρ))`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h5 : Real.exp (1 + ρ) * Real.exp (-ρ) = Real.exp 1`. Rewrite using `[← Real.exp_add]`.

Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (Real.exp_pos _).le` and prove the remaining obligations. Use `_ = (1 + c) ^ N * ((1 + ρ) ^ N * Real.exp (-ρ)) * Real.exp (-(l * ρ)) := by`. Rewrite using `[h4, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (1 + c) ^ N * (N.factorial * Real.exp 1) * ε ^ k := by`. Establish `h6 : (1 + ρ) ^ N * Real.exp (-ρ) ≤ N.factorial * Real.exp 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left h6 (by positivity)) h3 (Real.exp_pos _).le (by positivity)`.
-/
private theorem tail_num (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) (N k : ℕ) (ρ : ℝ) (hρ : 1 + (k : ℝ) ≤ ρ) :
    (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) ≤
      ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρ0 : 0 ≤ ρ := by linarith
  set l := max 0 (-Real.log ε) with hl
  have hl0 : 0 ≤ l := le_max_left _ _
  have hl1 : -Real.log ε ≤ l := le_max_right _ _
  have h1 : 1 + c * ρ ≤ (1 + c) * (1 + ρ) := by nlinarith
  have h2 : (1 + ρ) ^ N ≤ N.factorial * Real.exp (1 + ρ) := by
    have := Real.pow_div_factorial_le_exp (1 + ρ) (by linarith) N
    rwa [div_le_iff₀' (by positivity)] at this
  have h3 : Real.exp (-(l * ρ)) ≤ ε ^ k := by
    have e : ε ^ k = Real.exp (k * Real.log ε) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hε, Real.rpow_natCast]
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ ρ - k), mul_le_mul_of_nonneg_right hl1 hk]
  have h4 : Real.exp (-((1 + l) * ρ)) = Real.exp (-ρ) * Real.exp (-(l * ρ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h5 : Real.exp (1 + ρ) * Real.exp (-ρ) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  calc (1 + c * ρ) ^ N * Real.exp (-((1 + l) * ρ))
      ≤ ((1 + c) * (1 + ρ)) ^ N * Real.exp (-((1 + l) * ρ)) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (Real.exp_pos _).le
    _ = (1 + c) ^ N * ((1 + ρ) ^ N * Real.exp (-ρ)) * Real.exp (-(l * ρ)) := by
        rw [h4, mul_pow]
        ring
    _ ≤ (1 + c) ^ N * (N.factorial * Real.exp 1) * ε ^ k := by
        have h6 : (1 + ρ) ^ N * Real.exp (-ρ) ≤ N.factorial * Real.exp 1 := by
          calc (1 + ρ) ^ N * Real.exp (-ρ) ≤ (N.factorial * Real.exp (1 + ρ)) * Real.exp (-ρ) :=
                mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
            _ = N.factorial * Real.exp 1 := by rw [mul_assoc, h5]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h6 (by positivity)) h3 (Real.exp_pos _).le (by positivity)

/- English proof (translation)
Establish `e : ∫ x, g x ∂ν - ∫ x, f x ∂ν = -∫ x, A.indicator f x ∂ν`. Simplify using `only [h]`. Rewrite using `[integral_sub hf (hf.indicator hA)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg]`.

Establish `h1 : ‖∫ x, A.indicator f x ∂ν‖ₑ ≤ ENNReal.ofReal B`. Use `(enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)` and prove the remaining obligations. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `enorm_indicator_eq_indicator_enorm ..`. Rewrite `h1` using `[← ofReal_norm]`.

Conclude with `(ENNReal.ofReal_le_ofReal_iff hB).mp h1`.
-/
private theorem diff_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (f g : X → ℂ) (A : Set X)
    (hA : MeasurableSet A) (hf : Integrable f ν) (h : ∀ x, g x = f x - A.indicator f x) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∫⁻ x, A.indicator (fun x => ‖f x‖ₑ) x ∂ν ≤ ENNReal.ofReal B) :
    ‖∫ x, g x ∂ν - ∫ x, f x ∂ν‖ ≤ B := by
  have e : ∫ x, g x ∂ν - ∫ x, f x ∂ν = -∫ x, A.indicator f x ∂ν := by
    simp only [h]
    rw [integral_sub hf (hf.indicator hA)]
    ring
  rw [e, norm_neg]
  have h1 : ‖∫ x, A.indicator f x ∂ν‖ₑ ≤ ENNReal.ofReal B := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)
    refine lintegral_congr fun x => ?_
    exact enorm_indicator_eq_indicator_enorm ..
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h1

/- English proof (translation)
Introduce `hS hI hT hD E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε`. Set `s : Su E n ι` to `⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩`. Take `⟨c, hc, hsz⟩` from `hS E n hn`. Take `⟨c', hc', hcut⟩` from `hI E n`. Take `⟨N, hN⟩` from `hT E n ι s`.

Take `⟨Ct, hCt, hbd⟩` from `hN (1 + max 0 (-Real.log ε)) (by positivity)`. Use `⟨(c' + 1) * (2 + c + c ^ 2), fun C' hC' => ⟨Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)), fun k U Uπ Φ t o pp ht => ?_⟩⟩` and prove the remaining obligations. Set `m : Mid s` to `⟨U, Uπ, Φ, t, o, pp⟩`. Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Take `⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + k) * (1 + r₀ + r₁)` from `⟨_, rfl⟩`.

Establish `hρk : 1 + (k : ℝ) ≤ ρ` using `by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]`. Establish `hρ1 : 1 ≤ ρ` using `by linarith`. Establish `hρr : 1 + (r₀ + k * r₁) ≤ ρ` using `by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]`. Establish `hC'0 : 0 ≤ C'` using `le_trans (by positivity) hC'`. Take `⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = C' * ρ` from `⟨_, rfl⟩`.

Establish `hτ0 : 0 ≤ τ` using `by rw [hτdef]; positivity`. Establish `hR0 : 0 ≤ c * ρ` using `by positivity`. Establish `hsupp : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ c * ρ` using `fun z hz => by`. Establish `h1` using `(ht.toIsTest2.size z hz).1`. Use `(hsz z).2.1.trans (mul_le_mul_of_nonneg_left ?_ hc)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Set `A : Set (H E n 0)` to `{x | x.1 ∉ cutSet E n τ}`. Establish `hAm : MeasurableSet A`. Establish `ho : IsOpen A` using `((mahler_holds E n τ).1.preimage continuous_fst).isOpen_compl`. Use `haveI : BorelSpace (H E n 0) := ⟨rfl⟩`.

Conclude with `ho.measurableSet`. Establish `hAρ : ∀ x ∈ A, |ldet x| ≤ c * ρ → ρ ≤ r0 x` using `fun x hx hl => by`. Assume the negation of the conclusion as `hlt`. Use `hx (hcut τ x.1 ?_)` and prove the remaining obligations. Establish `h1` using `(hsz x).1`.

Establish `h2 : redSize x.1 ≤ ρ + c * (1 + c * ρ)` using `h1.trans (add_le_add (not_le.mp hlt).le (mul_le_mul_of_nonneg_left (by linarith) hc))`. Establish `h3 : 1 + redSize x.1 ≤ (2 + c + c ^ 2) * ρ` using `by nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ ρ - 1)]`. Establish `hq : 0 ≤ (2 + c + c ^ 2) * ρ` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hb` using `hbd m (c * ρ) ρ hR0 hsupp A hAρ`.

Establish `hB : 0 ≤ Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))` using `by positivity`. Establish `hmain` using `diff_le D.ν (lInt0 D k₁ k₂ Uπ) (lInt D k₁ k₂ τ Uπ) A hAm (hD E n ι s m) (fun x => by`. Establish `h2 : chiT τ x.2 = (1 : ℂ)` using `Set.indicator_of_mem (mem_cut_zero hτ0 x.2) _`. Distinguish the cases in `hx : x.1 ∈ cutSet E n τ`. Establish `h1 : chiT τ x.1 = (1 : ℂ)` using `Set.indicator_of_mem hx _`.

Establish `h3 : x ∉ A` using `fun h => h hx`. Simplify using `[lInt, lInt0, h1, h2, h3]`. Establish `h1 : chiT τ x.1 = (0 : ℂ)` using `Set.indicator_of_notMem hx _`. Establish `h3 : x ∈ A` using `hx`. Simplify using `[lInt, lInt0, h1, h2, h3]) _ hB hb`.

Rewrite using `[← hρdef, ← hτdef]`. Use `hmain.trans ?_` and prove the remaining obligations. Establish `hn'` using `tail_num c ε hc hε N k ρ hρk`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem tail_main : UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Sizes → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.InCut → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TailInt →
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.DiagInt → DiscreteGroups.T1.G.CutTail2 := by
  intro hS hI hT hD E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  obtain ⟨c, hc, hsz⟩ := hS E n hn
  obtain ⟨c', hc', hcut⟩ := hI E n
  obtain ⟨N, hN⟩ := hT E n ι s
  obtain ⟨Ct, hCt, hbd⟩ := hN (1 + max 0 (-Real.log ε)) (by positivity)
  refine ⟨(c' + 1) * (2 + c + c ^ 2), fun C' hC' =>
    ⟨Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)), fun k U Uπ Φ t o pp ht => ?_⟩⟩
  let m : Mid s := ⟨U, Uπ, Φ, t, o, pp⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + k) * (1 + r₀ + r₁) := ⟨_, rfl⟩
  have hρk : 1 + (k : ℝ) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hρ1 : 1 ≤ ρ := by linarith
  have hρr : 1 + (r₀ + k * r₁) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = C' * ρ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hR0 : 0 ≤ c * ρ := by positivity
  have hsupp : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ c * ρ := fun z hz => by
    have h1 := (ht.toIsTest2.size z hz).1
    refine (hsz z).2.1.trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith
  let A : Set (H E n 0) := {x | x.1 ∉ cutSet E n τ}
  have hAm : MeasurableSet A := by
    have ho : IsOpen A := ((mahler_holds E n τ).1.preimage continuous_fst).isOpen_compl
    haveI : BorelSpace (H E n 0) := ⟨rfl⟩
    exact ho.measurableSet
  have hAρ : ∀ x ∈ A, |ldet x| ≤ c * ρ → ρ ≤ r0 x := fun x hx hl => by
    by_contra hlt
    refine hx (hcut τ x.1 ?_)
    have h1 := (hsz x).1
    have h2 : redSize x.1 ≤ ρ + c * (1 + c * ρ) := h1.trans (add_le_add (not_le.mp hlt).le
      (mul_le_mul_of_nonneg_left (by linarith) hc))
    have h3 : 1 + redSize x.1 ≤ (2 + c + c ^ 2) * ρ := by nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ ρ - 1)]
    have hq : 0 ≤ (2 + c + c ^ 2) * ρ := by positivity
    calc c' * (1 + redSize x.1) ≤ c' * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_left h3 hc'
      _ ≤ (c' + 1) * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_right (by linarith) hq
      _ = ((c' + 1) * (2 + c + c ^ 2)) * ρ := by ring
      _ ≤ C' * ρ := mul_le_mul_of_nonneg_right hC' (by linarith)
      _ = τ := hτdef.symm
  have hb := hbd m (c * ρ) ρ hR0 hsupp A hAρ
  have hB : 0 ≤ Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) := by positivity
  have hmain := diff_le D.ν (lInt0 D k₁ k₂ Uπ) (lInt D k₁ k₂ τ Uπ) A hAm (hD E n ι s m) (fun x => by
      have h2 : chiT τ x.2 = (1 : ℂ) := Set.indicator_of_mem (mem_cut_zero hτ0 x.2) _
      by_cases hx : x.1 ∈ cutSet E n τ
      · have h1 : chiT τ x.1 = (1 : ℂ) := Set.indicator_of_mem hx _
        have h3 : x ∉ A := fun h => h hx
        simp [lInt, lInt0, h1, h2, h3]
      · have h1 : chiT τ x.1 = (0 : ℂ) := Set.indicator_of_notMem hx _
        have h3 : x ∈ A := hx
        simp [lInt, lInt0, h1, h2, h3]) _ hB hb
  rw [← hρdef, ← hτdef]
  refine hmain.trans ?_
  have hn' := tail_num c ε hc hε N k ρ hρk
  calc Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))
      = Ct * ‖U‖ * ((1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))) := by ring
    _ ≤ Ct * ‖U‖ * (((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ‖U‖ * ε ^ k := by ring

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `_` and use `tail_main`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailOf_pf :
    Basic → Sizes → InCut → TailInt → DiagInt → DiscreteGroups.T1.G.CutTail2 := fun _ => tail_main
