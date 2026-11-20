import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
/- English proof (translation)
Establish `key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0`. Introduce and unpack `k M rfl`. Conclude with `degM_zero x M`. Conclude with `key _ _ hW`.
-/
private theorem deg_finrank_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (x : GA E n)
    (W : Submodule E (Fin n → E)) (hW : Module.finrank E W = 0) : deg x W = 0 := by
  have key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro k M rfl
    exact degM_zero x M
  exact key _ _ hW

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
/- English proof (translation)
Simplify using `only [logSize, inv_inv]`. Conclude with `add_comm _ _`.
-/
private theorem logSize_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (h : GA E n) :
    logSize (h⁻¹ : GA E n) = logSize h := by
  simp only [logSize, inv_inv]
  exact add_comm _ _

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
/- English proof (translation)
Establish `a : (1 : ℝ) ≤ k` using `by exact_mod_cast h1`. Establish `b : (k : ℝ) ≤ n` using `by exact_mod_cast hk`. Establish `c : (1 : ℝ) ≤ 2 * n + 1 - k` using `by linarith`. Establish `d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k)` using `by nlinarith`. Establish `e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k))` using `mul_le_mul_of_nonneg_left d hτ`.

Simplify using `only [prof]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem tau_le_prof {n k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 1 ≤ k) (hk : k ≤ n) : τ ≤ prof n τ k := by
  have a : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have b : (k : ℝ) ≤ n := by exact_mod_cast hk
  have c : (1 : ℝ) ≤ 2 * n + 1 - k := by linarith
  have d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k) := by nlinarith
  have e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k)) := mul_le_mul_of_nonneg_left d hτ
  simp only [prof]
  nlinarith

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨C, hC0, hC⟩` from `E1.degRight E n`. Take `⟨B, hB⟩` from `(D1.degBdd E n).1 (1 : GA E n)`. Establish `hB' : ∀ W, deg (1 : GA E n) W ≤ B` using `fun W => hB ⟨W, rfl⟩`. Use `set A : ℝ := deg (1 : GA E n) ⊤ with hA`.

Use `⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩` and prove the remaining obligations. Establish `hr : 0 ≤ redSize g` using `((E1.redBasic E n).2.1 g).1`. Establish `hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g`. Apply `mul_le_mul_of_nonneg_right _ hr` to reduce the goal to its premises. Use `abs_nonneg B` as an intermediate fact.

Use `abs_nonneg A` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) = (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g` using `by ring`. Establish `hBa` using `le_abs_self B`. Establish `hAa` using `neg_abs_le A`.

Establish `hBn` using `abs_nonneg B`. Establish `hAn` using `abs_nonneg A`. Establish `hτ0 : 0 ≤ τ`. Establish `: 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g` using `mul_nonneg (by positivity) hr`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1` from `exists_lt_of_ciInf_lt (lt_add_one (redSize g))`. Establish `hinv` using `((E1.mahler_holds E n τ).2.1 γ g)`. Use `hinv.1 ?_` and prove the remaining obligations. Use `set h : GA E n := ratGL E n γ * g with hh`. Establish `hup : ∀ W, deg h W ≤ B + C * (2 + redSize g)`.

Introduce `W`. Establish `s` using `hC 1 h W`. Rewrite `s` using `[one_mul]`. Establish `t : C * (1 + logSize h) ≤ C * (2 + redSize g)` using `mul_le_mul_of_nonneg_left (by linarith) hC0`. Combine the linear relations using `[hB' W]`.

Use `⟨fun W => ?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1` into its components or cases. Rewrite using `[deg_finrank_zero h W h0, h0]`. Simplify using `[prof]`. Establish `hk : Module.finrank E W ≤ n`.

Use `Submodule.finrank_le W` as an intermediate fact. Simplify using `using this`. Use `le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s` using `hC h (h⁻¹ : GA E n) ⊤`.

Rewrite `s` using `[mul_inv_cancel, logSize_inv']`. Establish `t : C * (1 + logSize h) ≤ C * (2 + redSize g)` using `mul_le_mul_of_nonneg_left (by linarith) hC0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.inCut_pf :
    InCut := by
  intro E _ _ _ n
  obtain ⟨C, hC0, hC⟩ := E1.degRight E n
  obtain ⟨B, hB⟩ := (D1.degBdd E n).1 (1 : GA E n)
  have hB' : ∀ W, deg (1 : GA E n) W ≤ B := fun W => hB ⟨W, rfl⟩
  set A : ℝ := deg (1 : GA E n) ⊤ with hA
  refine ⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩
  have hr : 0 ≤ redSize g := ((E1.redBasic E n).2.1 g).1
  have hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g := by
    apply mul_le_mul_of_nonneg_right _ hr
    have := abs_nonneg B
    have := abs_nonneg A
    linarith
  have hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) =
      (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g := by ring
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hBn := abs_nonneg B
  have hAn := abs_nonneg A
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g := mul_nonneg (by positivity) hr
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1 :=
    exists_lt_of_ciInf_lt (lt_add_one (redSize g))
  have hinv := ((E1.mahler_holds E n τ).2.1 γ g)
  refine hinv.1 ?_
  set h : GA E n := ratGL E n γ * g with hh
  have hup : ∀ W, deg h W ≤ B + C * (2 + redSize g) := by
    intro W
    have s := hC 1 h W
    rw [one_mul] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith [hB' W]
  refine ⟨fun W => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1
    · rw [deg_finrank_zero h W h0, h0]
      simp [prof]
    · have hk : Module.finrank E W ≤ n := by
        have := Submodule.finrank_le W
        simpa using this
      refine le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))
      linarith
  · have s := hC h (h⁻¹ : GA E n) ⊤
    rw [mul_inv_cancel, logSize_inv'] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
