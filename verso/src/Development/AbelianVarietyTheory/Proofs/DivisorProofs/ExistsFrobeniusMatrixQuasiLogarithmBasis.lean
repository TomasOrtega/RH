import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogLiftPdivGroupFrameStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

section Div

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} {d : ℕ}

/- English proof (translation)
Introduce `α` and use `by obtain ⟨b, hb, e⟩ := hf α exact ⟨b, h hb, e⟩`.
-/
theorem in_mono {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) : In N' f :=
  fun α => by
    obtain ⟨b, hb, e⟩ := hf α
    exact ⟨b, h hb, e⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨b, -, e⟩ := hf α refine ⟨b * p, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, ?_⟩ rw [coeff_smul, e, ← map_mul, mul_comm]`.
-/
theorem in_span_smul (p : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (Ideal.span {p}) (algebraMap B Q p • f) := fun α => by
  obtain ⟨b, -, e⟩ := hf α
  refine ⟨b * p, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, ?_⟩
  rw [coeff_smul, e, ← map_mul, mul_comm]

/- English proof (translation)
Take `⟨b, hb, e⟩` from `h`. Take `⟨b', rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Use `⟨b', Submodule.mem_top, ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_mul, ← mul_assoc, mul_comm c, mul_assoc, hc, mul_one]`.
-/
theorem div_coeff (p : B) {c : Q} (hc : c * algebraMap B Q p = 1) {q : Q}
    (h : ∃ b ∈ Ideal.span {p}, q = algebraMap B Q b) : ∃ b ∈ (⊤ : Ideal B), c * q = algebraMap B Q b := by
  obtain ⟨b, hb, e⟩ := h
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b', Submodule.mem_top, ?_⟩
  rw [e, map_mul, ← mul_assoc, mul_comm c, mul_assoc, hc, mul_one]

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `hf`. Establish `hμ' : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by`. Simplify using `[up, hμ i]`. Use `⟨?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]`.

Use `div_coeff p hc (h1 i)` as an intermediate fact. Simplify `this` using `[lin, coeff_smul]`. Rewrite using `[formalCoboundary_smul hμ']`. Introduce `α`. Use `div_coeff p hc (h2 α)` as an intermediate fact.

Simplify `this` using `[coeff_smul]`.
-/
theorem ql_div (p : B) {c : Q} (hc : c * algebraMap B Q p = 1)
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ (Ideal.span {p}) f) : QL μ ⊤ (c • f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, hμ i]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
      mul_zero]
  · have := div_coeff p hc (h1 i)
    simpa [lin, coeff_smul] using this
  · rw [formalCoboundary_smul hμ']
    intro α
    have := div_coeff p hc (h2 α)
    simpa [coeff_smul] using this

/- English proof (translation)
Simplify using `only [comb, Finset.smul_sum, map_mul, mul_comm, mul_smul]`.
-/
theorem comb_mul {ι : Type} [Fintype ι] (p : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun l => b l * p) e = algebraMap B Q p • comb b e := by
  simp only [comb, Finset.smul_sum, map_mul, mul_comm, mul_smul]

end Div

end GlobalTheory.QLog

namespace GlobalTheory.QLog

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hm k e hB hA`. Establish `key` using `fun f hf => GlobalTheory.T.quasi_log_lift_pdiv_group_frame p C v O hv ε hε F G d c μ' hL hm f hf`. Take `⟨u, hu⟩` from `F.frame.unit_p`. Use `set pinv : F.Q := ((u⁻¹ : F.Qˣ) : F.Q) with hpinv`. Establish `hpB : (p : F.Q) = algebraMap F.B F.Q (p : F.B)` using `(map_natCast _ _).symm`.

Establish `hc : pinv * algebraMap F.B F.Q (p : F.B) = 1`. Rewrite using `[← hpB, ← hu, hpinv, Units.inv_mul]`. Establish `hc' : algebraMap F.B F.Q (p : F.B) * pinv = 1` using `by rw [mul_comm, hc]`. Establish `h1 : ∀ i', ∃ b : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (pinv • frob p F.s (e (Sum.inl i')) - comb b e)` using `fun i' => (hB.2 _ (ql_div (p : F.B) hc hL.const ((key _ (hB.1 _)).2 (hA i').1))).exists`. Establish `h2 : ∀ j, ∃ b : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (e (Sum.inr j)) - comb b e)` using `fun j => (hB.2 _ (key _ (hB.1 _)).1).exists`.

Use `choose b1 hb1 using h1`. Use `choose b2 hb2 using h2`. Use `⟨Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i, ?_⟩` and prove the remaining obligations. Introduce `i`. Break down `i with i' | j` into its components or cases.

Establish `hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) * blk d k (p : F.B) 1) l (Sum.inl i')) = fun l => b1 i' l * p`. Use function extensionality and compare the values at `l`. Simplify using `[blk, Matrix.mul_diagonal]`. Rewrite using `[hcol, comb_mul]`. Establish `heq : frob p F.s (e (Sum.inl i')) - algebraMap F.B F.Q (p : F.B) • comb (b1 i') e = algebraMap F.B F.Q (p : F.B) • (pinv • frob p F.s (e (Sum.inl i')) - comb (b1 i') e)`.

Rewrite using `[smul_sub, smul_smul, hc', one_smul]`. Rewrite using `[heq]`. Establish `hp` using `in_span_smul (p : F.B) (hb1 i')`. Conclude with `⟨in_mono le_top hp, fun _ _ => hp⟩`. Establish `hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) * blk d k (p : F.B) 1) l (Sum.inr j)) = fun l => b2 j l`.

Use function extensionality and compare the values at `l`. Simplify using `[blk, Matrix.mul_diagonal]`. Rewrite using `[hcol]`. Conclude with `⟨hb2 j, fun _ h => absurd h (by simp)⟩`.
-/
theorem exists_frob_matrix : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∃ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, ∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hm k e hB hA
  have key := fun f hf => GlobalTheory.T.quasi_log_lift_pdiv_group_frame p C v O hv ε hε F G d c μ' hL hm f hf
  obtain ⟨u, hu⟩ := F.frame.unit_p
  set pinv : F.Q := ((u⁻¹ : F.Qˣ) : F.Q) with hpinv
  have hpB : (p : F.Q) = algebraMap F.B F.Q (p : F.B) := (map_natCast _ _).symm
  have hc : pinv * algebraMap F.B F.Q (p : F.B) = 1 := by
    rw [← hpB, ← hu, hpinv, Units.inv_mul]
  have hc' : algebraMap F.B F.Q (p : F.B) * pinv = 1 := by rw [mul_comm, hc]
  have h1 : ∀ i', ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (pinv • frob p F.s (e (Sum.inl i')) - comb b e) := fun i' =>
    (hB.2 _ (ql_div (p : F.B) hc hL.const
      ((key _ (hB.1 _)).2 (hA i').1))).exists
  have h2 : ∀ j, ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (frob p F.s (e (Sum.inr j)) - comb b e) := fun j =>
    (hB.2 _ (key _ (hB.1 _)).1).exists
  choose b1 hb1 using h1
  choose b2 hb2 using h2
  refine ⟨Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i, ?_⟩
  intro i
  rcases i with i' | j
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inl i')) = fun l => b1 i' l * p := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol, comb_mul]
    have heq : frob p F.s (e (Sum.inl i')) - algebraMap F.B F.Q (p : F.B) • comb (b1 i') e =
        algebraMap F.B F.Q (p : F.B) • (pinv • frob p F.s (e (Sum.inl i')) - comb (b1 i') e) := by
      rw [smul_sub, smul_smul, hc', one_smul]
    rw [heq]
    have hp := in_span_smul (p : F.B) (hb1 i')
    exact ⟨in_mono le_top hp, fun _ _ => hp⟩
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inr j)) = fun l => b2 j l := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol]
    exact ⟨hb2 j, fun _ h => absurd h (by simp)⟩

end GlobalTheory.QLog
