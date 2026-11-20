import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.NormalisedTranslate

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

/- English proof (translation)
Introduce `h0`. Substitute `h0` using the available equality. Establish `hz : lamOf D cc 0 = ⊥`. Unfold `lamOf`. Rewrite using `[AddSubgroup.closure_eq_bot_iff]`.

Introduce and unpack `w ⟨c, -, rfl⟩`. Simplify using the standard rewrite rules. Establish `h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup` using `B.L.ω₁_mem_lattice`. Rewrite `h1` using `[B.lat, hz, AddSubgroup.mem_bot]`. Establish `h2` using `B.L.indep.ne_zero 0`.

Conclude with `h2 (by simpa using h1)`.
-/
theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : δ ≠ 0 := by
  intro h0
  subst h0
  have hz : lamOf D cc 0 = ⊥ := by
    unfold lamOf
    rw [AddSubgroup.closure_eq_bot_iff]
    rintro w ⟨c, -, rfl⟩
    simp
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, hz, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M))`.
-/
theorem le_Qbar (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] : M ≤ Qbar := by
  intro x hx
  rw [mem_algebraicClosure_iff]
  exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M))

/- English proof (translation)
Take `⟨m, hm, -⟩` from `IO.self_int T hI hx`. Establish `hs` using `IO.sqrt_d_pos D`. Rewrite `hm` using `[GlobalTheory.GalTheta.Hf_nsmul_left, GlobalTheory.GalTheta.Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]`. Establish `hq : (p : ℝ) ^ (2 * k) * qH D T x = (m : ℝ)`. Unfold `qH`.

Move the coercions through the operations in `at hm`. Clear denominators, using `at hm` for the nonvanishing conditions. Rewrite using `[mul_comm 2 k, pow_mul]`. Take the linear combination `hm / 2`. Distinguish the cases in `h2 : p = 2`.

Unfold `wPh`. Rewrite using `[if_pos h2]`. Establish `hp0 : (p : ℝ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `e : qH D T x = (((m : ℚ) / (p : ℚ) ^ (2 * k) : ℚ) : ℝ)`. Use `push_cast`.

Rewrite using `[← hq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, Complex.ofReal_ratCast]`. Conclude with `GlobalTheory.ThetaAlgebraic.exp_rat_mem _`. Rewrite using `[GlobalTheory.GalThetaSign.wPh_eq D T x hp h2 hq]`.

Conclude with `zpow_mem (neg_mem (one_mem _)) _`.
-/
theorem wPh_mem {D : D7} (T : Tor D) {N N' : ℕ} {La' : AddSubgroup (VC D N N')} (hI : IO.HfInt T La')
    {p k : ℕ} (hp : p.Prime) {x : VC D N N'} (hx : p ^ k • x ∈ La') : wPh D T p x ∈ Qbar := by
  obtain ⟨m, hm, -⟩ := IO.self_int T hI hx
  have hs := IO.sqrt_d_pos D
  rw [GlobalTheory.GalTheta.Hf_nsmul_left, GlobalTheory.GalTheta.Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul,
    ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hm
  have hq : (p : ℝ) ^ (2 * k) * qH D T x = (m : ℝ) := by
    unfold qH
    push_cast at hm
    field_simp at hm
    rw [mul_comm 2 k, pow_mul]
    linear_combination hm / 2
  by_cases h2 : p = 2
  · unfold wPh
    rw [if_pos h2]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e : qH D T x = (((m : ℚ) / (p : ℚ) ^ (2 * k) : ℚ) : ℝ) := by
      push_cast
      rw [← hq]
      field_simp
    rw [e, Complex.ofReal_ratCast]
    exact GlobalTheory.ThetaAlgebraic.exp_rat_mem _
  · rw [GlobalTheory.GalThetaSign.wPh_eq D T x hp h2 hq]
    exact zpow_mem (neg_mem (one_mem _)) _

/- English proof (translation)
Take `⟨a, b, -, h⟩` from `hI w hw _ hx`. Establish `hb : (Hf D T w (n • x)).im = b` using `by rw [h]; simp`. Rewrite `hb` using `[GlobalTheory.GalTheta.Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.im_ofReal_mul]`. Establish `hn0 : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Establish `e : (Hf D T w x).im = (((b : ℚ) / (n : ℚ) : ℚ) : ℝ)`.

Use `push_cast`. Rewrite using `[← hb]`. Clear the denominators using the available nonvanishing facts. Unfold `kap`. Rewrite using `[e, Complex.ofReal_ratCast]`.

Use `GlobalTheory.ThetaAlgebraic.exp_rat_mem (-2 * ((b : ℚ) / (n : ℚ))) using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kap_mem {D : D7} (T : Tor D) {N N' : ℕ} {La' : AddSubgroup (VC D N N')} (hI : IO.HfInt T La')
    {n : ℕ} (hn : n ≠ 0) {w x : VC D N N'} (hw : w ∈ La') (hx : n • x ∈ La') : kap D T w x ∈ Qbar := by
  obtain ⟨a, b, -, h⟩ := hI w hw _ hx
  have hb : (Hf D T w (n • x)).im = b := by rw [h]; simp
  rw [GlobalTheory.GalTheta.Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.im_ofReal_mul] at hb
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e : (Hf D T w x).im = (((b : ℚ) / (n : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← hb]
    field_simp
  unfold kap
  rw [e, Complex.ofReal_ratCast]
  convert GlobalTheory.ThetaAlgebraic.exp_rat_mem (-2 * ((b : ℚ) / (n : ℚ))) using 2
  push_cast
  ring

/- English proof (translation)
Introduce `D cc δ B χ hcc hδ hV N N' L L' hA`. Take `⟨hTh, -, M, hM, hC⟩` from `hV N N' L L' hA`. Establish `hq : CoefIn D (B.eNat χ N N' L L') Qbar` using `fun α => le_Qbar M (hC α)`. Establish `hI` using `hermitian_form_integral_values D cc hcc δ hδ (delta_ne_zero B) N N' L L' hA`. Establish `h1 : ∀ t : VC D N N', (∃ m : ℕ, 0 < m ∧ m • t ∈ La D (tor0 D cc δ) L L') → AlgEntire D (U D (tor0 D cc δ) t (B.eNat χ N N' L L'))` using `fun t ht => ⟨IO.U_diff _ t hTh.1, GlobalTheory.AlgTranslate.coefIn_translate D cc δ ⟨hcc, hδ⟩ N N' L L' hA.2.2.1 hA.2.2.2 _ hTh hq t ht⟩`.

Use `⟨h1, fun p k hp x hx => ⟨?_, fun w hw => kap_mem _ hI (pow_ne_zero k hp.ne_zero) hw hx⟩⟩` and prove the remaining obligations. Take `⟨hd, hc⟩` from `h1 x ⟨p ^ k, pow_pos hp.pos k, hx⟩`. Use `⟨hd.const_mul _, fun α => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.ThetaConj.taylor_mul D (wPh D (tor0 D cc δ) p x) hd α`. Conclude with `e ▸ mul_mem (wPh_mem _ hI hp hx) (hc α)`.
-/
theorem algEntire_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → (∀ t : VC D N N', (∃ m : ℕ, 0 < m ∧ m • t ∈ La D (tor0 D cc δ) L L') → AlgEntire D (U D (tor0 D cc δ) t (B.eNat χ N N' L L'))) ∧ ∀ (p k : ℕ), p.Prime → ∀ x : VC D N N', p ^ k • x ∈ La D (tor0 D cc δ) L L' → AlgEntire D (Wop D (tor0 D cc δ) p x (B.eNat χ N N' L L')) ∧ ∀ w ∈ La D (tor0 D cc δ) L L', kap D (tor0 D cc δ) w x ∈ Qbar := by
  intro D cc δ B χ hcc hδ hV N N' L L' hA
  obtain ⟨hTh, -, M, hM, hC⟩ := hV N N' L L' hA
  have hq : CoefIn D (B.eNat χ N N' L L') Qbar := fun α => le_Qbar M (hC α)
  have hI := hermitian_form_integral_values D cc hcc δ hδ (delta_ne_zero B) N N' L L' hA
  have h1 : ∀ t : VC D N N', (∃ m : ℕ, 0 < m ∧ m • t ∈ La D (tor0 D cc δ) L L') →
      AlgEntire D (U D (tor0 D cc δ) t (B.eNat χ N N' L L')) := fun t ht =>
    ⟨IO.U_diff _ t hTh.1,
      GlobalTheory.AlgTranslate.coefIn_translate D cc δ ⟨hcc, hδ⟩ N N' L L' hA.2.2.1 hA.2.2.2 _ hTh hq t ht⟩
  refine ⟨h1, fun p k hp x hx => ⟨?_, fun w hw => kap_mem _ hI (pow_ne_zero k hp.ne_zero) hw hx⟩⟩
  obtain ⟨hd, hc⟩ := h1 x ⟨p ^ k, pow_pos hp.pos k, hx⟩
  refine ⟨hd.const_mul _, fun α => ?_⟩
  have e := GlobalTheory.ThetaConj.taylor_mul D (wPh D (tor0 D cc δ) p x) hd α
  exact e ▸ mul_mem (wPh_mem _ hI hp hx) (hc α)

end GlobalTheory.NormalisedTranslate
