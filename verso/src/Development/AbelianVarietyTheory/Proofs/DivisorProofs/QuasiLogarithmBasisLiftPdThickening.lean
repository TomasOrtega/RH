import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageGenerationStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependentStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BasisLift

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `[comb, map_add, add_smul, Finset.sum_add_distrib]`.
-/
theorem comb_add (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b + c) e = comb b e + comb c e := by
  simp [comb, map_add, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[comb, map_sub, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem comb_sub (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b - c) e = comb b e - comb c e := by
  simp [comb, map_sub, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[comb]`.
-/
theorem comb_zero (e : ι → MvPowerSeries σ Q) : comb (0 : ι → B) e = 0 := by
  simp [comb]

/- English proof (translation)
Simplify using `[comb, map_mul, mul_smul, Finset.smul_sum]`.
-/
theorem comb_mul (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => r * b i) e = algebraMap B Q r • comb b e := by
  simp [comb, map_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Simplify using `only [mul_comm _ r]`. Conclude with `comb_mul r b e`.
-/
theorem comb_mul_right (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => b i * r) e = algebraMap B Q r • comb b e := by
  simp only [mul_comm _ r]; exact comb_mul r b e

/- English proof (translation)
Simplify using `only [comb, map_sum, coeff_smul]`.
-/
theorem coeff_comb (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ i, algebraMap B Q (b i) * coeff α (e i) := by
  simp only [comb, map_sum, coeff_smul]

end GlobalTheory.BasisLift

open GlobalTheory.BasisLift in

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ hF d μ hL C _ _ hC Θ hΘ ι _ e he hB hch`. Take `⟨u, hu⟩` from `hF.unit_p`. Establish `hmapP : algebraMap B Q (p : B) = (p : Q)` using `map_natCast _ _`. Establish `hconst : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by`. Simplify using `[up, constantCoeff_map, hL.const i]`.

Establish `ql0 : ∀ N : Ideal B, QL μ N (0 : MvPowerSeries (Fin d) Q)`. Introduce `N`. Use `⟨by simp, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩` and prove the remaining obligations. Establish `h0` using `formalCoboundary_smul hconst (0 : Q) (0 : MvPowerSeries (Fin d) Q)`. Simplify using `only [zero_smul] at h0`.

Simplify using `[h0]`. Establish `hsm : ∀ n : ℕ, (Ideal.span {(p : B)} ^ n • ⊤ : Submodule B B) = Ideal.span {(p : B) ^ n}`. Introduce `n`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Establish `key : ∀ t ∈ Ideal.span {(p : B)}, ∃ t' : B, (↑u⁻¹ : Q) * algebraMap B Q t = algebraMap B Q t'`.

Introduce `t ht`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 ht`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hmapP, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]`. Establish `chainE : ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → ∀ f, QL μ ⊤ f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s ∧ QL μ N (f - comb b e - s)`.

Introduce `N hN`. Proceed by induction on `hN with`. Consider the case `refl => intro f hf; exact ⟨0, 0, fun α => ⟨0, trivial, by simp⟩, by simpa [comb_zero] using hf⟩`. Consider the case `tail _ hst ih`. Introduce `f hf`.

Take `⟨b, s, hs, hq⟩` from `ih f hf`. Take `⟨b', s', -, hs', hq'⟩` from `GlobalTheory.T.quasiLogarithm_devissage_generation_step p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst _ hq`. Use `⟨b + b', s + s', ?_, ?_⟩` and prove the remaining obligations. Introduce `α`. Take `⟨x, -, hx⟩` from `hs α`.

Take `⟨y, -, hy⟩` from `hs' α`. Conclude with `⟨x + y, trivial, by rw [map_add, hx, hy, map_add]⟩`. Rewrite using `[comb_add]`. Use `hq' using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Establish `divP : ∀ h : MvPowerSeries (Fin d) Q, QL μ (Ideal.span {(p : B)}) h → QL μ ⊤ ((↑u⁻¹ : Q) • h) ∧ h = (p : Q) • ((↑u⁻¹ : Q) • h)`. Introduce `h ⟨h0, hl, hc⟩`. Use `⟨⟨?_, fun i => ?_, fun α => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]`. Take `⟨t, ht, he'⟩` from `hl i`.

Take `⟨t', ht'⟩` from `key t ht`. Use `⟨t', trivial, ?_⟩` and prove the remaining obligations. Simplify using `only [lin, coeff_smul] at he' ⊢`. Rewrite using `[he', ht']`. Take `⟨t, ht, he'⟩` from `hc α`.

Take `⟨t', ht'⟩` from `key t ht`. Use `⟨t', trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[formalCoboundary_smul hconst, coeff_smul, he', ht']`. Rewrite using `[smul_smul, ← hu, Units.mul_inv, one_smul]`. Establish `E1 : ∀ f : {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, ∃ (b : ι → B) (s g : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s ∧ QL μ ⊤ g ∧ f.1 = comb b e + s + (p : Q) • g`.

Introduce `⟨f, hf⟩`. Take `⟨b, s, hs, hq⟩` from `chainE _ hch f hf`. Take `⟨hg, hgq⟩` from `divP _ hq`. Conclude with `⟨b, s, _, hs, hg, by rw [← hgq]; abel⟩`. Use `choose bF sF gF hsF hgF heqF using E1`.

Establish `V : ∀ α : Fin d →₀ ℕ, ∃ v : ℕ, ∀ g, QL μ ⊤ g → (p : Q) ^ v * coeff α g ∈ (algebraMap B Q).range`. Introduce `α`. Distinguish the cases in `hα : α = 0`. Use `⟨0, fun g hg => ⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hα, coeff_zero_eq_constantCoeff_apply, hg.1]`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, α i ≠ 0 := by`. Assume the negation of the conclusion as `h; push_neg at h; exact hα (Finsupp.ext fun i => by simp [h i])`. Take `⟨v, n, hn, hαi⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hi p (Fact.out : p.Prime).one_lt.ne'`. Establish `hcop : Nat.Coprime n p` using `Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)`.

Take `⟨w, hw⟩` from `hF.unit_coprime n hcop`. Use `⟨v, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨t, -, ht⟩` from `GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hL ⊤ g hg α i`. Use `⟨↑w⁻¹ * t, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[hαi]`.

Move the coercions through the operations in `at ht`. Rewrite using `[map_mul, ← ht]`. Establish `hw1 : algebraMap B Q (↑w⁻¹) * (n : Q) = 1`. Rewrite using `[← map_natCast (algebraMap B Q) n, ← map_mul, ← hw, Units.inv_mul, map_one]`. Take the linear combination `((p : Q) ^ v * coeff α g) * hw1`.

Establish `chainU : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), comb c e = s → ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → In (⊤ : Ideal B) s → (∀ i, c i ∈ N) ∧ In N s`. Introduce `c s hcs N hN hs`. Proceed by induction on `hN with`. Consider the case `refl => exact ⟨fun _ => trivial, hs⟩`. Consider the case `tail _ hst ih`.

Conclude with `GlobalTheory.T.quasiLogarithm_devissage_step_independent p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst c s ih.1 ih.2 (by rw [hcs, sub_self]; exact ql0 _)`. Establish `U1 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → ∃ (c' : ι → B) (s' : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s' ∧ comb c' e = s' ∧ ∀ i, c i = c' i * p`. Introduce `c s hs hcs`. Take `⟨hc, hsp⟩` from `chainU c s hcs _ hch hs`. Use `choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)`.

Use `⟨c', (↑u⁻¹ : Q) • s, ?_, ?_, fun i => (hc' i).symm⟩` and prove the remaining obligations. Introduce `α`. Take `⟨t, ht, h1⟩` from `hsp α`. Take `⟨t', h2⟩` from `key t ht`. Conclude with `⟨t', trivial, by rw [coeff_smul, h1, h2]⟩`.

Establish `hc2 : c = fun i => c' i * p` using `funext fun i => (hc' i).symm`. Rewrite using `[← hcs, hc2, comb_mul_right, smul_smul, hmapP, ← hu, Units.inv_mul, one_smul]`. Establish `U2 : ∀ K (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → ∀ i, c i ∈ Ideal.span {(p : B) ^ K}`. Introduce `K`. Proceed by induction on `K with`.

Consider the case `zero => intro c s _ _ i`. Simplify using the standard rewrite rules. Consider the case `succ K ih`. Introduce `c s hs hcs i`. Take `⟨c', s', hs', hcs', hc⟩` from `U1 c s hs hcs`.

Rewrite using `[hc i, pow_succ]`. Conclude with `Ideal.mem_span_singleton.2 (mul_dvd_mul_right (Ideal.mem_span_singleton.1 (ih c' s' hs' hcs' i)) _)`. Establish `U3 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → c = 0`. Introduce `c s hs hcs`. Use function extensionality and compare the values at `i`.

Use `hF.complete.toIsHausdorff.haus (c i) fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, hsm]`. Conclude with `U2 n c s hs hcs i`. Use `⟨he, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨Fs, hF0, hFs⟩ : ∃ Fs : ℕ → {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, Fs 0 = ⟨f, hf⟩ ∧ ∀ k, Fs (k + 1) = ⟨gF (Fs k), hgF (Fs k)⟩` from `⟨fun k => Nat.rec ⟨f, hf⟩ (fun _ y => ⟨gF y, hgF y⟩) k, rfl, fun _ => rfl⟩`.

Take `⟨x, hx⟩ : ∃ x : ℕ → ι → B, ∀ K i, x K i = ∑ k ∈ Finset.range K, (p : B) ^ k * bF (Fs k) i` from `⟨_, fun _ _ => rfl⟩`. Establish `hrec : ∀ K, ∃ S, In (⊤ : Ideal B) S ∧ f = comb (x K) e + S + (p : Q) ^ K • (Fs K).1`. Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`.

Establish `hx0 : x 0 = 0` using `funext fun i => by simp [hx]`. Use `⟨0, fun α => ⟨0, trivial, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hx0, comb_zero, hF0]`. Simplify using the standard rewrite rules. Consider the case `succ K ih`.

Take `⟨S, hS, hfe⟩` from `ih`. Use `⟨S + (p : Q) ^ K • sF (Fs K), ?_, ?_⟩` and prove the remaining obligations. Introduce `α`. Take `⟨a, -, ha⟩` from `hS α`. Take `⟨c, -, hc⟩` from `hsF (Fs K) α`.

Conclude with `⟨a + p ^ K * c, trivial, by simp [coeff_smul, ha, hc, map_add, map_mul, map_pow, map_natCast]⟩`. Establish `h1 : x (K + 1) = x K + fun i => (p : B) ^ K * bF (Fs K) i`. Use function extensionality and compare the values at `i`. Simplify using `[hx, Finset.sum_range_succ]`. Establish `h2 : (Fs (K + 1)).1 = gF (Fs K)` using `by rw [hFs]`.

Rewrite using `[h1, comb_add, comb_mul, h2, map_pow, map_natCast]`. Use `conv_lhs => rw [hfe, heqF (Fs K)]`. Simplify using `only [smul_add, smul_smul, ← pow_succ]`. Normalize the expressions using the abelian group laws. Establish `hcau : ∀ m n, m ≤ n → ∀ i, x n i - x m i ∈ Ideal.span {(p : B) ^ m}`.

Introduce `m n hmn i`. Rewrite using `[hx, hx, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]`. Use `Ideal.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Conclude with `Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _)`. Establish `hlim : ∀ i, ∃ L : B, ∀ n, x n i - L ∈ Ideal.span {(p : B) ^ n}`.

Introduce `i`. Take `⟨L, hL'⟩` from `hF.complete.toIsPrecomplete.prec (f := fun n => x n i) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, hsm, ← neg_sub]`. Conclude with `neg_mem (hcau m n hmn i))`. Conclude with `⟨L, fun n => by have := hL' n; rwa [SModEq.sub_mem, hsm] at this⟩`.

Use `choose L hLx using hlim`. Establish `hIn : In (⊤ : Ideal B) (f - comb L e)`. Introduce `α`. Take `⟨v, hv⟩` from `V α`. Take `⟨S, hS, hfe⟩` from `hrec v`.

Use `choose c hc using fun i => Ideal.mem_span_singleton'.1 (hLx i v)`. Establish `hmem : coeff α (f - comb L e) ∈ (algebraMap B Q).range`. Rewrite using `[hfe]`. Establish `e1 : comb (x v) e + S + (p : Q) ^ v • (Fs v).1 - comb L e = (comb (x v) e - comb L e) + S + (p : Q) ^ v • (Fs v).1` using `by abel`. Rewrite using `[e1, ← comb_sub, map_add, map_add, coeff_comb, coeff_smul]`.

Use `add_mem (add_mem (Subring.sum_mem _ fun i _ => ?_) ?_) (hv _ (Fs v).2)` and prove the remaining obligations. Rewrite using `[show (x v - L) i = c i * (p : B) ^ v from (hc i).symm, show algebraMap B Q (c i * (p : B) ^ v) * coeff α (e i) = algebraMap B Q (c i) * ((p : Q) ^ v * coeff α (e i)) by`. Rewrite using `[map_mul, map_pow, map_natCast, mul_assoc]]`. Conclude with `Subring.mul_mem _ ⟨c i, rfl⟩ (hv _ (he i))`. Take `⟨a, -, ha⟩` from `hS α`.

Conclude with `⟨a, ha.symm⟩`. Take `⟨b, hb⟩` from `hmem`. Conclude with `⟨b, trivial, hb.symm⟩`. Use `⟨L, hIn, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hs : In (⊤ : Ideal B) (comb (y - L) e)`.

Introduce `α`. Take `⟨a, -, ha⟩` from `hIn α`. Take `⟨a', -, ha'⟩` from `hy α`. Use `⟨a - a', trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← ha, ← ha', ← map_sub, comb_sub]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Conclude with `sub_eq_zero.1 (U3 _ _ hs rfl)`.
-/
theorem GlobalTheory.basis_lift : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL C _ _ hC Θ hΘ ι _ e he hB hch
  obtain ⟨u, hu⟩ := hF.unit_p
  have hmapP : algebraMap B Q (p : B) = (p : Q) := map_natCast _ _
  have hconst : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hL.const i]
  have ql0 : ∀ N : Ideal B, QL μ N (0 : MvPowerSeries (Fin d) Q) := by
    intro N
    refine ⟨by simp, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
    have h0 := formalCoboundary_smul hconst (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simp only [zero_smul] at h0
    simp [h0]
  have hsm : ∀ n : ℕ, (Ideal.span {(p : B)} ^ n • ⊤ : Submodule B B) = Ideal.span {(p : B) ^ n} := by
    intro n; rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have key : ∀ t ∈ Ideal.span {(p : B)}, ∃ t' : B, (↑u⁻¹ : Q) * algebraMap B Q t = algebraMap B Q t' := by
    intro t ht
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    refine ⟨a, ?_⟩
    rw [map_mul, hmapP, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

  have chainE : ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N →
      ∀ f, QL μ ⊤ f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q),
        In (⊤ : Ideal B) s ∧ QL μ N (f - comb b e - s) := by
    intro N hN
    induction hN with
    | refl => intro f hf; exact ⟨0, 0, fun α => ⟨0, trivial, by simp⟩, by simpa [comb_zero] using hf⟩
    | tail _ hst ih =>
      intro f hf
      obtain ⟨b, s, hs, hq⟩ := ih f hf
      obtain ⟨b', s', -, hs', hq'⟩ := GlobalTheory.T.quasiLogarithm_devissage_generation_step p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst _ hq
      refine ⟨b + b', s + s', ?_, ?_⟩
      · intro α
        obtain ⟨x, -, hx⟩ := hs α
        obtain ⟨y, -, hy⟩ := hs' α
        exact ⟨x + y, trivial, by rw [map_add, hx, hy, map_add]⟩
      · rw [comb_add]; convert hq' using 1; abel

  have divP : ∀ h : MvPowerSeries (Fin d) Q, QL μ (Ideal.span {(p : B)}) h →
      QL μ ⊤ ((↑u⁻¹ : Q) • h) ∧ h = (p : Q) • ((↑u⁻¹ : Q) • h) := by
    intro h ⟨h0, hl, hc⟩
    refine ⟨⟨?_, fun i => ?_, fun α => ?_⟩, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]
    · obtain ⟨t, ht, he'⟩ := hl i
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      simp only [lin, coeff_smul] at he' ⊢
      rw [he', ht']
    · obtain ⟨t, ht, he'⟩ := hc α
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      rw [formalCoboundary_smul hconst, coeff_smul, he', ht']
    · rw [smul_smul, ← hu, Units.mul_inv, one_smul]
  have E1 : ∀ f : {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, ∃ (b : ι → B) (s g : MvPowerSeries (Fin d) Q),
      In (⊤ : Ideal B) s ∧ QL μ ⊤ g ∧ f.1 = comb b e + s + (p : Q) • g := by
    intro ⟨f, hf⟩
    obtain ⟨b, s, hs, hq⟩ := chainE _ hch f hf
    obtain ⟨hg, hgq⟩ := divP _ hq
    exact ⟨b, s, _, hs, hg, by rw [← hgq]; abel⟩
  choose bF sF gF hsF hgF heqF using E1

  have V : ∀ α : Fin d →₀ ℕ, ∃ v : ℕ, ∀ g, QL μ ⊤ g → (p : Q) ^ v * coeff α g ∈ (algebraMap B Q).range := by
    intro α
    by_cases hα : α = 0
    · refine ⟨0, fun g hg => ⟨0, ?_⟩⟩
      rw [hα, coeff_zero_eq_constantCoeff_apply, hg.1]; simp
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push_neg at h; exact hα (Finsupp.ext fun i => by simp [h i])
      obtain ⟨v, n, hn, hαi⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Fact.out : p.Prime).one_lt.ne'
      have hcop : Nat.Coprime n p := Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)
      obtain ⟨w, hw⟩ := hF.unit_coprime n hcop
      refine ⟨v, fun g hg => ?_⟩
      obtain ⟨t, -, ht⟩ := GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hL ⊤ g hg α i
      refine ⟨↑w⁻¹ * t, ?_⟩
      rw [hαi] at ht
      push_cast at ht
      rw [map_mul, ← ht]
      have hw1 : algebraMap B Q (↑w⁻¹) * (n : Q) = 1 := by
        rw [← map_natCast (algebraMap B Q) n, ← map_mul, ← hw, Units.inv_mul, map_one]
      linear_combination ((p : Q) ^ v * coeff α g) * hw1

  have chainU : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), comb c e = s → ∀ N,
      Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → In (⊤ : Ideal B) s →
        (∀ i, c i ∈ N) ∧ In N s := by
    intro c s hcs N hN hs
    induction hN with
    | refl => exact ⟨fun _ => trivial, hs⟩
    | tail _ hst ih =>
      exact GlobalTheory.T.quasiLogarithm_devissage_step_independent p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst c s ih.1 ih.2
        (by rw [hcs, sub_self]; exact ql0 _)
  have U1 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∃ (c' : ι → B) (s' : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s' ∧ comb c' e = s' ∧
        ∀ i, c i = c' i * p := by
    intro c s hs hcs
    obtain ⟨hc, hsp⟩ := chainU c s hcs _ hch hs
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    refine ⟨c', (↑u⁻¹ : Q) • s, ?_, ?_, fun i => (hc' i).symm⟩
    · intro α
      obtain ⟨t, ht, h1⟩ := hsp α
      obtain ⟨t', h2⟩ := key t ht
      exact ⟨t', trivial, by rw [coeff_smul, h1, h2]⟩
    · have hc2 : c = fun i => c' i * p := funext fun i => (hc' i).symm
      rw [← hcs, hc2, comb_mul_right, smul_smul, hmapP, ← hu, Units.inv_mul, one_smul]
  have U2 : ∀ K (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∀ i, c i ∈ Ideal.span {(p : B) ^ K} := by
    intro K
    induction K with
    | zero => intro c s _ _ i; simp
    | succ K ih =>
      intro c s hs hcs i
      obtain ⟨c', s', hs', hcs', hc⟩ := U1 c s hs hcs
      rw [hc i, pow_succ]
      exact Ideal.mem_span_singleton.2 (mul_dvd_mul_right (Ideal.mem_span_singleton.1 (ih c' s' hs' hcs' i)) _)
  have U3 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → c = 0 := by
    intro c s hs hcs; funext i
    refine hF.complete.toIsHausdorff.haus (c i) fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hsm]; exact U2 n c s hs hcs i
  refine ⟨he, fun f hf => ?_⟩

  obtain ⟨Fs, hF0, hFs⟩ : ∃ Fs : ℕ → {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f},
      Fs 0 = ⟨f, hf⟩ ∧ ∀ k, Fs (k + 1) = ⟨gF (Fs k), hgF (Fs k)⟩ :=
    ⟨fun k => Nat.rec ⟨f, hf⟩ (fun _ y => ⟨gF y, hgF y⟩) k, rfl, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ι → B, ∀ K i, x K i = ∑ k ∈ Finset.range K, (p : B) ^ k * bF (Fs k) i :=
    ⟨_, fun _ _ => rfl⟩
  have hrec : ∀ K, ∃ S, In (⊤ : Ideal B) S ∧ f = comb (x K) e + S + (p : Q) ^ K • (Fs K).1 := by
    intro K
    induction K with
    | zero =>
      have hx0 : x 0 = 0 := funext fun i => by simp [hx]
      refine ⟨0, fun α => ⟨0, trivial, by simp⟩, ?_⟩
      rw [hx0, comb_zero, hF0]; simp
    | succ K ih =>
      obtain ⟨S, hS, hfe⟩ := ih
      refine ⟨S + (p : Q) ^ K • sF (Fs K), ?_, ?_⟩
      · intro α
        obtain ⟨a, -, ha⟩ := hS α
        obtain ⟨c, -, hc⟩ := hsF (Fs K) α
        exact ⟨a + p ^ K * c, trivial, by simp [coeff_smul, ha, hc, map_add, map_mul, map_pow, map_natCast]⟩
      · have h1 : x (K + 1) = x K + fun i => (p : B) ^ K * bF (Fs K) i := by
          funext i; simp [hx, Finset.sum_range_succ]
        have h2 : (Fs (K + 1)).1 = gF (Fs K) := by rw [hFs]
        rw [h1, comb_add, comb_mul, h2, map_pow, map_natCast]
        conv_lhs => rw [hfe, heqF (Fs K)]
        simp only [smul_add, smul_smul, ← pow_succ]
        abel
  have hcau : ∀ m n, m ≤ n → ∀ i, x n i - x m i ∈ Ideal.span {(p : B) ^ m} := by
    intro m n hmn i
    rw [hx, hx, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    exact Ideal.mem_span_singleton.2
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _)
  have hlim : ∀ i, ∃ L : B, ∀ n, x n i - L ∈ Ideal.span {(p : B) ^ n} := by
    intro i
    obtain ⟨L, hL'⟩ := hF.complete.toIsPrecomplete.prec (f := fun n => x n i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_sub]; exact neg_mem (hcau m n hmn i))
    exact ⟨L, fun n => by have := hL' n; rwa [SModEq.sub_mem, hsm] at this⟩
  choose L hLx using hlim
  have hIn : In (⊤ : Ideal B) (f - comb L e) := by
    intro α
    obtain ⟨v, hv⟩ := V α
    obtain ⟨S, hS, hfe⟩ := hrec v
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hLx i v)
    have hmem : coeff α (f - comb L e) ∈ (algebraMap B Q).range := by
      rw [hfe]
      have e1 : comb (x v) e + S + (p : Q) ^ v • (Fs v).1 - comb L e =
          (comb (x v) e - comb L e) + S + (p : Q) ^ v • (Fs v).1 := by abel
      rw [e1, ← comb_sub, map_add, map_add, coeff_comb, coeff_smul]
      refine add_mem (add_mem (Subring.sum_mem _ fun i _ => ?_) ?_) (hv _ (Fs v).2)
      · rw [show (x v - L) i = c i * (p : B) ^ v from (hc i).symm,
          show algebraMap B Q (c i * (p : B) ^ v) * coeff α (e i) =
            algebraMap B Q (c i) * ((p : Q) ^ v * coeff α (e i)) by
              rw [map_mul, map_pow, map_natCast, mul_assoc]]
        exact Subring.mul_mem _ ⟨c i, rfl⟩ (hv _ (he i))
      · obtain ⟨a, -, ha⟩ := hS α; exact ⟨a, ha.symm⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, trivial, hb.symm⟩
  refine ⟨L, hIn, fun y hy => ?_⟩
  have hs : In (⊤ : Ideal B) (comb (y - L) e) := by
    intro α
    obtain ⟨a, -, ha⟩ := hIn α
    obtain ⟨a', -, ha'⟩ := hy α
    refine ⟨a - a', trivial, ?_⟩
    rw [map_sub, ← ha, ← ha', ← map_sub, comb_sub]
    congr 1; abel
  exact sub_eq_zero.1 (U3 _ _ hs rfl)
