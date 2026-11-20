import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinearStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlopeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLawsStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt.le`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hx]`.

Consider the case `succ k ih`. Take `⟨hne, hv⟩` from `ih`. Rewrite using `[Function.iterate_succ_apply']`. Use `⟨((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 _ hne).1, ?_⟩` and prove the remaining obligations. Introduce `r hr0 hr1`.

Rewrite using `[((GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.1 _ hne).2]`. Establish `h1 : 0 < r / l` using `div_pos hr0 hl0`. Establish `h2 : r / l ≤ 1` using `by rw [div_le_one hl0]; linarith`. Rewrite using `[hv (r / l) h1 h2, pow_succ]`. Establish `e : r / (l : ℝ) / (l : ℝ) ^ k = r / ((l : ℝ) ^ k * l)` using `by rw [div_div, mul_comm]`.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vr_iterate_phi (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, (φc l)^[k] x ≠ 0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hl0 : (0 : ℝ) < l := by linarith
  intro k
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨hne, hv⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 _ hne).1, ?_⟩
    intro r hr0 hr1
    rw [((GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.1 _ hne).2]
    have h1 : 0 < r / l := div_pos hr0 hl0
    have h2 : r / l ≤ 1 := by rw [div_le_one hl0]; linarith
    rw [hv (r / l) h1 h2, pow_succ]
    have e : r / (l : ℝ) / (l : ℝ) ^ k = r / ((l : ℝ) ^ k * l) := by rw [div_div, mul_comm]
    rw [e]
    ring

/- English proof (translation)
Introduce `l _ h s hsh w w' hfix hw hw' hrat`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Take `⟨cA, kA, sA⟩` from `GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w hw`. Take `⟨cB, kB, sB⟩` from `GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w' hw'`.

Establish `key` using `GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s 1 hl2 hsh le_rfl (fun r => vr l r w) (fun r => vr l r w') cA cB kA kB sA sB ?_ ?_`. Take `⟨n, hn⟩` from `key`. Conclude with `⟨n, fun r hr => by simpa using hn r hr⟩`. Introduce and unpack `r ⟨hr0, hr1⟩`. Establish `e1` using `(vr_iterate_phi l w' hw' h).2 r hr0 hr1`.

Rewrite `e1` using `[hfix, (GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.2.1 w' s hw']`. Use `show (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `r ⟨hr0, hr1⟩`. Establish `hlr0 : 0 < (l : ℝ) * r` using `mul_pos hl0 hr0`.

Establish `hlr1 : (l : ℝ) * r ≤ 1` using `by rw [le_div_iff₀ hl0] at hr1; linarith`. Take `⟨hmul, hphi, -, -⟩` from `GlobalTheory.T.acrisValuation_radius_laws l (l * r) hlr0 hlr1`. Establish `e` using `congrArg (vr l (l * r)) hrat`. Rewrite `e` using `[hmul _ _ (hphi w hw).1 hw', hmul _ _ hw (hphi w' hw').1, (hphi w hw).2, (hphi w' hw').2]`. Establish `hc : (l : ℝ) * r / l = r` using `by field_simp`.

Rewrite `e` using `[hc]`. Use `show vr l (l * r) w - ((1 : ℕ) : ℝ) * vr l (l * r) w' = l * (vr l r w - ((1 : ℕ) : ℝ) * vr l r w')`. Simplify using `only [Nat.cast_one, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vr_sub_eq_int_mul : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  intro l _ h s hsh w w' hfix hw hw' hrat
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨cA, kA, sA⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w hw
  obtain ⟨cB, kB, sB⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w' hw'
  have key := GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s 1 hl2 hsh le_rfl (fun r => vr l r w) (fun r => vr l r w')
    cA cB kA kB sA sB ?_ ?_
  · obtain ⟨n, hn⟩ := key
    exact ⟨n, fun r hr => by simpa using hn r hr⟩
  · rintro r ⟨hr0, hr1⟩
    have e1 := (vr_iterate_phi l w' hw' h).2 r hr0 hr1
    rw [hfix, (GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.2.1 w' s hw'] at e1
    show (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r
    linarith
  · rintro r ⟨hr0, hr1⟩
    have hlr0 : 0 < (l : ℝ) * r := mul_pos hl0 hr0
    have hlr1 : (l : ℝ) * r ≤ 1 := by rw [le_div_iff₀ hl0] at hr1; linarith
    obtain ⟨hmul, hphi, -, -⟩ := GlobalTheory.T.acrisValuation_radius_laws l (l * r) hlr0 hlr1
    have e := congrArg (vr l (l * r)) hrat
    rw [hmul _ _ (hphi w hw).1 hw', hmul _ _ hw (hphi w' hw').1, (hphi w hw).2,
      (hphi w' hw').2] at e
    have hc : (l : ℝ) * r / l = r := by field_simp
    rw [hc] at e
    show vr l (l * r) w - ((1 : ℕ) : ℝ) * vr l (l * r) w' = l * (vr l r w - ((1 : ℕ) : ℝ) * vr l r w')
    simp only [Nat.cast_one, one_mul]
    linarith

end GlobalTheory.PMon.Gauss
