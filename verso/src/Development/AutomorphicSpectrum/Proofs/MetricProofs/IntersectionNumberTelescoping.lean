import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def positionPerm {n : ℕ} (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' m).symm

/- English proof (translation)
Simplify using `[positionPerm]`.
-/
theorem positionPerm_last {n : ℕ} (m : Fin (n + 1)) : positionPerm m (Fin.last n) = m := by
  simp [positionPerm]

/- English proof (translation)
Simplify using `[positionPerm]`.
-/
theorem positionPerm_castSucc {n : ℕ} (m : Fin (n + 1)) (j : Fin n) :
    positionPerm m (Fin.castSucc j) = m.succAbove j := by
  simp [positionPerm]

def word {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) : Fin (n + 1) → HermLine ι :=
  fun j => if (j : ℕ) < m then a else if (j : ℕ) < k then a₀ else A'

/- English proof (translation)
Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [word, positionPerm_last, hk]`. Consider the case `cast i`. Simplify using `only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]`.

Break down `lt_or_ge (i : ℕ) m with h | h` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]`. Simplify using `[h]`. Rewrite using `[Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]`. Establish `h1 : ¬ (i : ℕ) + 1 < m` using `by omega`.

Establish `h2 : ¬ (i : ℕ) < m` using `by omega`. Simplify using `[h1, h2]`.
-/
theorem word_comp_low {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) (hk : m < k) :
    word (n := n) a a₀ A' k m ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last, hk]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      simp [h]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [word, positionPerm_last]`. Consider the case `cast i`. Simplify using `only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]`.

Break down `lt_or_ge (i : ℕ) m with h | h` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]`. Establish `h1 : (i : ℕ) < m + 1` using `by omega`. Simplify using `[h, h1]`. Rewrite using `[Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]`.

Establish `h1 : ¬ (i : ℕ) + 1 < m + 1` using `by omega`. Establish `h2 : ¬ (i : ℕ) < m` using `by omega`. Simplify using `[h1, h2]`.
-/
theorem word_comp_high {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) :
    word (n := n) a a₀ A' k (m + 1) ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      have h1 : (i : ℕ) < m + 1 := by omega
      simp [h, h1]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m + 1 := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa using hx`. Consider the case `cast i => simpa using hL i`.
-/
theorem forall_snoc {n : ℕ} {p : HermLine ι → Prop} {L : Fin n → HermLine ι} {x : HermLine ι}
    (hL : ∀ j, p (L j)) (hx : p x) : ∀ j, p ((Fin.snoc L x : Fin (n + 1) → HermLine ι) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hx
  | cast i => simpa using hL i

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k`. Take `⟨i, hi⟩` from `h k`. Conclude with `⟨i, right_ne_zero_of_mul hi⟩`. Introduce `h k`.

Take `⟨i, hi⟩` from `h k`. Conclude with `⟨i, mul_ne_zero (hc k) hi⟩`.
-/
theorem cone_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, right_ne_zero_of_mul hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

/- English proof (translation)
Establish `hcone` using `cone_smul c z hc`. Unfold `logRatio`. Distinguish the cases in `h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0`. Rewrite using `[if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]`. Establish `hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))`.

Rewrite using `[Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => h (hcone.mp h')), if_neg h]`.
-/
theorem logRatio_smul {a a₀ : HermLine ι} (hd : a.a = a₀.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := by
  have hcone := cone_smul c z hc
  unfold logRatio
  by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]
    have hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']
    ring
  · rw [if_neg (fun h' => h (hcone.mp h')), if_neg h]

/- English proof (translation)
Establish `h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `ha₀`. Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `ha`. Use `show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Use `((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_` and prove the remaining obligations. Introduce `z hz`.

Establish `hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0` using `hz`. Simplify using `only [logRatio, if_pos hz']`.
-/
theorem logRatio_smooth {a a₀ : HermLine ι} (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logRatio a a₀) := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_
  intro z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  simp only [logRatio, if_pos hz']

/- English proof (translation)
Establish `h0` using `a₀.pos z hz`. Establish `h1` using `a.pos z hz`. Use `show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z`. Rewrite using `[logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0, ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]`.
-/
theorem tensor_logRatio_h {a a₀ : HermLine ι}
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)).h z = a.h z := by
  have h0 := a₀.pos z hz
  have h1 := a.pos z hz
  show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z
  rw [logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0,
    ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]

/- English proof (translation)
Establish `hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z` using `fun c z hc => logRatio_smul hd c z hc`. Establish `hMs : ∀ j, IsSmoothHerm (mixWord (n` using `n) a a₀ A' k m j) := fun j => by`. Simplify using `only [mixWord]`. Apply the tactic sequence `split_ifs <;> assumption`. Establish `hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n` using `n) a a₀ A' k r j) := fun r j => by`.

Simplify using `only [word]`. Apply the tactic sequence `split_ifs <;> assumption`. Establish `hmn : m < n + 1` using `lt_of_lt_of_le hm hk`. Establish `h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `ha₀`. Establish `hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `logRatio_smooth ha ha₀`.

Establish `hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))` using `by show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z)) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Conclude with `h0.mul hlr.neg.exp`. Establish `e1 : I P (n + 1) (word (n` using `n) a a₀ A' k (m + 1)) = I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by`. Rewrite using `[← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]`. Establish `e0 : I P (n + 1) (word (n` using `n) a a₀ A' k m) = I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by`.

Rewrite using `[← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]`. Establish `e2 : I P (n + 1) (Fin.snoc (mixWord (n` using `n) a a₀ A' k m) a) = I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by`. Use `metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha) (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_` and prove the remaining obligations. Introduce `j`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [Fin.snoc_last]`. Use `show a.a = a₀.a + 0`. Rewrite using `[add_zero, hd]`. Consider the case `cast i => simp only [Fin.snoc_castSucc]`.

Introduce `j z hz`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Fin.snoc_last]`. Conclude with `(tensor_logRatio_h hu z hz.1).symm`.

Consider the case `cast i => simp only [Fin.snoc_castSucc]`. Establish `e3` using `metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀ (logRatio_smooth ha ha₀)`. Rewrite using `[e1, e0, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem word_step (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k m : ℕ)
    (hP : IsArithVar P (n + 1)) (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) (hA' : IsSmoothHerm A')
    (hd : a.a = a₀.a) (hk : k ≤ n + 1) (hm : m < k) :
    I P (n + 1) (word a a₀ A' k (m + 1)) - I P (n + 1) (word a a₀ A' k m) =
      -ptsIntegral P (pot (mixWord (n := n) a a₀ A' k m)) (logRatio a a₀) := by
  have hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := fun c z hc => logRatio_smul hd c z hc
  have hMs : ∀ j, IsSmoothHerm (mixWord (n := n) a a₀ A' k m j) := fun j => by
    simp only [mixWord]
    split_ifs <;> assumption
  have hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n := n) a a₀ A' k r j) := fun r j => by
    simp only [word]
    split_ifs <;> assumption
  have hmn : m < n + 1 := lt_of_lt_of_le hm hk
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := logRatio_smooth ha ha₀
  have hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    exact h0.mul hlr.neg.exp
  have e1 : I P (n + 1) (word (n := n) a a₀ A' k (m + 1)) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by
    rw [← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]
  have e0 : I P (n + 1) (word (n := n) a a₀ A' k m) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by
    rw [← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]
  have e2 : I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m)
        (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by
    refine metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha)
      (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        show a.a = a₀.a + 0
        rw [add_zero, hd]
      | cast i => simp only [Fin.snoc_castSucc]
    · intro j z hz
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact (tensor_logRatio_h hu z hz.1).symm
      | cast i => simp only [Fin.snoc_castSucc]
  have e3 := metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀
    (logRatio_smooth ha ha₀)
  rw [e1, e0, e2, e3]
  ring

/- English proof (translation)
Introduce `K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk`. Establish `h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n` using `n) a a₀ A' k k := by`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : (j : ℕ) < k <;> simp [word, h]`. Establish `h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n` using `n) a a₀ A' k 0 := by`.

Use function extensionality and compare the values at `j`. Simplify using `[word]`. Establish `hs` using `Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k`. Rewrite using `[h1, h0, ← hs, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Conclude with `word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)`.
-/
theorem positionTelescope : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) →
      IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 →
      I P (n + 1) (fun j => if (j : ℕ) < k then a else A') -
          I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') =
        -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  intro K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk
  have h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n := n) a a₀ A' k k := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [word, h]
  have h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n := n) a a₀ A' k 0 := by
    funext j
    simp [word]
  have hs := Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k
  rw [h1, h0, ← hs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele
