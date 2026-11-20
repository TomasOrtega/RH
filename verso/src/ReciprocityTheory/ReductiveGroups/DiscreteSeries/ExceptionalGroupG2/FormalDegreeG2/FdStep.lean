import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Introduce `i j hij`. Establish `h1` using `hlam hij`. Establish `h2 : (c j : ℝ) ≤ c i` using `by exact_mod_cast hc hij.le`. Simplify using `only [Pi.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  have h1 := hlam hij
  have h2 : (c j : ℝ) ≤ c i := by exact_mod_cast hc hij.le
  simp only [Pi.add_apply]
  linarith

/- English proof (translation)
Take `⟨h1, h2⟩` from `hlam`. Use `⟨fdS_strictAnti h1 hc, fun a => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `h2 a`. Use `⟨m + (c a : ℤ), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  obtain ⟨h1, h2⟩ := hlam
  refine ⟨fdS_strictAnti h1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := h2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

/- English proof (translation)
Introduce `a b hab`. Establish `hg` using `hgap a b hab`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `h1` using `hlam h`. Establish `h2 : (c b : ℝ) ≤ c a` using `by exact_mod_cast hc h.le`.

Simplify using `only [Pi.add_apply]`. Rewrite `*` using `[abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd (h ▸ rfl) hab`. Establish `h1` using `hlam h`.

Establish `h2 : (c a : ℝ) ≤ c b` using `by exact_mod_cast hc h.le`. Simplify using `only [Pi.add_apply]`. Rewrite `*` using `[abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  intro a b hab
  have hg := hgap a b hab
  rcases lt_trichotomy a b with h | h | h
  · have h1 := hlam h
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc h.le
    simp only [Pi.add_apply]
    rw [abs_of_pos (by linarith)] at *
    linarith
  · exact absurd (h ▸ rfl) hab
  · have h1 := hlam h
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc h.le
    simp only [Pi.add_apply]
    rw [abs_of_neg (by linarith)] at *
    linarith

/- English proof (translation)
Establish `hμs : StrictAnti μ` using `hμ.1`. Rewrite using `[hstep μ s hμ hg hg' hs, ratioV_eq_vand hμs s]`. Establish `h1` using `vand_pos hμs`. Establish `h2` using `vand_pos hs`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμs : StrictAnti μ := hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμs s]
  have h1 := vand_pos hμs
  have h2 := vand_pos hs
  field_simp

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `c hc hsum`. Establish `h0 : ∀ i, c i = 0` using `fun i => Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i)`.

Establish `hl : (lam + fun i => (c i : ℝ)) = lam`. Use function extensionality and compare the values at `i`. Simplify using `[h0 i]`. Rewrite using `[hl]`. Consider the case `succ N ih`.

Introduce `c hc hsum`. Establish `hne : (univ.filter (fun i => c i ≠ 0)).Nonempty`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]`. Establish `: ∑ i, c i = 0` using `Finset.sum_eq_zero (fun i _ => by simpa using hcon (Finset.mem_univ i))`.

Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hafter⟩ : ∃ s, c s ≠ 0 ∧ ∀ j, s < j → c j = 0 := by`. Use `⟨(univ.filter (fun i => c i ≠ 0)).max' hne, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.max'_mem _ hne` as an intermediate fact. Simplify using `only [Finset.mem_filter] at this`.

Conclude with `this.2`. Introduce `j hj`. Assume the negation of the conclusion as `hcj`. Conclude with `absurd (Finset.le_max' _ j (by simp [hcj])) (not_le.mpr hj)`. Set `c' : Fin n → ℕ` to `fun i => if i = s then c i - 1 else c i`.

Establish `hc' : Antitone c'`. Introduce `i j hij`. Simplify using `only [c']`. Establish `hcij` using `hc hij`. Apply the tactic sequence `by_cases hi : i = s <;> by_cases hj : j = s`.

Rewrite using `[if_pos hj, if_pos hi]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hj, if_pos hi]`. Establish `hsj : s < j` using `lt_of_le_of_ne (by rw [← hi]; exact hij) (Ne.symm hj)`. Rewrite using `[hafter j hsj]`.

Conclude with `Nat.zero_le _`. Rewrite using `[if_pos hj, if_neg hi]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hj, if_neg hi]`. Conclude with `hcij`.

Establish `hcs : c' s = c s - 1` using `by simp [c']`. Establish `hsum' : ∑ i, c' i = N`. Establish `e1` using `Finset.add_sum_erase univ c (Finset.mem_univ s)`. Establish `e2` using `Finset.add_sum_erase univ c' (Finset.mem_univ s)`. Establish `e3 : ∑ x ∈ univ.erase s, c x = ∑ x ∈ univ.erase s, c' x` using `Finset.sum_congr rfl (fun x hx => by simp [c', Finset.ne_of_mem_erase hx])`.

Rewrite `e2` using `[hcs]`. Use linear arithmetic over natural numbers and integers. Establish `hih` using `ih c' hc' hsum'`. Establish `heq : ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) = lam + fun i => (c i : ℝ)`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.single_apply, c']`. Distinguish the cases in `hi : i = s`. Rewrite using `[if_pos hi, if_pos hi]`. Substitute `hi` using the available equality. Rewrite using `[Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hs)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hi, if_neg hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `hμ` using `fdS_hc hlam hc'`.

Establish `hg` using `fdS_gap hlam.1 hgap hc'`. Establish `hg' : GapAtLeast ε ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) h`. Rewrite using `[heq]`. Conclude with `fdS_gap hlam.1 hgap hc`. Establish `hsa : StrictAnti ((lam + fun i => (c' i : ℝ)) + Pi.single s 1)`.

Rewrite using `[heq]`. Conclude with `fdS_strictAnti hlam.1 hc`. Establish `key` using `fdS_stepQ dfun hstep hμ hg s hg' hsa`. Rewrite `key` using `[heq]`. Rewrite using `[key, hih]`.
-/
theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  intro N
  induction N with
  | zero =>
    intro c hc hsum
    have h0 : ∀ i, c i = 0 := fun i => Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i)
    have hl : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [h0 i]
    rw [hl]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      have : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i _ => by simpa using hcon (Finset.mem_univ i))
      omega
    obtain ⟨s, hs, hafter⟩ : ∃ s, c s ≠ 0 ∧ ∀ j, s < j → c j = 0 := by
      refine ⟨(univ.filter (fun i => c i ≠ 0)).max' hne, ?_, ?_⟩
      · have := Finset.max'_mem _ hne
        simp only [Finset.mem_filter] at this
        exact this.2
      · intro j hj
        by_contra hcj
        exact absurd (Finset.le_max' _ j (by simp [hcj])) (not_le.mpr hj)
    let c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i
    have hc' : Antitone c' := by
      intro i j hij
      simp only [c']
      have hcij := hc hij
      by_cases hi : i = s <;> by_cases hj : j = s
      · rw [if_pos hj, if_pos hi]
        omega
      · rw [if_neg hj, if_pos hi]
        have hsj : s < j := lt_of_le_of_ne (by rw [← hi]; exact hij) (Ne.symm hj)
        rw [hafter j hsj]
        exact Nat.zero_le _
      · rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hcij
    have hcs : c' s = c s - 1 := by simp [c']
    have hsum' : ∑ i, c' i = N := by
      have e1 := Finset.add_sum_erase univ c (Finset.mem_univ s)
      have e2 := Finset.add_sum_erase univ c' (Finset.mem_univ s)
      have e3 : ∑ x ∈ univ.erase s, c x = ∑ x ∈ univ.erase s, c' x :=
        Finset.sum_congr rfl (fun x hx => by simp [c', Finset.ne_of_mem_erase hx])
      rw [hcs] at e2
      omega
    have hih := ih c' hc' hsum'
    have heq : ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply, c']
      by_cases hi : i = s
      · rw [if_pos hi, if_pos hi]
        subst hi
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hs)]
        push_cast
        ring
      · rw [if_neg hi, if_neg hi]
        ring
    have hμ := fdS_hc hlam hc'
    have hg := fdS_gap hlam.1 hgap hc'
    have hg' : GapAtLeast ε ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) h := by
      rw [heq]
      exact fdS_gap hlam.1 hgap hc
    have hsa : StrictAnti ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) := by
      rw [heq]
      exact fdS_strictAnti hlam.1 hc
    have key := fdS_stepQ dfun hstep hμ hg s hg' hsa
    rw [heq] at key
    rw [key, hih]

/- English proof (translation)
Establish `hn : ∀ i : Fin n, (i : ℕ) ≤ n - 1` using `fun i => by`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `c : Fin n → ℕ` to `fun i => t * (n - 1 - (i : ℕ))`. Establish `hc : Antitone c`.

Introduce `i j hij`. Simplify using `only [c]`. Establish `: (i : ℕ) ≤ j` using `hij`. Conclude with `Nat.mul_le_mul_left _ (by omega)`. Establish `heq : lamT lam t = lam + fun i => (c i : ℝ)`.

Use function extensionality and compare the values at `i`. Simplify using `only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]`. Establish `h1 : 1 ≤ n`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Move the coercions through the operations in `[Nat.cast_sub (hn i), Nat.cast_sub h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `fdS_main dfun hstep hlam hgap _ c hc rfl`.
-/
theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hn : ∀ i : Fin n, (i : ℕ) ≤ n - 1 := fun i => by
    have := i.isLt
    omega
  let c : Fin n → ℕ := fun i => t * (n - 1 - (i : ℕ))
  have hc : Antitone c := by
    intro i j hij
    simp only [c]
    have : (i : ℕ) ≤ j := hij
    exact Nat.mul_le_mul_left _ (by omega)
  have heq : lamT lam t = lam + fun i => (c i : ℝ) := by
    funext i
    simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]
    have h1 : 1 ≤ n := by
      have := i.isLt
      omega
    push_cast [Nat.cast_sub (hn i), Nat.cast_sub h1]
    ring
  rw [heq]
  exact fdS_main dfun hstep hlam hgap _ c hc rfl

end ReciprocityTheory.ChartRestriction.DS.G2
