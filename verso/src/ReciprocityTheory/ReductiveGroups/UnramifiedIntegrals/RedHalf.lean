import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

/- English proof (translation)
Introduce `hPL`. Apply `(h.1 P hP).2` to reduce the goal to its premises. Rewrite using `[two_mul]`. Conclude with `add_mem hPL hPL`.
-/
theorem IsHalfReps.notMem (h : IsHalfReps L α T) {P : ℂ} (hP : P ∈ T) : P ∉ L.lattice := by
  intro hPL
  apply (h.1 P hP).2
  rw [two_mul]
  exact add_mem hPL hPL

/- English proof (translation)
Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Break down `Finset.mem_union.mp hP with hP | hP` into its components or cases. Conclude with `⟨(h.1 P hP).1, h.notMem hP⟩`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.mp hP`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_neg]`. Conclude with `neg_mem (h.1 Q hQ).1`. Introduce `hn; exact h.notMem hQ (by simpa using neg_mem hn)`. Introduce `P hP Q hQ hPQ`.

Apply the tactic sequence `rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ`. Conclude with `h.2.1 P hP Q hQ (Or.inl hPQ)`. Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.mp hQ`. Establish `e : P = Q'` using `h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))`. Substitute `e` using the available equality.

Conclude with `absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2`. Take `⟨P', hP', rfl⟩` from `Finset.mem_image.mp hP`. Establish `h1 : P' + Q ∈ L.lattice`. Use `neg_mem hPQ` as an intermediate fact. Establish `e : -(-P' - Q) = P' + Q` using `by ring`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `e : P' = Q` using `h.2.1 P' hP' Q hQ (Or.inr h1)`. Substitute `e` using the available equality. Conclude with `absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2`. Take `⟨P', hP', rfl⟩` from `Finset.mem_image.mp hP`.

Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.mp hQ`. Establish `h1 : P' - Q' ∈ L.lattice`. Use `neg_mem hPQ` as an intermediate fact. Establish `e : -(-P' - -Q') = P' - Q'` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Rewrite using `[h.2.1 P' hP' Q' hQ' (Or.inl h1)]`. Introduce `z hz hzL`. Take `⟨P, hP, hzP | hzP⟩` from `h.2.2 z hz hzL`. Conclude with `⟨P, Finset.mem_union_left _ hP, hzP⟩`. Conclude with `⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩`.

Rewrite using `[Finset.disjoint_left]`. Introduce `P hP hP'`. Take `⟨Q, hQ, hQP⟩` from `Finset.mem_image.mp hP'`. Establish `h0 : P + Q ∈ L.lattice` using `by rw [← hQP]; simp`. Establish `e : P = Q` using `h.2.1 P hP Q hQ (Or.inr h0)`.

Substitute `e` using the available equality. Conclude with `(h.1 P hP).2 (by rw [two_mul]; exact h0)`.
-/
theorem IsHalfReps.kerReps (h : IsHalfReps L α T) :
    IsKerReps L α (T ∪ T.image (fun P => -P)) ∧ Disjoint T (T.image (fun P => -P)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact ⟨(h.1 P hP).1, h.notMem hP⟩
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨?_, ?_⟩
      · rw [mul_neg]; exact neg_mem (h.1 Q hQ).1
      · intro hn; exact h.notMem hQ (by simpa using neg_mem hn)
  · intro P hP Q hQ hPQ
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact h.2.1 P hP Q hQ (Or.inl hPQ)
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have e : P = Q' := h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))
      subst e
      exact absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      have h1 : P' + Q ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - Q) = P' + Q := by ring
        rwa [e] at this
      have e : P' = Q := h.2.1 P' hP' Q hQ (Or.inr h1)
      subst e
      exact absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have h1 : P' - Q' ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - -Q') = P' - Q' := by ring
        rwa [e] at this
      rw [h.2.1 P' hP' Q' hQ' (Or.inl h1)]
  · intro z hz hzL
    obtain ⟨P, hP, hzP | hzP⟩ := h.2.2 z hz hzL
    · exact ⟨P, Finset.mem_union_left _ hP, hzP⟩
    · exact ⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP'
    have h0 : P + Q ∈ L.lattice := by rw [← hQP]; simp
    have e : P = Q := h.2.1 P hP Q hQ (Or.inr h0)
    subst e
    exact (h.1 P hP).2 (by rw [two_mul]; exact h0)

/- English proof (translation)
Establish `h1` using `kerRepsCard L α _ hα hs h.kerReps.1`. Rewrite `h1` using `[Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective]`. Rewrite using `[← h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsHalfReps.card (h : IsHalfReps L α T) (hα : α ≠ 0) (hs : MulStable L α) :
    2 * (T.card : ℝ) + 1 = Complex.normSq α := by
  have h1 := kerRepsCard L α _ hα hs h.kerReps.1
  rw [Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective] at h1
  rw [← h1]; push_cast; ring

/- English proof (translation)
Introduce `P hP Q hQ hPQ`. Conclude with `h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)`.
-/
theorem IsHalfReps.injOn (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by
  intro P hP Q hQ hPQ
  exact h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)

/- English proof (translation)
The claim follows from `Finset.card_image_of_injOn h.injOn`.
-/
theorem IsHalfReps.card_xsOf (h : IsHalfReps L α T) : (xsOf L T).card = T.card :=
  Finset.card_image_of_injOn h.injOn

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `Finset.mem_image.mp hx`. Establish `hPL` using `h.notMem hP`. Unfold `fW`. Rewrite using `[← L.derivWeierstrassP_sq P hPL]`. Conclude with `pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))`.
-/
theorem IsHalfReps.fW_ne (h : IsHalfReps L α T) {x : ℂ} (hx : x ∈ xsOf L T) : fW L.g₂ L.g₃ x ≠ 0 := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  have hPL := h.notMem hP
  unfold fW
  rw [← L.derivWeierstrassP_sq P hPL]
  exact pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨P, hP, hPz⟩` from `Finset.mem_image.mp hx`. Break down `(pInjective L z P hz (h.notMem hP)).mp hPz.symm with h1 | h1` into its components or cases. Establish `e : α * z = α * (z - P) + α * P` using `by ring`.

Rewrite using `[e]`. Conclude with `add_mem (hs _ h1) (h.1 P hP).1`. Establish `e : α * z = α * (z + P) - α * P` using `by ring`. Rewrite using `[e]`. Conclude with `sub_mem (hs _ h1) (h.1 P hP).1`.

Introduce `hk`. Take `⟨P, hP, h1⟩` from `h.2.2 z hk hz`. Conclude with `Finset.mem_image.mpr ⟨P, hP, ((pInjective L z P hz (h.notMem hP)).mpr h1).symm⟩`.
-/
theorem IsHalfReps.mem_xsOf (h : IsHalfReps L α T) (hs : MulStable L α) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z ∈ xsOf L T ↔ α * z ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨P, hP, hPz⟩ := Finset.mem_image.mp hx
    rcases (pInjective L z P hz (h.notMem hP)).mp hPz.symm with h1 | h1
    · have e : α * z = α * (z - P) + α * P := by ring
      rw [e]; exact add_mem (hs _ h1) (h.1 P hP).1
    · have e : α * z = α * (z + P) - α * P := by ring
      rw [e]; exact sub_mem (hs _ h1) (h.1 P hP).1
  · intro hk
    obtain ⟨P, hP, h1⟩ := h.2.2 z hk hz
    exact Finset.mem_image.mpr ⟨P, hP, ((pInjective L z P hz (h.notMem hP)).mpr h1).symm⟩

/- English proof (translation)
Take `⟨t, n, ht, -, -⟩` from `mulStableIntegral L α hs`. Establish `h1 : (N : ℂ) = α * (starRingEnd ℂ) α`. Rewrite using `[Complex.mul_conj, hN]`. Simplify using the standard rewrite rules. Establish `e : (N : ℂ) * z = t • (α * z) - α * (α * z)`.

Rewrite using `[h1, zsmul_eq_mul, ← ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (zsmul_mem hz t) (hs _ hz)`.
-/
theorem ker_norm (hs : MulStable L α) {N : ℕ} (hN : Complex.normSq α = N) {z : ℂ}
    (hz : α * z ∈ L.lattice) : (N : ℂ) * z ∈ L.lattice := by
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hs
  have h1 : (N : ℂ) = α * (starRingEnd ℂ) α := by
    rw [Complex.mul_conj, hN]; simp
  have e : (N : ℂ) * z = t • (α * z) - α * (α * z) := by
    rw [h1, zsmul_eq_mul, ← ht]; ring
  rw [e]
  exact sub_mem (zsmul_mem hz t) (hs _ hz)

/- English proof (translation)
Take `⟨S, hS⟩` from `kerRepsExist L α hα hs`. Set `g : ℂ → ℂ` to `fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)`. Establish `hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P` using `fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩`. Use `⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hP`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.mp hx`. Establish `hk` using `hS.1 _ (hg P0 hP0).1`. Use `⟨hk.1, fun h2 => hk.2 ?_⟩` and prove the remaining obligations. Take `⟨k, hk'⟩` from `hodd`.

Establish `h3` using `ker_norm hs hN hk.1`. Establish `e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0))`. Rewrite using `[hk', zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `sub_mem h3 (zsmul_mem h2 _)`. Introduce `P hP Q hQ hPQ`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hP`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.mp hx`.

Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hQ`. Take `⟨Q0, hQ0, rfl⟩` from `Finset.mem_image.mp hy`. Establish `h1` using `(pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ`. Rewrite `h1` using `[(hg P0 hP0).2, (hg Q0 hQ0).2]`. Rewrite using `[h1]`.

Introduce `z hz hzL`. Take `⟨P0, hP0, h0⟩` from `hS.2.2 z hz hzL`. Use `⟨g (L.weierstrassP P0), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩` and prove the remaining obligations. Apply `(pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp` to reduce the goal to its premises. Rewrite using `[(hg P0 hP0).2]`.

Conclude with `(pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)`.
-/
theorem halfReps_exist (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by
  obtain ⟨S, hS⟩ := kerRepsExist L α hα hs
  let g : ℂ → ℂ := fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)
  have hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P :=
    fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩
  refine ⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    have hk := hS.1 _ (hg P0 hP0).1
    refine ⟨hk.1, fun h2 => hk.2 ?_⟩
    obtain ⟨k, hk'⟩ := hodd
    have h3 := ker_norm hs hN hk.1
    have e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0)) := by
      rw [hk', zsmul_eq_mul]; push_cast; ring
    rw [e]
    exact sub_mem h3 (zsmul_mem h2 _)
  · intro P hP Q hQ hPQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨Q0, hQ0, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ
    rw [(hg P0 hP0).2, (hg Q0 hQ0).2] at h1
    rw [h1]
  · intro z hz hzL
    obtain ⟨P0, hP0, h0⟩ := hS.2.2 z hz hzL
    refine ⟨g (L.weierstrassP P0),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩
    apply (pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp
    rw [(hg P0 hP0).2]
    exact (pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)

end ReciprocityTheory.ChartRestriction.L1
