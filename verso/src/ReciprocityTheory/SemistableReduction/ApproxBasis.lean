import ReciprocityTheory.SemistableReduction.ApproxBasisB

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Unfold `normSq`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`.
-/
private theorem normSq_smul_eq_norm_sq_mul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    normSq (c • u) = ‖c‖ ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/- English proof (translation)
Unfold `approxR`. Establish `h1 : (1 : ℝ) ≤ Real.sqrt r` using `Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hr)`. Rewrite using `[le_div_iff₀ hρ]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hρ1 hμ.le, mul_le_mul_of_nonneg_left h1 hμ.le]`.
-/
private theorem le_approxR {r : ℕ} (hr : 0 < r) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : μ ≤ approxR r μ ρ := by
  unfold approxR
  have h1 : (1 : ℝ) ≤ Real.sqrt r := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hr)
  rw [le_div_iff₀ hρ]
  nlinarith [mul_le_mul_of_nonneg_left hρ1 hμ.le, mul_le_mul_of_nonneg_left h1 hμ.le]

/- English proof (translation)
Establish `hR` using `le_approxR j.pos hμ hρ hρ1`. Establish `h` using `approxB_normSq_add_le (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ((approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))`. Rewrite `h` using `[sub_add_cancel, approxB_normSq_single]`. Use polynomial arithmetic with `[mul_le_mul hR hR hμ.le (le_trans hμ.le hR)]`.
-/
private theorem normSq_le_of_normSq_sub_approxR_single_le {r : ℕ} {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (j : Fin r) (x : Fin r → ℂ)
    (hx : normSq (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) :
    normSq x ≤ (2 * approxR r μ ρ) ^ 2 := by
  have hR := le_approxR j.pos hμ hρ hρ1
  have h := approxB_normSq_add_le (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
    ((approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  rw [sub_add_cancel, approxB_normSq_single] at h
  nlinarith [mul_le_mul hR hR hμ.le (le_trans hμ.le hR)]

/- English proof (translation)
Rewrite using `[approxB_embVec_sum, Matrix.mulVec_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [approxB_embVec_smul, Matrix.mulVec_smul]`.
-/
private theorem mulVec_embVec_sum_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) {α : Type*} (s : Finset α) (g : α → K) (f : α → Fin r → K) :
    Q *ᵥ embVec σ (∑ j ∈ s, g j • f j) = ∑ j ∈ s, σ (g j) • (Q *ᵥ embVec σ (f j)) := by
  rw [approxB_embVec_sum, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [approxB_embVec_smul, Matrix.mulVec_smul]

/- English proof (translation)
Unfold `ApproxGraphStatement at hG`. Unfold `ApproxStatement`. Introduce `K _ _ ι _ _ r p S σ Q L v μ ρ hp hμ hρ hρ1 hQ hS hInt hcov hvL hvi hvμ`. Use `choose l0 hl0L hl0 using fun j : Fin r => hcov (fun _ => (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))`. Take `⟨X, hX⟩ : ∃ X : ι → Fin r → Fin r → ℂ, ∀ i j, X i j = Q i *ᵥ embVec (σ i) (l0 j)` from `⟨_, fun _ _ => rfl⟩`.

Establish `happ : ∀ i j, normSq (X i j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2`. Introduce `i j`. Rewrite using `[hX]`. Use `le_trans ?_ (hl0 j)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') (l0 j) - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))) (fun i' _ => approxB_normSq_nonneg _) (Finset.mem_univ i)`.

Establish `hGi` using `fun i => hG r p μ ρ (X i) hp hμ hρ hρ1 (fun j _ => happ i j)`. Establish `hdiag : ∀ i j, normSq (X i j) ≤ (2 * approxR r μ ρ) ^ 2` using `fun i j => normSq_le_of_normSq_sub_approxR_single_le hμ hρ hρ1 j _ (happ i j)`. Establish `hinj : ∀ g : ApproxPosIdx r p → K, (∀ k : ApproxPosIdx r p, S.h (l0 k.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0) → g = 0`. Introduce `g hg`. Assume the negation of the conclusion as `hne`.

Take `⟨i⟩` from `‹Nonempty ι›`. Establish `hzz : S.h (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0`. Rewrite using `[approxB_h_sum_left]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [approxB_h_smul_left, hg j, mul_zero]`. Establish `h1` using `hS i (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1)`.

Rewrite `h1` using `[hzz, map_zero, mulVec_embVec_sum_smul]`. Establish `hx : (fun k : ApproxPosIdx r p => σ i (g k)) ≠ 0`. Introduce `hx`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Conclude with `(map_eq_zero (σ i)).mp (congrFun hx k)`. Establish `h2` using `(approxB_graph_pos hρ1 hρ (X i) (hGi i).1 (fun k => σ i (g k))).2 hx`. Simplify using `only [hX] at h2`. Rewrite `h2` using `[← h1]`. Simplify using `at h2`.

Take `⟨Δ, coef, a, hΔ0, hΔ, horth, hmem, hli⟩` from `approxB_split hp S L hInt l0 v hl0L hvi hinj`. Take `⟨la, hla⟩ : ∃ la : Fin r → Fin r → K, la = fun j : Fin r => if h : (j : ℕ) < p then l0 j else Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1` from `⟨_, rfl⟩`. Establish `hla_pos : ∀ (j : Fin r) (h : (j : ℕ) < p), la j = l0 j` using `fun j h => by`. Rewrite using `[hla]`. Simplify using `only [dif_pos h]`.

Establish `hla_neg : ∀ (j : Fin r) (h : ¬ (j : ℕ) < p), la j = Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1` using `fun j h => by`. Rewrite using `[hla]`. Simplify using `only [dif_neg h]`. Establish `hli' : LinearIndependent K la` using `by rw [hla]; exact hli`. Establish `horth' : ∀ (k : Fin r), (k : ℕ) < p → ∀ j : Fin r, ¬ (j : ℕ) < p → S.h (l0 k) (la j) = 0` using `fun k hk j hj => by`.

Rewrite using `[hla_neg j hj]`. Conclude with `horth _ ⟨k, hk⟩`. Establish `hdet : ∀ i, ((Matrix.of la).map (σ i)).det ≠ 0`. Introduce `i`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Establish `hu : IsUnit (Matrix.of la)` using `(Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of la)).mp hli'`. Conclude with `(map_ne_zero (σ i)).mpr ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`. Establish `hcomb : ∀ i (w : Fin r → ℂ), Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • (Q i *ᵥ embVec (σ i) (la j))`. Introduce `i w`. Rewrite using `[Matrix.mulVec_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _`. Establish `hne : ∀ i (w : Fin r → ℂ), w ≠ 0 → Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) ≠ 0`. Introduce `i w hw h0`. Apply `hw` to reduce the goal to its premises. Establish `h1` using `Matrix.eq_zero_of_mulVec_eq_zero (hQ i) h0`.

Use `Matrix.eq_zero_of_vecMul_eq_zero (hdet i) ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Use function extensionality and compare the values at `b`. Simplify using `[Matrix.vecMul, dotProduct, embVec, Finset.sum_apply]`. Use `⟨la, fun j => ?_, hli', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : (j : ℕ) < p`. Rewrite using `[hla_pos j h]`. Conclude with `hl0L j`. Rewrite using `[hla_neg j h]`. Conclude with `hmem _ (hvL _)`.

Introduce `j k hj hk`. Rewrite using `[hla_pos j hj]`. Conclude with `horth' j hj k (not_lt.mpr hk)`. Introduce `i w hw`. Establish `hsum : Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • X i j`.

Rewrite using `[hcomb]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (j : ℕ) < p`. Rewrite using `[hla_pos j h, hX]`. Rewrite using `[hw j (not_lt.mp h), zero_smul, zero_smul]`.

Rewrite using `[hsum]`. Take `⟨h1, h2⟩` from `(hGi i).1 w hw`. Use `⟨h1, fun hw0 => ?_⟩` and prove the remaining obligations. Establish `h3` using `h2 hw0`. Rewrite using `[approxB_jForm_self_re]`.

Establish `hq : (ρ / 3) ^ 2 < 1` using `by nlinarith`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_right hq h3]`. Introduce `i w hw hw0`. Use `(hGi i).2.1 _ (fun j hj => ?_) (hne i w hw0)` and prove the remaining obligations. Rewrite using `[hcomb, approxB_jForm_sum_right]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[approxB_jForm_smul_right]`. Distinguish the cases in `hk : (k : ℕ) < p`. Rewrite using `[hw k hk, zero_mul]`. Rewrite using `[hX, ← hS, horth' j hj k hk, map_zero, mul_zero]`.

Introduce `i j hj`. Rewrite using `[hS i, hla_pos j hj, ← hX]`. Conclude with `le_trans (approxB_norm_jForm_self_le p _) (hdiag i j)`. Introduce `i j hj`. Establish `hj' : ¬ (j : ℕ) < p` using `not_lt.mpr hj`.

Take `⟨x, hx⟩ : ∃ x, x = v (a ⟨j, hj'⟩)` from `⟨_, rfl⟩`. Rewrite using `[hS i, hla_neg j hj', ← hx]`. Establish `hort : ∀ k : Fin r, (k : ℕ) < p → jForm p (X i k) (Q i *ᵥ embVec (σ i) (Δ • x - ∑ k', coef x k' • l0 k'.1)) = 0`. Introduce `k hk`. Establish `h0 : S.h (l0 k) (Δ • x - ∑ k', coef x k' • l0 k'.1) = 0` using `horth x ⟨k, hk⟩`.

Rewrite using `[hX, ← hS, h0, map_zero]`. Establish `hspan : Q i *ᵥ embVec (σ i) (Δ • x) - Q i *ᵥ embVec (σ i) (Δ • x - ∑ k', coef x k' • l0 k'.1) ∈ Submodule.span ℂ (X i '' {j | (j : ℕ) < p})`. Rewrite using `[← Matrix.mulVec_sub, ← approxB_embVec_sub, sub_sub_cancel, mulVec_embVec_sum_smul]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, k.2, hX i k.1⟩)`. Establish `hb` using `(hGi i).2.2 _ _ hort hspan`.

Rewrite `hb` using `[approxB_embVec_smul, Matrix.mulVec_smul, normSq_smul_eq_norm_sq_mul]`. Establish `hxμ : normSq (Q i *ᵥ embVec (σ i) x) ≤ μ ^ 2`. Use `le_trans (Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') x)) (fun _ _ => approxB_normSq_nonneg _) (Finset.mem_univ i)) ?_` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `hvμ _`.

Establish `hgram : (σ i).mapMatrix (Matrix.of fun k j : ApproxPosIdx r p => S.h (l0 k.1) (l0 j.1)) = Matrix.of fun k j : ApproxPosIdx r p => jForm p (X i k.1) (X i j.1)`. Use extensionality with `k j`. Simplify using `[RingHom.mapMatrix_apply, hS, hX]`. Establish `hΔbd : ‖σ i Δ‖ ≤ ((2 * approxR r μ ρ) ^ 2) ^ p`. Rewrite using `[hΔ, RingHom.map_det, hgram]`.

Establish `h` using `approxB_det_le_of_posSemidef _ (approxB_gram_posSemidef hρ1 hρ (X i) (hGi i).1) ((2 * approxR r μ ρ) ^ 2) fun k => by`. Simplify using `only [Matrix.of_apply]`. Conclude with `le_trans (Complex.re_le_norm _) (le_trans (approxB_norm_jForm_self_le p _) (hdiag i k.1))`. Rewrite `h` using `[approxB_card_pos hp]`. Then use the resulting hypothesis. Establish `hsq : ‖σ i Δ‖ ^ 2 ≤ (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hΔbd 2`.

Establish `hpow : (2 * approxR r μ ρ) ^ (4 * p) = (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2`. Rewrite using `[← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpow]`.

Use `le_trans hb ?_` and prove the remaining obligations. Establish `hs0` using `approxB_normSq_nonneg (Q i *ᵥ embVec (σ i) x)`. Use polynomial arithmetic with `[mul_le_mul hsq hxμ hs0 (by positivity)]`.
-/
theorem approxBasis_holds (hG : ApproxGraphStatement) : ApproxStatement := by
  unfold ApproxGraphStatement at hG
  unfold ApproxStatement
  intro K _ _ ι _ _ r p S σ Q L v μ ρ hp hμ hρ hρ1 hQ hS hInt hcov hvL hvi hvμ
  choose l0 hl0L hl0 using fun j : Fin r =>
    hcov (fun _ => (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  obtain ⟨X, hX⟩ : ∃ X : ι → Fin r → Fin r → ℂ,
      ∀ i j, X i j = Q i *ᵥ embVec (σ i) (l0 j) := ⟨_, fun _ _ => rfl⟩
  have happ : ∀ i j, normSq (X i j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
      ≤ μ ^ 2 := by
    intro i j
    rw [hX]
    refine le_trans ?_ (hl0 j)
    exact Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') (l0 j) -
      (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))) (fun i' _ => approxB_normSq_nonneg _)
      (Finset.mem_univ i)
  have hGi := fun i => hG r p μ ρ (X i) hp hμ hρ hρ1 (fun j _ => happ i j)
  have hdiag : ∀ i j, normSq (X i j) ≤ (2 * approxR r μ ρ) ^ 2 :=
    fun i j => normSq_le_of_normSq_sub_approxR_single_le hμ hρ hρ1 j _ (happ i j)
  have hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l0 k.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0) → g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hzz : S.h (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0 := by
      rw [approxB_h_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [approxB_h_smul_left, hg j, mul_zero]
    have h1 := hS i (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1)
    rw [hzz, map_zero, mulVec_embVec_sum_smul] at h1
    have hx : (fun k : ApproxPosIdx r p => σ i (g k)) ≠ 0 := by
      intro hx
      apply hne
      funext k
      exact (map_eq_zero (σ i)).mp (congrFun hx k)
    have h2 := (approxB_graph_pos hρ1 hρ (X i) (hGi i).1 (fun k => σ i (g k))).2 hx
    simp only [hX] at h2
    rw [← h1] at h2
    simp at h2
  obtain ⟨Δ, coef, a, hΔ0, hΔ, horth, hmem, hli⟩ :=
    approxB_split hp S L hInt l0 v hl0L hvi hinj
  obtain ⟨la, hla⟩ : ∃ la : Fin r → Fin r → K, la = fun j : Fin r => if h : (j : ℕ) < p then l0 j
      else Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := ⟨_, rfl⟩
  have hla_pos : ∀ (j : Fin r) (h : (j : ℕ) < p), la j = l0 j := fun j h => by
    rw [hla]; simp only [dif_pos h]
  have hla_neg : ∀ (j : Fin r) (h : ¬ (j : ℕ) < p), la j =
      Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := fun j h => by
    rw [hla]; simp only [dif_neg h]
  have hli' : LinearIndependent K la := by rw [hla]; exact hli
  have horth' : ∀ (k : Fin r), (k : ℕ) < p → ∀ j : Fin r, ¬ (j : ℕ) < p →
      S.h (l0 k) (la j) = 0 := fun k hk j hj => by
    rw [hla_neg j hj]; exact horth _ ⟨k, hk⟩
  have hdet : ∀ i, ((Matrix.of la).map (σ i)).det ≠ 0 := by
    intro i
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu : IsUnit (Matrix.of la) :=
      (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of la)).mp hli'
    exact (map_ne_zero (σ i)).mpr ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hcomb : ∀ i (w : Fin r → ℂ),
      Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • (Q i *ᵥ embVec (σ i) (la j)) := by
    intro i w
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
  have hne : ∀ i (w : Fin r → ℂ), w ≠ 0 → Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) ≠ 0 := by
    intro i w hw h0
    apply hw
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i) h0
    refine Matrix.eq_zero_of_vecMul_eq_zero (hdet i) ?_
    rw [← h1]
    funext b
    simp [Matrix.vecMul, dotProduct, embVec, Finset.sum_apply]
  refine ⟨la, fun j => ?_, hli', ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : (j : ℕ) < p
    · rw [hla_pos j h]; exact hl0L j
    · rw [hla_neg j h]; exact hmem _ (hvL _)
  · intro j k hj hk
    rw [hla_pos j hj]
    exact horth' j hj k (not_lt.mpr hk)
  · intro i w hw
    have hsum : Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • X i j := by
      rw [hcomb]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) < p
      · rw [hla_pos j h, hX]
      · rw [hw j (not_lt.mp h), zero_smul, zero_smul]
    rw [hsum]
    obtain ⟨h1, h2⟩ := (hGi i).1 w hw
    refine ⟨h1, fun hw0 => ?_⟩
    have h3 := h2 hw0
    rw [approxB_jForm_self_re]
    have hq : (ρ / 3) ^ 2 < 1 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hq h3]
  · intro i w hw hw0
    refine (hGi i).2.1 _ (fun j hj => ?_) (hne i w hw0)
    rw [hcomb, approxB_jForm_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [approxB_jForm_smul_right]
    by_cases hk : (k : ℕ) < p
    · rw [hw k hk, zero_mul]
    · rw [hX, ← hS, horth' j hj k hk, map_zero, mul_zero]
  · intro i j hj
    rw [hS i, hla_pos j hj, ← hX]
    exact le_trans (approxB_norm_jForm_self_le p _) (hdiag i j)
  · intro i j hj
    have hj' : ¬ (j : ℕ) < p := not_lt.mpr hj
    obtain ⟨x, hx⟩ : ∃ x, x = v (a ⟨j, hj'⟩) := ⟨_, rfl⟩
    rw [hS i, hla_neg j hj', ← hx]
    have hort : ∀ k : Fin r, (k : ℕ) < p → jForm p (X i k) (Q i *ᵥ embVec (σ i)
        (Δ • x - ∑ k', coef x k' • l0 k'.1)) = 0 := by
      intro k hk
      have h0 : S.h (l0 k) (Δ • x - ∑ k', coef x k' • l0 k'.1) = 0 := horth x ⟨k, hk⟩
      rw [hX, ← hS, h0, map_zero]
    have hspan : Q i *ᵥ embVec (σ i) (Δ • x) -
        Q i *ᵥ embVec (σ i) (Δ • x - ∑ k', coef x k' • l0 k'.1)
        ∈ Submodule.span ℂ (X i '' {j | (j : ℕ) < p}) := by
      rw [← Matrix.mulVec_sub, ← approxB_embVec_sub, sub_sub_cancel, mulVec_embVec_sum_smul]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, k.2, hX i k.1⟩)
    have hb := (hGi i).2.2 _ _ hort hspan
    rw [approxB_embVec_smul, Matrix.mulVec_smul, normSq_smul_eq_norm_sq_mul] at hb
    have hxμ : normSq (Q i *ᵥ embVec (σ i) x) ≤ μ ^ 2 := by
      refine le_trans (Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') x))
        (fun _ _ => approxB_normSq_nonneg _) (Finset.mem_univ i)) ?_
      rw [hx]
      exact hvμ _
    have hgram : (σ i).mapMatrix (Matrix.of fun k j : ApproxPosIdx r p => S.h (l0 k.1) (l0 j.1)) =
        Matrix.of fun k j : ApproxPosIdx r p => jForm p (X i k.1) (X i j.1) := by
      ext k j
      simp [RingHom.mapMatrix_apply, hS, hX]
    have hΔbd : ‖σ i Δ‖ ≤ ((2 * approxR r μ ρ) ^ 2) ^ p := by
      rw [hΔ, RingHom.map_det, hgram]
      have h := approxB_det_le_of_posSemidef _ (approxB_gram_posSemidef hρ1 hρ (X i) (hGi i).1)
        ((2 * approxR r μ ρ) ^ 2) fun k => by
          simp only [Matrix.of_apply]
          exact le_trans (Complex.re_le_norm _)
            (le_trans (approxB_norm_jForm_self_le p _) (hdiag i k.1))
      rwa [approxB_card_pos hp] at h
    have hsq : ‖σ i Δ‖ ^ 2 ≤ (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hΔbd 2
    have hpow : (2 * approxR r μ ρ) ^ (4 * p) =
        (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [hpow]
    refine le_trans hb ?_
    have hs0 := approxB_normSq_nonneg (Q i *ᵥ embVec (σ i) x)
    nlinarith [mul_le_mul hsq hxμ hs0 (by positivity)]

end ReciprocityTheory.MultiplicativeHeights
