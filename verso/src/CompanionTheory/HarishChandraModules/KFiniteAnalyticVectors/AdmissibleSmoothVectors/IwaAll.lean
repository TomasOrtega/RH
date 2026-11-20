import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

noncomputable section

namespace CompanionTheory.D.gk.admitted

open Matrix PI.UpqRep

namespace CholeskyDecomposition

variable {n : ℕ}

def pr (ε : Fin n → Bool) (i : Fin n) : Fin n := if ε i.rev = ε i then i else i.rev

def ht (ε : Fin n → Bool) (i : Fin n) : ℤ := if ε i.rev = ε i then 0 else 2 * (i : ℤ) + 1 - n

def sg (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

def wt (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i.rev = ε i then sg ε i else 1

/- English proof (translation)
Unfold `pr`. Distinguish the cases in `h : ε i.rev = ε i`. Simplify using `[h]`. Establish `h' : ¬ε i = ε i.rev` using `fun e => h e.symm`. Simplify using `[h, h']`.
-/
theorem pr_pr (ε : Fin n → Bool) (i : Fin n) : pr ε (pr ε i) = i := by
  unfold pr
  by_cases h : ε i.rev = ε i
  · simp [h]
  · have h' : ¬ε i = ε i.rev := fun e => h e.symm
    simp [h, h']

/- English proof (translation)
Establish `h1` using `Fin.val_rev i`. Establish `h2` using `i.isLt`. Use linear arithmetic over natural numbers and integers.
-/
theorem rev_cast (i : Fin n) : ((i.rev : Fin n) : ℤ) = n - 1 - i := by
  have h1 := Fin.val_rev i
  have h2 := i.isLt
  omega

/- English proof (translation)
Introduce `h2`. Apply `h` to reduce the goal to its premises. Establish `e : i.rev = i`. Use `ext`. Establish `h3` using `Fin.val_rev i`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`.
-/
theorem ht_ne {ε : Fin n → Bool} {i : Fin n} (h : ε i.rev ≠ ε i) : 2 * (i : ℤ) + 1 - n ≠ 0 := by
  intro h2
  apply h
  have e : i.rev = i := by
    ext
    have h3 := Fin.val_rev i
    omega
  rw [e]

/- English proof (translation)
Unfold `ht`. Distinguish the cases in `h : ε i.rev = ε i`. Simplify using `[h]`. Rewrite using `[if_neg h]`. Conclude with `⟨fun e => absurd e (ht_ne h), fun e => absurd e h⟩`.
-/
theorem ht_eq_zero {ε : Fin n → Bool} {i : Fin n} : ht ε i = 0 ↔ ε i.rev = ε i := by
  unfold ht
  by_cases h : ε i.rev = ε i
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun e => absurd e (ht_ne h), fun e => absurd e h⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hji : j ≤ i`. Rewrite using `[Fin.le_iff_val_le_val]`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `hε hji`.

Rewrite `h3` using `[hi, hj]`. Conclude with `absurd h3 (by decide)`.
-/
theorem lt_of_sign {ε : Fin n → Bool} (hε : Monotone ε) {i j : Fin n} (hi : ε i = false) (hj : ε j = true) :
    (i : ℤ) < j := by
  by_contra hc
  have hji : j ≤ i := by
    rw [Fin.le_iff_val_le_val]
    omega
  have h3 := hε hji
  rw [hi, hj] at h3
  exact absurd h3 (by decide)

/- English proof (translation)
Establish `hpos : ∀ i : Fin n, ε i = true → ε i.rev = false → 0 < 2 * (i : ℤ) + 1 - n`. Introduce `i h1 h2`. Establish `h3` using `lt_of_sign hε h2 h1`. Rewrite `h3` using `[rev_cast]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hneg : ∀ i : Fin n, ε i = false → ε i.rev = true → 2 * (i : ℤ) + 1 - n < 0`. Introduce `i h1 h2`. Establish `h3` using `lt_of_sign hε h1 h2`. Rewrite `h3` using `[rev_cast]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨pr_pr ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `h1 : ε i ≤ ε j` using `hε hij`. Establish `h2 : ε j.rev ≤ ε i.rev` using `hε (Fin.rev_le_rev.mpr hij)`. Establish `hij' : (i : ℤ) ≤ j` using `by exact_mod_cast hij`.

Unfold `ht`. Use `split_ifs with a b b`. Conclude with `le_refl _`. Establish `key : ∀ x y z w : Bool, x ≤ z → w ≤ y → y = x → ¬w = z → z = true ∧ w = false`. Introduce `x y z w`.

Apply the tactic sequence `cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })`. Take `⟨hz, hw⟩` from `key _ _ _ _ h1 h2 a b`. Conclude with `(hpos j hz hw).le`. Establish `key : ∀ x y z w : Bool, x ≤ z → w ≤ y → ¬y = x → w = z → x = false ∧ y = true`. Introduce `x y z w`.

Apply the tactic sequence `cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })`. Take `⟨hx, hy⟩` from `key _ _ _ _ h1 h2 a b`. Conclude with `(hneg i hx hy).le`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`.

Unfold `ht pr`. Distinguish the cases in `h : ε i.rev = ε i`. Simplify using `[h]`. Establish `h' : ¬ε i = ε i.rev` using `fun e => h e.symm`. Simplify using `only [h, h', ↓reduceIte, Fin.rev_rev]`.

Rewrite using `[rev_cast]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i h`. Establish `h'` using `ht_eq_zero.mp h`. Unfold `pr`.

Rewrite using `[if_pos h']`. Introduce `i j hi hij`. Establish `hi' : ¬ε i.rev = ε i` using `fun e => hi (ht_eq_zero.mpr e)`. Establish `hj' : ¬ε j.rev = ε j` using `fun e => hi (hij.trans (ht_eq_zero.mpr e))`. Unfold `ht at hij`.

Rewrite `hij` using `[if_neg hi', if_neg hj']`. Use `ext`. Use linear arithmetic over natural numbers and integers. Introduce `i`. Unfold `wt sg`.

Apply the tactic sequence `split_ifs <;> norm_num`. Introduce `i`. Unfold `wt sg`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `i`.

Unfold `wt pr`. Distinguish the cases in `h : ε i.rev = ε i`. Simplify using `[h]`. Establish `h' : ¬ε i = ε i.rev` using `fun e => h e.symm`. Simplify using `[h, h']`.

Introduce `i j hi hj`. Establish `hi'` using `ht_eq_zero.mp hi`. Establish `hj'` using `ht_eq_zero.mp hj`. Establish `key : ∀ a b : Fin n, ε a.rev = ε a → ε b.rev = ε b → ε a = false → ε b = true → False`. Introduce `a b ha hb h1 h2`.

Establish `t1` using `lt_of_sign hε (ha.trans h1) h2`. Establish `t2` using `lt_of_sign hε h1 (hb.trans h2)`. Rewrite `t1`, `t2` using `[rev_cast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : ε i = ε j`.

Apply the tactic sequence `cases h1 : ε i <;> cases h2 : ε j`. Both sides reduce to the same expression. Conclude with `(key i j hi' hj' h1 h2).elim`. Conclude with `(key j i hj' hi' h2 h1).elim`. Both sides reduce to the same expression.

Unfold `wt sg`. Rewrite using `[if_pos hi', if_pos hj', he]`.
-/
theorem adapted {ε : Fin n → Bool} (hε : Monotone ε) : Adapted (pr ε) (ht ε) (wt ε) := by
  have hpos : ∀ i : Fin n, ε i = true → ε i.rev = false → 0 < 2 * (i : ℤ) + 1 - n := by
    intro i h1 h2
    have h3 := lt_of_sign hε h2 h1
    rw [rev_cast] at h3
    linarith
  have hneg : ∀ i : Fin n, ε i = false → ε i.rev = true → 2 * (i : ℤ) + 1 - n < 0 := by
    intro i h1 h2
    have h3 := lt_of_sign hε h1 h2
    rw [rev_cast] at h3
    linarith
  refine ⟨pr_pr ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : ε i ≤ ε j := hε hij
    have h2 : ε j.rev ≤ ε i.rev := hε (Fin.rev_le_rev.mpr hij)
    have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
    unfold ht
    split_ifs with a b b
    · exact le_refl _
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → y = x → ¬w = z → z = true ∧ w = false := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hz, hw⟩ := key _ _ _ _ h1 h2 a b
      exact (hpos j hz hw).le
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → ¬y = x → w = z → x = false ∧ y = true := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hx, hy⟩ := key _ _ _ _ h1 h2 a b
      exact (hneg i hx hy).le
    · linarith
  · intro i
    unfold ht pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp only [h, h', ↓reduceIte, Fin.rev_rev]
      rw [rev_cast]
      ring
  · intro i h
    have h' := ht_eq_zero.mp h
    unfold pr
    rw [if_pos h']
  · intro i j hi hij
    have hi' : ¬ε i.rev = ε i := fun e => hi (ht_eq_zero.mpr e)
    have hj' : ¬ε j.rev = ε j := fun e => hi (hij.trans (ht_eq_zero.mpr e))
    unfold ht at hij
    rw [if_neg hi', if_neg hj'] at hij
    ext
    omega
  · intro i
    unfold wt sg
    split_ifs <;> norm_num
  · intro i
    unfold wt sg
    split_ifs <;> simp
  · intro i
    unfold wt pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp [h, h']
  · intro i j hi hj
    have hi' := ht_eq_zero.mp hi
    have hj' := ht_eq_zero.mp hj
    have key : ∀ a b : Fin n, ε a.rev = ε a → ε b.rev = ε b → ε a = false → ε b = true → False := by
      intro a b ha hb h1 h2
      have t1 := lt_of_sign hε (ha.trans h1) h2
      have t2 := lt_of_sign hε h1 (hb.trans h2)
      rw [rev_cast] at t1 t2
      linarith
    have he : ε i = ε j := by
      cases h1 : ε i <;> cases h2 : ε j
      · rfl
      · exact (key i j hi' hj' h1 h2).elim
      · exact (key j i hj' hi' h2 h1).elim
      · rfl
    unfold wt sg
    rw [if_pos hi', if_pos hj', he]

/- English proof (translation)
Unfold `pr`. Distinguish the cases in `h : ε i.rev = ε i`. Simplify using `[h]`. Rewrite using `[if_neg h]`. Conclude with `⟨fun e => (h (by rw [e])).elim, fun e => (h e).elim⟩`.
-/
theorem pr_eq_iff {ε : Fin n → Bool} {i : Fin n} : pr ε i = i ↔ ε i.rev = ε i := by
  unfold pr
  by_cases h : ε i.rev = ε i
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun e => (h (by rw [e])).elim, fun e => (h e).elim⟩

/- English proof (translation)
Establish `hA` using `adapted hε`. Establish `hp : ∀ i, pr ε (pr ε i) = i` using `pr_pr ε`. Establish `hqq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2`. Rewrite using `[← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]`. Evaluate the numerical expressions.

Establish `hqs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹`. Rewrite using `[star_inv₀, Complex.star_def, Complex.conj_ofReal]`. Apply the tactic sequence `have hsg2 : ∀ i, sg ε i * sg ε i = 1 := fun i => by unfold sg; split_ifs <;> norm_num`. Apply the tactic sequence `have hsgs : ∀ i, star (sg ε i) = sg ε i := fun i => by unfold sg; split_ifs <;> simp`. Establish `hnf : ∀ i, ¬ε i.rev = ε i → pr ε i = i.rev ∧ ¬ε (pr ε i).rev = ε (pr ε i) ∧ sg ε (pr ε i) = -sg ε i`.

Introduce `i h`. Establish `hpi : pr ε i = i.rev` using `by unfold pr; rw [if_neg h]`. Use `⟨hpi, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpi, Fin.rev_rev]`. Conclude with `fun e => h e.symm`.

Rewrite using `[hpi]`. Unfold `sg`. Apply the tactic sequence `cases hx : ε i <;> cases hy : ε i.rev <;> simp_all`. Generalize the expression as in `hq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = q at hqq hqs`. Set `α : Fin n → ℂ` to `fun i => if ε i.rev = ε i then 1 else q`.

Set `β : Fin n → ℂ` to `fun i => if ε i.rev = ε i then 0 else sg ε i * q`. Apply the tactic sequence `have hαs : ∀ i, star (α i) = α i := fun i => by simp only [α]; split_ifs <;> simp [hqs]`. Apply the tactic sequence `have hβs : ∀ i, star (β i) = β i := fun i => by simp only [β]; split_ifs <;> simp [hqs, hsgs]`. Establish `hVt : (dp (pr ε) α β).conjTranspose = dp (pr ε) α (fun i => β (pr ε i))`. Rewrite using `[dp_conjTranspose hp]`.

Simplify using `only [hαs, hβs]`. Establish `hJ : Jm ε = dp (pr ε) (sg ε) 0`. Rewrite using `[dp_diagonal]`. Both sides reduce to the same expression. Apply `Dec.of_conj (V := dp (pr ε) α β)` to reduce the goal to its premises.

Rewrite using `[hVt, dp_mul_dp hp, ← Matrix.diagonal_one, ← dp_diagonal (pr ε)]`. Apply `dp_congr` to reduce the goal to its premises. Introduce `i hi`. Establish `h` using `pr_eq_iff.mp hi`. Simplify using `[α, β, h, hi]`.

Introduce `i hi`. Establish `h : ¬ε i.rev = ε i` using `fun e => hi (pr_eq_iff.mpr e)`. Take `⟨hpi, hpp, hs⟩` from `hnf i h`. Simplify using `only [α, β, h, hpp, ↓reduceIte, hs, Pi.zero_apply]`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `(1 + sg ε i * sg ε i) * hqq + (1 / 2 : ℂ) * hsg2 i`. Expand and normalize the polynomial expressions, which then agree. Establish `key : (dp (pr ε) α β).conjTranspose * Jm ε * dp (pr ε) α β = dp (pr ε) 0 (wt ε)`. Rewrite using `[hVt, hJ, dp_mul_dp hp, dp_mul_dp hp]`. Apply `dp_congr` to reduce the goal to its premises.

Introduce `i hi`. Establish `h` using `pr_eq_iff.mp hi`. Simplify using `[α, β, h, hi, wt]`. Introduce `i hi`. Establish `h : ¬ε i.rev = ε i` using `fun e => hi (pr_eq_iff.mpr e)`.

Take `⟨hpi, hpp, hs⟩` from `hnf i h`. Simplify using `only [α, β, wt, h, hpp, ↓reduceIte, hs, Pi.zero_apply]`. Prove the components needed by the constructor for the conclusion. Take the linear combination `(-(sg ε i) * q * q) * hsg2 i`. Take the linear combination `(2 * sg ε i * sg ε i) * hqq + hsg2 i`.

Rewrite using `[key]`. Conclude with `hA.dec`.
-/
theorem dec_of_monotone {ε : Fin n → Bool} (hε : Monotone ε) : Dec (Jm ε) := by
  classical
  have hA := adapted hε
  have hp : ∀ i, pr ε (pr ε i) = i := pr_pr ε
  have hqq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hqs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hsg2 : ∀ i, sg ε i * sg ε i = 1 := fun i => by unfold sg; split_ifs <;> norm_num
  have hsgs : ∀ i, star (sg ε i) = sg ε i := fun i => by unfold sg; split_ifs <;> simp
  have hnf : ∀ i, ¬ε i.rev = ε i →
      pr ε i = i.rev ∧ ¬ε (pr ε i).rev = ε (pr ε i) ∧ sg ε (pr ε i) = -sg ε i := by
    intro i h
    have hpi : pr ε i = i.rev := by unfold pr; rw [if_neg h]
    refine ⟨hpi, ?_, ?_⟩
    · rw [hpi, Fin.rev_rev]
      exact fun e => h e.symm
    · rw [hpi]
      unfold sg
      cases hx : ε i <;> cases hy : ε i.rev <;> simp_all
  generalize hq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = q at hqq hqs
  let α : Fin n → ℂ := fun i => if ε i.rev = ε i then 1 else q
  let β : Fin n → ℂ := fun i => if ε i.rev = ε i then 0 else sg ε i * q
  have hαs : ∀ i, star (α i) = α i := fun i => by simp only [α]; split_ifs <;> simp [hqs]
  have hβs : ∀ i, star (β i) = β i := fun i => by simp only [β]; split_ifs <;> simp [hqs, hsgs]
  have hVt : (dp (pr ε) α β).conjTranspose = dp (pr ε) α (fun i => β (pr ε i)) := by
    rw [dp_conjTranspose hp]
    simp only [hαs, hβs]
  have hJ : Jm ε = dp (pr ε) (sg ε) 0 := by
    rw [dp_diagonal]
    rfl
  apply Dec.of_conj (V := dp (pr ε) α β)
  · rw [hVt, dp_mul_dp hp, ← Matrix.diagonal_one, ← dp_diagonal (pr ε)]
    apply dp_congr
    · intro i hi
      have h := pr_eq_iff.mp hi
      simp [α, β, h, hi]
    · intro i hi
      have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
      obtain ⟨hpi, hpp, hs⟩ := hnf i h
      simp only [α, β, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
      constructor
      · linear_combination (1 + sg ε i * sg ε i) * hqq + (1 / 2 : ℂ) * hsg2 i
      · ring
  · have key : (dp (pr ε) α β).conjTranspose * Jm ε * dp (pr ε) α β = dp (pr ε) 0 (wt ε) := by
      rw [hVt, hJ, dp_mul_dp hp, dp_mul_dp hp]
      apply dp_congr
      · intro i hi
        have h := pr_eq_iff.mp hi
        simp [α, β, h, hi, wt]
      · intro i hi
        have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
        obtain ⟨hpi, hpp, hs⟩ := hnf i h
        simp only [α, β, wt, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
        constructor
        · linear_combination (-(sg ε i) * q * q) * hsg2 i
        · linear_combination (2 * sg ε i * sg ε i) * hqq + hsg2 i
    rw [key]
    exact hA.dec

/- English proof (translation)
Set `σ` to `Tuple.sort ε`. Establish `hmono : Monotone (ε ∘ σ)` using `Tuple.monotone_sort ε`. Set `V : Matrix (Fin n) (Fin n) ℂ` to `(1 : Matrix (Fin n) (Fin n) ℂ).submatrix id σ`. Establish `hV : ∀ H : Matrix (Fin n) (Fin n) ℂ, V.conjTranspose * H * V = H.submatrix σ σ`. Introduce `H`.

Use extensionality with `a b`. Simplify using `[V, Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]`. Apply `Dec.of_conj (V := V)` to reduce the goal to its premises. Establish `h1` using `hV 1`. Rewrite `h1` using `[Matrix.mul_one]`.

Rewrite using `[h1]`. Conclude with `Matrix.submatrix_one_equiv σ`. Rewrite using `[hV]`. Establish `h2 : (Jm ε).submatrix σ σ = Jm (ε ∘ σ)`. Unfold `Jm`.

Rewrite using `[Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `dec_of_monotone hmono`.
-/
theorem dec_Jm (ε : Fin n → Bool) : Dec (Jm ε) := by
  classical
  let σ := Tuple.sort ε
  have hmono : Monotone (ε ∘ σ) := Tuple.monotone_sort ε
  let V : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id σ
  have hV : ∀ H : Matrix (Fin n) (Fin n) ℂ, V.conjTranspose * H * V = H.submatrix σ σ := by
    intro H
    ext a b
    simp [V, Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  apply Dec.of_conj (V := V)
  · have h1 := hV 1
    rw [Matrix.mul_one] at h1
    rw [h1]
    exact Matrix.submatrix_one_equiv σ
  · rw [hV]
    have h2 : (Jm ε).submatrix σ σ = Jm (ε ∘ σ) := by
      unfold Jm
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [h2]
    exact dec_of_monotone hmono

end CholeskyDecomposition

/- English proof (translation)
Introduce `n ε`. Take `⟨U, hU, h⟩` from `CholeskyDecomposition.dec_Jm ε`. Use `⟨U, hU, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨k, hk, s, hkJ, hsJ, rfl, htri⟩` from `h g hg`. Use `⟨k, ⟨hk, ?_⟩, s, hsJ, rfl, htri⟩` and prove the remaining obligations.

Establish `hk1 : k * k.conjTranspose = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff.mp hk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem iwasawa_decomposition_unitary_group : IwaAll := by
  intro n ε
  obtain ⟨U, hU, h⟩ := CholeskyDecomposition.dec_Jm ε
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨k, hk, s, hkJ, hsJ, rfl, htri⟩ := h g hg
  refine ⟨k, ⟨hk, ?_⟩, s, hsJ, rfl, htri⟩
  have hk1 : k * k.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hk
  calc k * Jm ε = k * (k.conjTranspose * Jm ε * k) := by rw [hkJ]
    _ = k * k.conjTranspose * Jm ε * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * k := by rw [hk1, Matrix.one_mul]

end CompanionTheory.D.gk.admitted
