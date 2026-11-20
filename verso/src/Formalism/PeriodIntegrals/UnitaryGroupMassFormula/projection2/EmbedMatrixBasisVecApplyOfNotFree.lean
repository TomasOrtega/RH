import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.GaStep

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n' c n : ℕ}

/- English proof (translation)
Establish `hs : n' + i < n' + (c + 1)` using `by omega`. Establish `he : eN k (n' + (c + 1)) (n' + i) = Pi.single (⟨n' + i, hs⟩ : Fin (n' + (c + 1))) 1`. Use function extensionality and compare the values at `s`. Unfold `eN`. Distinguish the cases in `h : (s : ℕ) = n' + i`.

Establish `: s = ⟨n' + i, hs⟩` using `Fin.ext h`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `: s ≠ ⟨n' + i, hs⟩` using `fun e => h (by rw [e])`. Simplify using `[h, this]`.

Establish `key : ∀ (A : Matrix (Fin (n + c)) (Fin (n' + (c + 1))) k) (j : Fin (n' + (c + 1))), Matrix.toLin' A (Pi.single j 1) l = A l j`. Introduce `A j`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Rewrite using `[he]`.

Unfold `xx1`. Rewrite using `[key, Matrix.of_apply, dif_neg (show ¬ IsFree n' n c l.1 (⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 from hf), dif_neg (show ¬ ((⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 < n') by show ¬ (n' + i < n'); omega)]`. Use `show (if l.1 = n + (n' + i - n') then (1 : k) else 0) = _`. Rewrite using `[Nat.add_sub_cancel_left]`.
-/
theorem embedMatrix_basisVec_apply_of_not_free (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k) (i : ℕ) (hi : i < c)
    (l : Fin (n + c)) (hf : ¬ IsFree n' n c l.1 (n' + i)) :
    xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) l = if l.1 = n + i then 1 else 0 := by
  have hs : n' + i < n' + (c + 1) := by omega
  have he : eN k (n' + (c + 1)) (n' + i) = Pi.single (⟨n' + i, hs⟩ : Fin (n' + (c + 1))) 1 := by
    funext s
    unfold eN
    by_cases h : (s : ℕ) = n' + i
    · have : s = ⟨n' + i, hs⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨n' + i, hs⟩ := fun e => h (by rw [e])
      simp [h, this]
  have key : ∀ (A : Matrix (Fin (n + c)) (Fin (n' + (c + 1))) k) (j : Fin (n' + (c + 1))),
      Matrix.toLin' A (Pi.single j 1) l = A l j := by
    intro A j
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  rw [he]
  unfold xx1
  rw [key, Matrix.of_apply,
    dif_neg (show ¬ IsFree n' n c l.1 (⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 from hf),
    dif_neg (show ¬ ((⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 < n') by show ¬ (n' + i < n'); omega)]
  show (if l.1 = n + (n' + i - n') then (1 : k) else 0) = _
  rw [Nat.add_sub_cancel_left]

/- English proof (translation)
Introduce `k _ n' c n xj tt`. Establish `heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1`. Introduce `N j hj`. Use function extensionality and compare the values at `s`. Unfold `eN`.

Distinguish the cases in `h : (s : ℕ) = j`. Establish `: s = ⟨j, hj⟩` using `Fin.ext h`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `: s ≠ ⟨j, hj⟩` using `fun e => h (by rw [e])`.

Simplify using `[h, this]`. Establish `hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) → ¬ IsFree n' n c l.1 (n' + i)`. Introduce `l i hi h`. Unfold `IsFree`. Use linear arithmetic over natural numbers and integers.

Set `M : Matrix (Fin (n + c)) (Fin (n + c)) k` to `Matrix.of fun l s => if s.1 < n then (if l = s then 1 else 0) else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l`. Establish `hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0`. Introduce `l s hs`. Simplify using `[M, hs]`. Establish `hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n → M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l`.

Introduce `l j hj hn`. Simplify using `[M, hn]`. Establish `hT : ∀ l s : Fin (n + c), s < l → M l s = 0`. Introduce `l s hsl`. Establish `hsl' : s.1 < l.1` using `hsl`.

Distinguish the cases in `hs : s.1 < n`. Rewrite using `[hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]`. Establish `hsc` using `s.2`. Rewrite using `[show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs, embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))), if_neg (by omega)]`. Establish `hD : ∀ s : Fin (n + c), M s s = 1`.

Introduce `s`. Distinguish the cases in `hs : s.1 < n`. Rewrite using `[hM_lt s s hs, if_pos rfl]`. Establish `hsc` using `s.2`. Rewrite using `[show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs, embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))), if_pos (by simp; omega)]`.

Establish `hUT : M.BlockTriangular id` using `fun i j hij => hT i j hij`. Establish `hdet : IsUnit M.det`. Rewrite using `[Matrix.det_of_upperTriangular hUT]`. Simplify using `[hD]`. Set `hinv : Invertible M` to `Matrix.invertibleOfIsUnitDet M hdet`.

Set `ν` to `M.toLinearEquiv' hinv`. Establish `hν : ∀ x, ν x = M.mulVec x`. Introduce `x`. Use `show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _`. Rewrite using `[Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]`.

Establish `hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩`. Introduce `j hj`. Rewrite using `[heN _ j hj, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i))`.

Introduce `i hi`. Rewrite using `[hν, hcol (n + i) (by omega)]`. Use function extensionality and compare the values at `l`. Rewrite using `[hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]`. Establish `hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0`.

Introduce `v s hs`. Simplify using `[inX, hs]`. Establish `hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0`. Introduce `i hi`. Use function extensionality and compare the values at `l`.

Unfold `eN`. Use `split_ifs with h`. Use `l.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Use `⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩` and prove the remaining obligations. Introduce `i v hv`. Establish `hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0` using `hv`. Use `show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0`. Introduce `l hl`.

Establish `hl' : n + i ≤ l.1` using `by simpa using hl`. Rewrite using `[hν]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `s _`.

Distinguish the cases in `hs : s.1 < n + i`. Rewrite using `[hT l s (show s.1 < l.1 by omega), zero_mul]`. Rewrite using `[hv' s (by simpa using hs), mul_zero]`. Break down `Nat.eq_zero_or_pos c with hc | hc` into its components or cases. Rewrite using `[show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]`.

Establish `h0` using `hνcol 0 hc`. Establish `e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0)`. Use function extensionality and compare the values at `l`. Rewrite using `[embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]`. Both sides reduce to the same expression.

Conclude with `h0.trans e1`. Introduce `i show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0`. Introduce `l hl`. Establish `hl' : n + i ≤ l.1` using `by simpa using hl`. Distinguish the cases in `hi : i < c`.

Rewrite using `[hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))] show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0`. Conclude with `sub_self _`. Rewrite using `[hzero i hi, map_zero, sub_zero]`. Both sides reduce to the same expression. Introduce `v`.

Rewrite using `[hν]`. Use function extensionality and compare the values at `l`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[hD l, one_mul]`.

Introduce `s _ hsl`. Distinguish the cases in `hs : s.1 < n`. Rewrite using `[hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]`. Rewrite using `[hinX v s hs, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ l) h`.
-/
theorem nElem : NElem := by
  intro k _ n' c n xj tt
  classical

  have heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1 := by
    intro N j hj
    funext s
    unfold eN
    by_cases h : (s : ℕ) = j
    · have : s = ⟨j, hj⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp [h, this]
  have hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) →
      ¬ IsFree n' n c l.1 (n' + i) := by
    intro l i hi h
    unfold IsFree
    omega

  let M : Matrix (Fin (n + c)) (Fin (n + c)) k := Matrix.of fun l s =>
    if s.1 < n then (if l = s then 1 else 0)
    else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l
  have hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0 := by
    intro l s hs
    simp [M, hs]
  have hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n →
      M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l := by
    intro l j hj hn
    simp [M, hn]
  have hT : ∀ l s : Fin (n + c), s < l → M l s = 0 := by
    intro l s hsl
    have hsl' : s.1 < l.1 := hsl
    by_cases hs : s.1 < n
    · rw [hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))),
        if_neg (by omega)]
  have hD : ∀ s : Fin (n + c), M s s = 1 := by
    intro s
    by_cases hs : s.1 < n
    · rw [hM_lt s s hs, if_pos rfl]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))),
        if_pos (by simp; omega)]
  have hUT : M.BlockTriangular id := fun i j hij => hT i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hUT]
    simp [hD]
  let hinv : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  let ν := M.toLinearEquiv' hinv
  have hν : ∀ x, ν x = M.mulVec x := by
    intro x
    show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩ := by
    intro j hj
    rw [heN _ j hj, Matrix.mulVec_single_one]
    rfl
  have hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) := by
    intro i hi
    rw [hν, hcol (n + i) (by omega)]
    funext l
    rw [hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0 := by
    intro v s hs
    simp [inX, hs]
  have hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0 := by
    intro i hi
    funext l
    unfold eN
    split_ifs with h
    · have := l.2
      omega
    · rfl
  refine ⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩
  · intro i v hv
    have hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0 := hv
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    rw [hν]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.1 < n + i
    · rw [hT l s (show s.1 < l.1 by omega), zero_mul]
    · rw [hv' s (by simpa using hs), mul_zero]
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]
    · have h0 := hνcol 0 hc
      have e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0) := by
        funext l
        rw [embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]
        rfl
      exact h0.trans e1
  · intro i
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) →
      (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    by_cases hi : i < c
    · rw [hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))]
      show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0
      exact sub_self _
    · rw [hzero i hi, map_zero, sub_zero]
      rfl
  · intro v
    rw [hν]
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single l]
    · rw [hD l, one_mul]
    · intro s _ hsl
      by_cases hs : s.1 < n
      · rw [hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]
      · rw [hinX v s hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h

end PI.OneCosetSharp.W
