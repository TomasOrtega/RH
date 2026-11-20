import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `hpq : p ≠ q` using `fun e => by have := congrArg Fin.val e; omega`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (· < p)]`. Use `congr 1`. Establish `hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun r => ¬ r < p)`. Introduce `x hx`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def]`. Apply the tactic sequence `rcases hx with rfl | rfl <;> omega`. Rewrite using `[← Finset.sum_subset hsub, Finset.sum_pair hpq]`. Introduce `x hx hx'`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def] at hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'`. Apply `hf` to reduce the goal to its premises. Rewrite using `[Fin.lt_def]`. Establish `h1 : (x : ℕ) ≠ p` using `fun e => hx'.1 (Fin.ext e)`.

Establish `h2 : (x : ℕ) ≠ q` using `fun e => hx'.2 (Fin.ext e)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exch_sum_split {N : ℕ} (p q : Fin N) (hq : (q : ℕ) = p + 1) (f : Fin N → ℝ)
    (hf : ∀ r, q < r → f r = 0) :
    ∑ r, f r = ∑ r ∈ Finset.univ.filter (· < p), f r + (f p + f q) := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < p)]
  congr 1
  have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun r => ¬ r < p) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def]
    rcases hx with rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub, Finset.sum_pair hpq]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
  apply hf
  rw [Fin.lt_def]
  have h1 : (x : ℕ) ≠ p := fun e => hx'.1 (Fin.ext e)
  have h2 : (x : ℕ) ≠ q := fun e => hx'.2 (Fin.ext e)
  omega

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]`. Establish `hsub : (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).submatrix (Fin.last m).succAbove (Fin.last m).succAbove = X.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last]`. Rewrite using `[Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]`.

Rewrite using `[hsub, Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, Even.neg_one_pow ⟨m, rfl⟩, one_mul]`. Introduce `j _ hj`. Rewrite using `[Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem det_updateRow_last_single_eq_mul_det_submatrix {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (x : ℝ) :
    (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).det =
      x * (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]
  · have hsub : (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).submatrix
        (Fin.last m).succAbove (Fin.last m).succAbove = X.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, Even.neg_one_pow ⟨m, rfl⟩, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `N k a n g g' p q hk hn1 hn0 hq hg hg'`. Establish `hG : gᵀ * g = (diagonal a * n)ᵀ * (diagonal a * n)`. Rewrite using `[hg]`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]`.

Establish `hG' : g'ᵀ * g' = (gᵀ * g).submatrix (Equiv.swap p q) (Equiv.swap p q)`. Rewrite using `[hg']`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[hG', hG]`.

Use `set M : Matrix (Fin N) (Fin N) ℝ := diagonal a * n with hM`. Establish `hMe : ∀ i j, M i j = a i * n i j` using `fun i j => by simp [hM, Matrix.diagonal_mul]`. Establish `hMl : ∀ i j, j < i → M i j = 0` using `fun i j h => by rw [hMe, hn0 i j h, mul_zero]`. Establish `hMd : ∀ i, M i i = a i` using `fun i => by rw [hMe, hn1, mul_one]`. Use `⟨fun j hj hjq => ?_, fun h => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hjp : j ≤ (p : ℕ)`. Use `congr 1`. Establish `hfix : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj z`. Introduce `z`. Establish `hz` using `z.isLt`.

Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.coe_castLE] at this`. Use linear arithmetic over natural numbers and integers.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.coe_castLE] at this`. Use linear arithmetic over natural numbers and integers. Use extensionality with `x y`.

Simplify using `only [Matrix.submatrix_apply, hfix]`. Establish `hpj : (p : ℕ) < j` using `by omega`. Establish `hqj : (q : ℕ) < j` using `by omega`. Establish `e1 : Fin.castLE hj ⟨p, hpj⟩ = p` using `Fin.ext rfl`. Establish `e2 : Fin.castLE hj ⟨q, hqj⟩ = q` using `Fin.ext rfl`.

Establish `hs : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj (Equiv.swap ⟨p, hpj⟩ ⟨q, hqj⟩ z)`. Introduce `z`. Use `(Fin.castLE_injective hj).swap_apply ⟨p, hpj⟩ ⟨q, hqj⟩ z` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis. Establish `hsub : ((Mᵀ * M).submatrix (Equiv.swap p q) (Equiv.swap p q)).submatrix (Fin.castLE hj) (Fin.castLE hj) = ((Mᵀ * M).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩)`.

Use extensionality with `x y`. Simplify using `only [Matrix.submatrix_apply, hs]`. Rewrite using `[hsub, Matrix.det_submatrix_equiv_self]`. Take `⟨p, hp⟩` from `p`. Take `⟨q, hqN⟩` from `q`.

Express the relevant statement in the definitionally equal form `q = p + 1 at hq`. Substitute `hq` using the available equality. Establish `h' : p + 1 ≤ N` using `h`. Use `set P : Fin N := ⟨p, hp⟩ with hP`. Use `set Q : Fin N := ⟨p + 1, hqN⟩ with hQ`.

Use `set σ := Equiv.swap P Q with hσ`. Use `set c : Fin (p + 1) → Fin N := Fin.castLE h' with hc`. Use `show (((Mᵀ * M).submatrix σ σ).submatrix c c).det = _`. Establish `hcl : c (Fin.last p) = P` using `Fin.ext rfl`. Establish `hσc : ∀ s : Fin (p + 1), s ≠ Fin.last p → σ (c s) = c s`.

Introduce `s hs`. Establish `h1 : (s : ℕ) < p`. Use `s.isLt` as an intermediate fact. Establish `: (s : ℕ) ≠ p` using `fun e => hs (Fin.ext e)`. Use linear arithmetic over natural numbers and integers.

Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Express the relevant statement in the definitionally equal form `(s : ℕ) = p at this`. Use linear arithmetic over natural numbers and integers.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Express the relevant statement in the definitionally equal form `(s : ℕ) = p + 1 at this`. Use linear arithmetic over natural numbers and integers. Establish `hσl : σ (c (Fin.last p)) = Q`.

Rewrite using `[hcl]`. Conclude with `Equiv.swap_apply_left P Q`. Establish `hle : ∀ s, σ (c s) ≤ Q`. Introduce `s`. Distinguish the cases in `hs : s = Fin.last p`.

Rewrite using `[hs, hσl]`. Rewrite using `[hσc s hs, Fin.le_def]`. Express the relevant statement in the definitionally equal form `(s : ℕ) ≤ p + 1`. Use `s.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `set B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun s i => M (c s) (σ (c i)) with hB`. Establish `hBe : ∀ s i, B s i = M (c s) (σ (c i))` using `fun s i => rfl`. Use `set emb : Fin p ↪ Fin N := ⟨fun i : Fin p => c i.castSucc, fun x y e => by simpa [Fin.ext_iff, hc] using e⟩ with hemb`. Establish `hembx : ∀ x, emb x = c x.castSucc` using `fun x => rfl`. Establish `hfilt : Finset.univ.filter (· < P) = (Finset.univ : Finset (Fin p)).map emb`.

Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hl`. Conclude with `⟨⟨l, hl⟩, Fin.ext rfl⟩`.

Introduce and unpack `⟨i, _, rfl⟩`. Conclude with `i.isLt`. Establish `hX : ((Mᵀ * M).submatrix σ σ).submatrix c c = (Bᵀ * B).updateRow (Fin.last p) ((Bᵀ * B) (Fin.last p) + Pi.single (Fin.last p) (a Q ^ 2))`. Use extensionality with `i j`. Establish `hsum : (((Mᵀ * M).submatrix σ σ).submatrix c c) i j = (Bᵀ * B) i j + M Q (σ (c i)) * M Q (σ (c j))`.

Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hBe]`. Rewrite using `[exch_sum_split P Q rfl _ (fun r hr => by rw [hMl r _ (lt_of_le_of_lt (hle i) hr), zero_mul]), Fin.sum_univ_castSucc, hfilt, Finset.sum_map, hcl]`. Simplify using `only [hembx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`.

Distinguish the cases in `hi : i = Fin.last p`. Substitute `hi` using the available equality. Rewrite using `[Matrix.updateRow_self, Pi.add_apply]`. Distinguish the cases in `hj : j = Fin.last p`. Substitute `hj` using the available equality.

Rewrite using `[hσl, hMd, Pi.single_eq_same]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hσl, hσc j hj, hMl Q (c j) (Fin.lt_def.2 j.isLt), mul_zero, Pi.single_eq_of_ne hj]`. Rewrite using `[Matrix.updateRow_ne hi, hσc i hi, hMl Q (c i) (Fin.lt_def.2 i.isLt), zero_mul, add_zero]`. Establish `hBT : B.BlockTriangular id`.

Introduce `s i hi`. Establish `hil : i ≠ Fin.last p` using `fun e => by`. Rewrite `hi` using `[e]`. Conclude with `(not_lt.2 (Fin.le_last s)) hi`. Rewrite using `[hBe, hσc i hil]`.

Conclude with `hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 hi))`. Establish `hdB : B.det = (∏ i : Fin p, a (c i.castSucc)) * (a P * n P Q)`. Rewrite using `[Matrix.det_of_upperTriangular hBT, Fin.prod_univ_castSucc]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]`. Rewrite using `[hBe, hσl, hcl, hMe]`. Establish `hminor : (Bᵀ * B).submatrix Fin.castSucc Fin.castSucc = (B.submatrix Fin.castSucc Fin.castSucc)ᵀ * B.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]`.

Rewrite using `[Fin.sum_univ_castSucc]`. Establish `hz : B (Fin.last p) i.castSucc = 0`. Rewrite using `[hBe, hσc _ (Fin.castSucc_lt_last i).ne, hcl]`. Conclude with `hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 (Fin.castSucc_lt_last i)))`. Rewrite using `[hz, zero_mul, add_zero]`.

Establish `hBT' : (B.submatrix Fin.castSucc Fin.castSucc).BlockTriangular id`. Introduce `s i hi`. Conclude with `hBT (Fin.castSucc_lt_castSucc_iff.2 hi)`. Establish `hdB' : (B.submatrix Fin.castSucc Fin.castSucc).det = ∏ i : Fin p, a (c i.castSucc)`. Rewrite using `[Matrix.det_of_upperTriangular hBT']`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_apply, hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]`. Establish `hprod : ∏ l ∈ Finset.univ.filter (· < P), a l ^ 2 = (∏ i : Fin p, a (c i.castSucc)) ^ 2`. Rewrite using `[hfilt, Finset.prod_map, ← Finset.prod_pow]`. Simplify using `only [hembx]`.

Rewrite using `[hX, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, det_updateRow_last_single_eq_mul_det_submatrix, hminor, Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose, hdB, hdB', hprod]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_minor_swap_columns : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n g g' : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (q : ℕ) = p + 1 → g = k * diagonal a * n → g' = g.submatrix id (Equiv.swap p q) → (∀ (j : ℕ) (h : j ≤ N), j ≠ q → ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = ((gᵀ * g).submatrix (Fin.castLE h) (Fin.castLE h)).det) ∧ ∀ h : (q : ℕ) ≤ N, ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
  intro N k a n g g' p q hk hn1 hn0 hq hg hg'

  have hG : gᵀ * g = (diagonal a * n)ᵀ * (diagonal a * n) := by
    rw [hg]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]
  have hG' : g'ᵀ * g' = (gᵀ * g).submatrix (Equiv.swap p q) (Equiv.swap p q) := by
    rw [hg']
    ext i j
    simp [Matrix.mul_apply]
  rw [hG', hG]
  set M : Matrix (Fin N) (Fin N) ℝ := diagonal a * n with hM
  have hMe : ∀ i j, M i j = a i * n i j := fun i j => by simp [hM, Matrix.diagonal_mul]
  have hMl : ∀ i j, j < i → M i j = 0 := fun i j h => by rw [hMe, hn0 i j h, mul_zero]
  have hMd : ∀ i, M i i = a i := fun i => by rw [hMe, hn1, mul_one]
  refine ⟨fun j hj hjq => ?_, fun h => ?_⟩
  · by_cases hjp : j ≤ (p : ℕ)
    ·
      congr 1
      have hfix : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj z := by
        intro z
        have hz := z.isLt
        apply Equiv.swap_apply_of_ne_of_ne
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
      ext x y
      simp only [Matrix.submatrix_apply, hfix]
    ·
      have hpj : (p : ℕ) < j := by omega
      have hqj : (q : ℕ) < j := by omega
      have e1 : Fin.castLE hj ⟨p, hpj⟩ = p := Fin.ext rfl
      have e2 : Fin.castLE hj ⟨q, hqj⟩ = q := Fin.ext rfl
      have hs : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) =
          Fin.castLE hj (Equiv.swap ⟨p, hpj⟩ ⟨q, hqj⟩ z) := by
        intro z
        have := (Fin.castLE_injective hj).swap_apply ⟨p, hpj⟩ ⟨q, hqj⟩ z
        rwa [e1, e2] at this
      have hsub : ((Mᵀ * M).submatrix (Equiv.swap p q) (Equiv.swap p q)).submatrix (Fin.castLE hj)
          (Fin.castLE hj) = ((Mᵀ * M).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
          (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) := by
        ext x y
        simp only [Matrix.submatrix_apply, hs]
      rw [hsub, Matrix.det_submatrix_equiv_self]
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hqN⟩ := q
    change q = p + 1 at hq
    subst hq
    have h' : p + 1 ≤ N := h
    set P : Fin N := ⟨p, hp⟩ with hP
    set Q : Fin N := ⟨p + 1, hqN⟩ with hQ
    set σ := Equiv.swap P Q with hσ
    set c : Fin (p + 1) → Fin N := Fin.castLE h' with hc
    show (((Mᵀ * M).submatrix σ σ).submatrix c c).det = _
    have hcl : c (Fin.last p) = P := Fin.ext rfl
    have hσc : ∀ s : Fin (p + 1), s ≠ Fin.last p → σ (c s) = c s := by
      intro s hs
      have h1 : (s : ℕ) < p := by
        have := s.isLt
        have : (s : ℕ) ≠ p := fun e => hs (Fin.ext e)
        omega
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p at this
        omega
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p + 1 at this
        omega
    have hσl : σ (c (Fin.last p)) = Q := by
      rw [hcl]
      exact Equiv.swap_apply_left P Q
    have hle : ∀ s, σ (c s) ≤ Q := by
      intro s
      by_cases hs : s = Fin.last p
      · rw [hs, hσl]
      · rw [hσc s hs, Fin.le_def]
        change (s : ℕ) ≤ p + 1
        have := s.isLt
        omega

    set B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun s i => M (c s) (σ (c i)) with hB
    have hBe : ∀ s i, B s i = M (c s) (σ (c i)) := fun s i => rfl
    set emb : Fin p ↪ Fin N :=
      ⟨fun i : Fin p => c i.castSucc, fun x y e => by simpa [Fin.ext_iff, hc] using e⟩ with hemb
    have hembx : ∀ x, emb x = c x.castSucc := fun x => rfl
    have hfilt : Finset.univ.filter (· < P) = (Finset.univ : Finset (Fin p)).map emb := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hl
        exact ⟨⟨l, hl⟩, Fin.ext rfl⟩
      · rintro ⟨i, _, rfl⟩
        exact i.isLt

    have hX : ((Mᵀ * M).submatrix σ σ).submatrix c c =
        (Bᵀ * B).updateRow (Fin.last p) ((Bᵀ * B) (Fin.last p) + Pi.single (Fin.last p) (a Q ^ 2)) := by
      ext i j
      have hsum : (((Mᵀ * M).submatrix σ σ).submatrix c c) i j =
          (Bᵀ * B) i j + M Q (σ (c i)) * M Q (σ (c j)) := by
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hBe]
        rw [exch_sum_split P Q rfl _ (fun r hr => by rw [hMl r _ (lt_of_le_of_lt (hle i) hr), zero_mul]),
          Fin.sum_univ_castSucc, hfilt, Finset.sum_map, hcl]
        simp only [hembx]
        ring
      rw [hsum]
      by_cases hi : i = Fin.last p
      · subst hi
        rw [Matrix.updateRow_self, Pi.add_apply]
        by_cases hj : j = Fin.last p
        · subst hj
          rw [hσl, hMd, Pi.single_eq_same]
          ring
        · rw [hσl, hσc j hj, hMl Q (c j) (Fin.lt_def.2 j.isLt), mul_zero, Pi.single_eq_of_ne hj]
      · rw [Matrix.updateRow_ne hi, hσc i hi, hMl Q (c i) (Fin.lt_def.2 i.isLt), zero_mul, add_zero]
    have hBT : B.BlockTriangular id := by
      intro s i hi
      have hil : i ≠ Fin.last p := fun e => by
        rw [e] at hi
        exact (not_lt.2 (Fin.le_last s)) hi
      rw [hBe, hσc i hil]
      exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 hi))
    have hdB : B.det = (∏ i : Fin p, a (c i.castSucc)) * (a P * n P Q) := by
      rw [Matrix.det_of_upperTriangular hBT, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
      · rw [hBe, hσl, hcl, hMe]
    have hminor : (Bᵀ * B).submatrix Fin.castSucc Fin.castSucc =
        (B.submatrix Fin.castSucc Fin.castSucc)ᵀ * B.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Fin.sum_univ_castSucc]
      have hz : B (Fin.last p) i.castSucc = 0 := by
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hcl]
        exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 (Fin.castSucc_lt_last i)))
      rw [hz, zero_mul, add_zero]
    have hBT' : (B.submatrix Fin.castSucc Fin.castSucc).BlockTriangular id := by
      intro s i hi
      exact hBT (Fin.castSucc_lt_castSucc_iff.2 hi)
    have hdB' : (B.submatrix Fin.castSucc Fin.castSucc).det = ∏ i : Fin p, a (c i.castSucc) := by
      rw [Matrix.det_of_upperTriangular hBT']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Matrix.submatrix_apply, hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
    have hprod : ∏ l ∈ Finset.univ.filter (· < P), a l ^ 2 = (∏ i : Fin p, a (c i.castSucc)) ^ 2 := by
      rw [hfilt, Finset.prod_map, ← Finset.prod_pow]
      simp only [hembx]
    rw [hX, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, det_updateRow_last_single_eq_mul_det_submatrix, hminor,
      Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose, hdB, hdB', hprod]
    ring

end GlobalTheory.ClassFin
