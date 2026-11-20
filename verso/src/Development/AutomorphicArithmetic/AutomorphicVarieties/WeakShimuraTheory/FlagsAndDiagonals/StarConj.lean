import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Lab

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Set `L : Matrix n n K →ₗ[K] K` to `{ toFun := fun X => (a * X * m) i j map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul] map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }`. Establish `hle : Submodule.span K (Set.range f) ≤ LinearMap.ker L` using `Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g)`. Rewrite `hle` using `[hf]`.

Establish `h0` using `hle (Submodule.mem_top (x := m * Matrix.single i j (1 : K) * a))`. Rewrite `h0` using `[LinearMap.mem_ker]`. Establish `e : L (m * Matrix.single i j (1 : K) * a) = Matrix.single i j (1 : K) i j`. Express the relevant statement in the definitionally equal form `(a * (m * Matrix.single i j (1 : K) * a) * m) i j = _`. Establish `: a * (m * Matrix.single i j (1 : K) * a) * m = (a * m) * Matrix.single i j (1 : K) * (a * m)`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, h, Matrix.one_mul, Matrix.mul_one]`. Rewrite `h0` using `[e]`. Simplify using `at h0`.
-/
private theorem span_entry {K n Γ : Type} [Field K] [Fintype n] [DecidableEq n] (f : Γ → Matrix n n K) (a m : Matrix n n K)
    (h : a * m = 1) (hf : Submodule.span K (Set.range f) = ⊤) (i j : n) : ∃ g, (a * f g * m) i j ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  let L : Matrix n n K →ₗ[K] K :=
    { toFun := fun X => (a * X * m) i j
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hle : Submodule.span K (Set.range f) ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g)
  rw [hf] at hle
  have h0 := hle (Submodule.mem_top (x := m * Matrix.single i j (1 : K) * a))
  rw [LinearMap.mem_ker] at h0
  have e : L (m * Matrix.single i j (1 : K) * a) = Matrix.single i j (1 : K) i j := by
    change (a * (m * Matrix.single i j (1 : K) * a) * m) i j = _
    have : a * (m * Matrix.single i j (1 : K) * a) * m = (a * m) * Matrix.single i j (1 : K) * (a * m) := by
      simp only [Matrix.mul_assoc]
    rw [this, h, Matrix.one_mul, Matrix.mul_one]
  rw [e] at h0
  simp at h0

/- English proof (translation)
Establish `h01` using `hY 0 1 (by decide)`. Establish `h03` using `hY 0 3 (by decide)`. Establish `h21` using `hY 2 1 (by decide)`. Establish `h23` using `hY 2 3 (by decide)`. Use extensionality with `i j`.

Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[ixB, h01, h03, h21, h23]`.
-/
private theorem sub_mul_par {K : Type} [CommRing K] (X : M4 K) {Y : M4 K} (hY : Par Y) :
    (X * Y).submatrix ixB ixB = X.submatrix ixB ixB * Y.submatrix ixB ixB := by
  have h01 := hY 0 1 (by decide)
  have h03 := hY 0 3 (by decide)
  have h21 := hY 2 1 (by decide)
  have h23 := hY 2 3 (by decide)
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [ixB, h01, h03, h21, h23]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : lamW i = lamW k`. Rewrite using `[hY k j (by omega), mul_zero]`.

Rewrite using `[hX i k hk, zero_mul]`.
-/
private theorem block_mul {K : Type} [CommRing K] {X Y : M4 K} (hX : IsBlock X) (hY : IsBlock Y) : IsBlock (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : lamW i = lamW k
  · rw [hY k j (by omega), mul_zero]
  · rw [hX i k hk, zero_mul]

private def pA (K : Type) [CommRing K] : M4 K := Matrix.diagonal fun i => (lamW i : K)

/- English proof (translation)
Use `revert i`. Evaluate the decidable proposition.
-/
private theorem lam_cases (i : Fin 4) : lamW i = 0 ∨ lamW i = 1 := by revert i; decide

/- English proof (translation)
Simplify using `[pA, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem add_pA_mul_sub_mul_pA_apply {K : Type} [CommRing K] (X : M4 K) (i j : Fin 4) :
    (X + pA K * X - X * pA K) i j = X i j * (1 + (lamW i : K) - (lamW j : K)) := by
  simp [pA, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/- English proof (translation)
Introduce `i j h` and use `hX i j h.ne'`.
-/
private theorem par_of_isBlock {K : Type} [CommRing K] {X : M4 K} (hX : IsBlock X) : Par X :=
  fun i j h => hX i j h.ne'

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[add_pA_mul_sub_mul_pA_apply]`. Apply the tactic sequence `rcases lam_cases i with hi | hi <;> rcases lam_cases j with hj | hj`. Conclude with `absurd (hi.trans hj.symm) hij`. Simplify using `[hi, hj]`.

Rewrite using `[hX i j (by rw [hi, hj]; norm_num)]`. Simplify using the standard rewrite rules. Conclude with `absurd (hi.trans hj.symm) hij`.
-/
private theorem block_part {K : Type} [CommRing K] {X : M4 K} (hX : Par X) : IsBlock (X + pA K * X - X * pA K) := by
  intro i j hij
  rw [add_pA_mul_sub_mul_pA_apply]
  rcases lam_cases i with hi | hi <;> rcases lam_cases j with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · simp [hi, hj]
  · rw [hX i j (by rw [hi, hj]; norm_num)]
    simp
  · exact absurd (hi.trans hj.symm) hij

/- English proof (translation)
Set `Ba : M4 K` to `a + pA K * a - a * pA K`. Set `Bm : M4 K` to `m + pA K * m - m * pA K`. Establish `hBa : IsBlock Ba` using `block_part ha`. Establish `hBm : IsBlock Bm` using `block_part hm`. Establish `hsum : m * Ba + Bm * a = 1 + 1`.

Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Ba, Bm, add_pA_mul_sub_mul_pA_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Establish `hma : ∑ k, m i k * a k j = (1 : M4 K) i j`. Rewrite using `[← Matrix.mul_apply, h']`.

Establish `: ∑ k, (m i k * (a k j * (1 + (lamW k : K) - (lamW j : K))) + m i k * (1 + (lamW i : K) - (lamW k : K)) * a k j) = (2 + (lamW i : K) - (lamW j : K)) * ∑ k, m i k * a k j`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hma]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.one_apply_ne hij]`.

Set `Y : M4 K` to `m * Ba - 1`. Establish `h1Y : 1 + Y = m * Ba` using `by simp [Y]`. Establish `h2Y : 1 - Y = Bm * a`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Y, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j hij`. Simplify using `only [Y, Matrix.sub_apply]`. Break down `lt_or_eq_of_le (not_lt.mp hij) with hlt | heq` into its components or cases. Rewrite using `[Par.mul hm (par_of_isBlock hBa) i j hlt, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ hlt)]`. Simplify using the standard rewrite rules.

Establish `: (m * Ba) i j = (m * a) i j`. Simplify using `only [Matrix.mul_apply, Ba, add_pA_mul_sub_mul_pA_apply]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Break down `lt_trichotomy (lamW k) (lamW j) with hk | hk | hk` into its components or cases. Rewrite using `[hm i k (by rw [← heq]; exact hk)]`.

Simplify using the standard rewrite rules. Rewrite using `[hk]`. Simplify using the standard rewrite rules. Rewrite using `[ha k j hk]`. Simplify using the standard rewrite rules.

Rewrite using `[this, h']`. Simplify using the standard rewrite rules. Introduce `X hX`. Rewrite using `[h2Y, h1Y]`. Establish `e : Bm * a * X * (m * Ba) = Bm * (a * X * m) * Ba`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e]`. Conclude with `block_mul (block_mul hBm hX) hBa`.
-/
private theorem split_of_block {K : Type} [CommRing K] {a m : M4 K} (h : a * m = 1) (h' : m * a = 1) (ha : Par a) (hm : Par m) :
    ∃ Y : M4 K, (∀ i j, ¬ lamW i < lamW j → Y i j = 0) ∧ ∀ X, IsBlock (a * X * m) → IsBlock ((1 - Y) * X * (1 + Y)) := by
  let Ba : M4 K := a + pA K * a - a * pA K
  let Bm : M4 K := m + pA K * m - m * pA K
  have hBa : IsBlock Ba := block_part ha
  have hBm : IsBlock Bm := block_part hm
  have hsum : m * Ba + Bm * a = 1 + 1 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Ba, Bm, add_pA_mul_sub_mul_pA_apply]
    rw [← Finset.sum_add_distrib]
    have hma : ∑ k, m i k * a k j = (1 : M4 K) i j := by
      rw [← Matrix.mul_apply, h']
    have : ∑ k, (m i k * (a k j * (1 + (lamW k : K) - (lamW j : K))) +
        m i k * (1 + (lamW i : K) - (lamW k : K)) * a k j) =
        (2 + (lamW i : K) - (lamW j : K)) * ∑ k, m i k * a k j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [this, hma]
    by_cases hij : i = j
    · subst hij
      simp
      ring
    · simp [Matrix.one_apply_ne hij]
  let Y : M4 K := m * Ba - 1
  have h1Y : 1 + Y = m * Ba := by simp [Y]
  have h2Y : 1 - Y = Bm * a := by
    calc 1 - Y = (1 + 1) - m * Ba := by simp only [Y]; abel
      _ = (m * Ba + Bm * a) - m * Ba := by rw [hsum]
      _ = Bm * a := by abel
  refine ⟨Y, ?_, ?_⟩
  · intro i j hij
    simp only [Y, Matrix.sub_apply]
    rcases lt_or_eq_of_le (not_lt.mp hij) with hlt | heq
    · rw [Par.mul hm (par_of_isBlock hBa) i j hlt, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ hlt)]
      simp
    · have : (m * Ba) i j = (m * a) i j := by
        simp only [Matrix.mul_apply, Ba, add_pA_mul_sub_mul_pA_apply]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rcases lt_trichotomy (lamW k) (lamW j) with hk | hk | hk
        · rw [hm i k (by rw [← heq]; exact hk)]
          simp
        · rw [hk]
          simp
        · rw [ha k j hk]
          simp
      rw [this, h']
      simp
  · intro X hX
    rw [h2Y, h1Y]
    have e : Bm * a * X * (m * Ba) = Bm * (a * X * m) * Ba := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact block_mul (block_mul hBm hX) hBa

end UpperTheory.V.Ws.Lab

open UpperTheory.V.Ws.Lab in
/- English proof (translation)
Introduce `K _ Γ _ r r' m hm hr' hpar hstar`. Establish `hma : adj m * m = 1` using `sp_adj_mul hm`. Establish `hmm : m * adj m = 1` using `sp_mul_adj hm`. Break down `hstar with hirr | hbe` into its components or cases. Apply the tactic sequence `obtain ⟨g1, hg1⟩ := span_entry (⇑r) (adj m) m hma hirr 0 2`.

Apply the tactic sequence `obtain ⟨g2, hg2⟩ := span_entry (⇑r) (adj m) m hma hirr 2 0`. Apply the tactic sequence `obtain ⟨g3, hg3⟩ := span_entry (⇑r) (adj m) m hma hirr 1 2`. Use `⟨⟨g1, 0, 2, by decide, by rw [hr']; exact hg1⟩, ⟨g2, 2, 0, by decide, by rw [hr']; exact hg2⟩, Or.inl ⟨g3, 1, 2, by decide, by rw [hr']; exact hg3⟩⟩` and prove the remaining obligations. Take `⟨hpr, hspan, hno⟩` from `hbe`. Establish `hmPar : Par m` using `hpar hpr`.

Establish `hadjPar : Par (adj m)` using `Par.adj hmPar`. Establish `hsub : ∀ g, (r' g).submatrix ixB ixB = (adj m).submatrix ixB ixB * (r g).submatrix ixB ixB * m.submatrix ixB ixB`. Introduce `g`. Rewrite using `[hr', sub_mul_par _ hmPar, sub_mul_par _ (hpr g)]`. Establish `hi0 : (![1, 3] : Fin 2 → Fin 4) 0 = 1` using `rfl`.

Establish `hi1 : (![1, 3] : Fin 2 → Fin 4) 1 = 3` using `rfl`. Establish `hinv2 : (adj m).submatrix ixB ixB * m.submatrix ixB ixB = 1`. Rewrite using `[← sub_mul_par _ hmPar, hma]`. Use extensionality with `p q`. Apply the tactic sequence `fin_cases p <;> fin_cases q <;> simp [ixB, hi0, hi1, Matrix.one_apply]`.

Apply the tactic sequence `obtain ⟨g1, hg1⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 0 1`. Apply the tactic sequence `obtain ⟨g2, hg2⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 1 0`. Rewrite `hg1`, `hg2` using `[← hsub]`. Use `⟨⟨g1, 1, 3, by decide, by simpa [ixB, hi0, hi1] using hg1⟩, ⟨g2, 3, 1, by decide, by simpa [ixB, hi0, hi1] using hg2⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`.

Establish `key : ∀ i j : Fin 4, lamW i < lamW j → (wt i j = wBe ∨ wt i j = -wAl ∨ wt i j = -wTh)`. Evaluate the decidable proposition. Establish `hblock : ∀ g, IsBlock (adj m * r g * m)`. Introduce `g i j hij`. Break down `lt_or_gt_of_ne hij with hlt | hgt` into its components or cases.

Assume the negation of the conclusion as `hne`. Establish `hne' : r' g i j ≠ 0` using `by rw [hr']; exact hne`. Break down `key i j hlt with hw | hw | hw` into its components or cases. Conclude with `hnot (Or.inl ⟨g, i, j, hw, hne'⟩)`. Conclude with `hnot (Or.inr (Or.inl ⟨g, i, j, hw, hne'⟩))`.

Conclude with `hnot (Or.inr (Or.inr ⟨g, i, j, hw, hne'⟩))`. Conclude with `Par.mul (Par.mul hadjPar (hpr g)) hmPar i j hgt`. Take `⟨Y, hYs, hYb⟩` from `split_of_block hma hmm hadjPar hmPar`. Conclude with `hno ⟨Y, hYs, fun g => hYb (r g) (hblock g)⟩`.
-/
theorem UpperTheory.V.Ws.Lab.starConj :
    ∀ (K : Type) [Field K] (Γ : Type) [Group Γ] (r r' : Γ →* M4 K) (m : M4 K), IsGSp 1 m → (∀ g, r' g = adj m * r g * m) →
      ((∀ g, Par (r g)) → Par m) → Star r → StarE r' := by
  intro K _ Γ _ r r' m hm hr' hpar hstar
  have hma : adj m * m = 1 := sp_adj_mul hm
  have hmm : m * adj m = 1 := sp_mul_adj hm
  rcases hstar with hirr | hbe
  · obtain ⟨g1, hg1⟩ := span_entry (⇑r) (adj m) m hma hirr 0 2
    obtain ⟨g2, hg2⟩ := span_entry (⇑r) (adj m) m hma hirr 2 0
    obtain ⟨g3, hg3⟩ := span_entry (⇑r) (adj m) m hma hirr 1 2
    refine ⟨⟨g1, 0, 2, by decide, by rw [hr']; exact hg1⟩,
      ⟨g2, 2, 0, by decide, by rw [hr']; exact hg2⟩,
      Or.inl ⟨g3, 1, 2, by decide, by rw [hr']; exact hg3⟩⟩
  · obtain ⟨hpr, hspan, hno⟩ := hbe
    have hmPar : Par m := hpar hpr
    have hadjPar : Par (adj m) := Par.adj hmPar
    have hsub : ∀ g, (r' g).submatrix ixB ixB =
        (adj m).submatrix ixB ixB * (r g).submatrix ixB ixB * m.submatrix ixB ixB := by
      intro g
      rw [hr', sub_mul_par _ hmPar, sub_mul_par _ (hpr g)]
    have hi0 : (![1, 3] : Fin 2 → Fin 4) 0 = 1 := rfl
    have hi1 : (![1, 3] : Fin 2 → Fin 4) 1 = 3 := rfl
    have hinv2 : (adj m).submatrix ixB ixB * m.submatrix ixB ixB = 1 := by
      rw [← sub_mul_par _ hmPar, hma]
      ext p q
      fin_cases p <;> fin_cases q <;> simp [ixB, hi0, hi1, Matrix.one_apply]
    obtain ⟨g1, hg1⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 0 1
    obtain ⟨g2, hg2⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 1 0
    rw [← hsub] at hg1 hg2
    refine ⟨⟨g1, 1, 3, by decide, by simpa [ixB, hi0, hi1] using hg1⟩,
      ⟨g2, 3, 1, by decide, by simpa [ixB, hi0, hi1] using hg2⟩, ?_⟩
    by_contra hnot
    have key : ∀ i j : Fin 4, lamW i < lamW j → (wt i j = wBe ∨ wt i j = -wAl ∨ wt i j = -wTh) := by
      decide
    have hblock : ∀ g, IsBlock (adj m * r g * m) := by
      intro g i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · by_contra hne
        have hne' : r' g i j ≠ 0 := by rw [hr']; exact hne
        rcases key i j hlt with hw | hw | hw
        · exact hnot (Or.inl ⟨g, i, j, hw, hne'⟩)
        · exact hnot (Or.inr (Or.inl ⟨g, i, j, hw, hne'⟩))
        · exact hnot (Or.inr (Or.inr ⟨g, i, j, hw, hne'⟩))
      · exact Par.mul (Par.mul hadjPar (hpr g)) hmPar i j hgt
    obtain ⟨Y, hYs, hYb⟩ := split_of_block hma hmm hadjPar hmPar
    exact hno ⟨Y, hYs, fun g => hYb (r g) (hblock g)⟩
