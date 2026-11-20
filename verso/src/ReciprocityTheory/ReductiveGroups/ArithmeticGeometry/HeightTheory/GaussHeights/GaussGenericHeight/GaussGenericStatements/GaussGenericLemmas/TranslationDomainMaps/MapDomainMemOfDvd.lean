import Mathlib

namespace BlockPoly

open MvPolynomial

section Diag

variable {K σ : Type*} [Field K]

noncomputable def diag (c : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun t => C (c t) * X t

/- English proof (translation)
Unfold `diag`. Rewrite using `[aeval_X]`.
-/
theorem diag_X (c : σ → K) (t : σ) : diag c (X t) = C (c t) * X t := by
  unfold diag
  rw [aeval_X]

/- English proof (translation)
Unfold `diag`. Rewrite using `[aeval_monomial, algebraMap_eq, monomial_eq, C_mul, mul_assoc]`. Use `congr 1`. Simplify using `only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow]`.
-/
theorem diag_monomial (c : σ → K) (m : σ →₀ ℕ) (a : K) :
    diag c (monomial m a) = monomial m (a * m.prod fun t e => c t ^ e) := by
  unfold diag
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul, mul_assoc]
  congr 1
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on' with`. Consider the case `monomial m a`. Rewrite using `[diag_monomial, coeff_monomial, coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem coeff_diag (c : σ → K) (g : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (diag c g) = (s.prod fun t e => c t ^ e) * coeff s g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [diag_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish `hne : (s : σ →₀ ℕ) → (s.prod fun t e => c t ^ e) ≠ 0` using `fun s => Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ (hc t)`. Use extensionality with `s`. Simplify using `only [mem_support_iff, coeff_diag]`. Conclude with `⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (hne s) h⟩`.
-/
theorem support_diag {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).support = g.support := by
  have hne : (s : σ →₀ ℕ) → (s.prod fun t e => c t ^ e) ≠ 0 := fun s =>
    Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ (hc t)
  ext s
  simp only [mem_support_iff, coeff_diag]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (hne s) h⟩

/- English proof (translation)
Simplify using `only [totalDegree, support_diag hc]`.
-/
theorem totalDegree_diag {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).totalDegree = g.totalDegree := by
  simp only [totalDegree, support_diag hc]

noncomputable def diagEquiv {c : σ → K} (hc : ∀ t, c t ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (diag c) (diag fun t => (c t)⁻¹)
    (algHom_ext fun t => by
      simp only [AlgHom.comp_apply, diag_X, map_mul, algHom_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (hc t), C_1, one_mul])
    (algHom_ext fun t => by
      simp only [AlgHom.comp_apply, diag_X, map_mul, algHom_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc t), C_1, one_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem diagEquiv_apply {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    diagEquiv hc g = diag c g := rfl

/- English proof (translation)
Take `⟨q, rfl⟩` from `hd`. Establish `hg : g ≠ 0` using `left_ne_zero_of_mul hh`. Establish `hq : q ≠ 0` using `right_ne_zero_of_mul hh`. Rewrite `hdeg` using `[totalDegree_mul_of_isDomain hg hq]`. Establish `hq0 : q.totalDegree = 0` using `by omega`.

Use `⟨q.coeff 0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `totalDegree_eq_zero_iff_eq_C.mp hq0`.
-/
theorem eq_mul_C_of_dvd {g h : MvPolynomial σ K} (hd : g ∣ h)
    (hdeg : h.totalDegree = g.totalDegree) (hh : h ≠ 0) : ∃ a : K, h = C a * g := by
  obtain ⟨q, rfl⟩ := hd
  have hg : g ≠ 0 := left_ne_zero_of_mul hh
  have hq : q ≠ 0 := right_ne_zero_of_mul hh
  rw [totalDegree_mul_of_isDomain hg hq] at hdeg
  have hq0 : q.totalDegree = 0 := by omega
  refine ⟨q.coeff 0, ?_⟩
  rw [mul_comm]
  congr 1
  exact totalDegree_eq_zero_iff_eq_C.mp hq0

end Diag

section Blocks

variable {K : Type*} [Field K] {D N : ℕ}

def bdeg (b : Fin (D + 1)) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) : ℕ := ∑ j, s (b, j)

def cb (b : Fin (D + 1)) (μ : K) : Fin (D + 1) × Fin (N + 1) → K :=
  fun t => if t.1 = b then μ else 1

/- English proof (translation)
Unfold `cb`. Use `split_ifs`. Conclude with `hμ`. Conclude with `one_ne_zero`.
-/
theorem cb_ne_zero {μ : K} (hμ : μ ≠ 0) (b : Fin (D + 1)) (t : Fin (D + 1) × Fin (N + 1)) :
    cb b μ t ≠ 0 := by
  unfold cb
  split_ifs
  · exact hμ
  · exact one_ne_zero

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fintype.prod_eq_single b]`. Simplify using `[cb, bdeg, Finset.prod_pow_eq_pow_sum]`. Introduce `i hi`. Simplify using `[cb, hi]`.
-/
theorem prod_cb (b : Fin (D + 1)) (μ : K) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    (s.prod fun t e => cb b μ t ^ e) = μ ^ bdeg b s := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fintype.prod_eq_single b]
  · simp [cb, bdeg, Finset.prod_pow_eq_pow_sum]
  · intro i hi
    simp [cb, hi]

/- English proof (translation)
Establish `hg : g ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `h2 : ∀ t : Fin (D + 1) × Fin (N + 1), cb b (2 : K) t ≠ 0` using `cb_ne_zero two_ne_zero b`. Establish `hne : diag (cb b (2 : K)) g ≠ 0`.

Introduce `h`. Apply `hg` to reduce the goal to its premises. Rewrite using `[← support_eq_empty, ← support_diag h2 g, h, support_zero]`. Take `⟨a, ha⟩` from `eq_mul_C_of_dvd hd (totalDegree_diag h2 g) hne`. Establish `key : ∀ r ∈ g.support, (2 : K) ^ bdeg b r = a`.

Introduce `r hr`. Establish `h3` using `congrArg (coeff r) ha`. Rewrite `h3` using `[coeff_diag, prod_cb, coeff_C_mul]`. Conclude with `mul_right_cancel₀ (mem_support_iff.mp hr) h3`. Establish `e` using `(key s hs).trans (key s' hs').symm`.

Establish `e' : ((2 ^ bdeg b s : ℕ) : K) = ((2 ^ bdeg b s' : ℕ) : K)`. Use `push_cast`. Conclude with `e`. Conclude with `Nat.pow_right_injective (le_refl 2) (Nat.cast_injective e')`.
-/
theorem bdeg_eq_of_dvd [CharZero K] (b : Fin (D + 1))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ diag (cb b (2 : K)) g) {s s' : Fin (D + 1) × Fin (N + 1) →₀ ℕ}
    (hs : s ∈ g.support) (hs' : s' ∈ g.support) : bdeg b s = bdeg b s' := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hs
  have h2 : ∀ t : Fin (D + 1) × Fin (N + 1), cb b (2 : K) t ≠ 0 := cb_ne_zero two_ne_zero b
  have hne : diag (cb b (2 : K)) g ≠ 0 := by
    intro h
    apply hg
    rw [← support_eq_empty, ← support_diag h2 g, h, support_zero]
  obtain ⟨a, ha⟩ := eq_mul_C_of_dvd hd (totalDegree_diag h2 g) hne
  have key : ∀ r ∈ g.support, (2 : K) ^ bdeg b r = a := by
    intro r hr
    have h3 := congrArg (coeff r) ha
    rw [coeff_diag, prod_cb, coeff_C_mul] at h3
    exact mul_right_cancel₀ (mem_support_iff.mp hr) h3
  have e := (key s hs).trans (key s' hs').symm
  have e' : ((2 ^ bdeg b s : ℕ) : K) = ((2 ^ bdeg b s' : ℕ) : K) := by
    push_cast
    exact e
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective e')

def eT (e : Equiv.Perm (Fin (D + 1))) : Fin (D + 1) × Fin (N + 1) ≃ Fin (D + 1) × Fin (N + 1) :=
  Equiv.prodCongr e (Equiv.refl _)

/- English proof (translation)
Unfold `bdeg`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h : ((e b, j) : Fin (D + 1) × Fin (N + 1)) = eT e (b, j)` using `rfl`. Rewrite using `[h, Finsupp.mapDomain_apply (eT e).injective]`.
-/
theorem bdeg_mapDomain (e : Equiv.Perm (Fin (D + 1))) (b : Fin (D + 1))
    (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    bdeg (e b) (s.mapDomain (eT e)) = bdeg b s := by
  unfold bdeg
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ((e b, j) : Fin (D + 1) × Fin (N + 1)) = eT e (b, j) := rfl
  rw [h, Finsupp.mapDomain_apply (eT e).injective]

/- English proof (translation)
Establish `hinj : Function.Injective (eT (N` using `N) e) := (eT (N := N) e).injective`. Establish `hg : g ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `hr : rename (eT e) g ≠ 0` using `(map_ne_zero_iff _ (rename_injective _ hinj)).mpr hg`.

Establish `hdeg : (rename (eT e) g).totalDegree = g.totalDegree`. Use `le_antisymm (totalDegree_rename_le _ g) ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `hd`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hq` using `[mul_zero]`. Conclude with `hr hq`. Rewrite using `[hq, totalDegree_mul_of_isDomain hg hq0]`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `eq_mul_C_of_dvd hd hdeg hr`.

Establish `h1` using `congrArg (coeff (s.mapDomain (eT e))) ha`. Rewrite `h1` using `[coeff_rename_mapDomain _ hinj, coeff_C_mul]`. Rewrite `hs`, the goal using `[mem_support_iff]`. Introduce `h0`. Rewrite `h1` using `[h0, mul_zero]`.

Conclude with `hs h1`.
-/
theorem mapDomain_mem_of_dvd (e : Equiv.Perm (Fin (D + 1)))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ rename (eT e) g) {s : Fin (D + 1) × Fin (N + 1) →₀ ℕ} (hs : s ∈ g.support) :
    s.mapDomain (eT e) ∈ g.support := by
  have hinj : Function.Injective (eT (N := N) e) := (eT (N := N) e).injective
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hs
  have hr : rename (eT e) g ≠ 0 :=
    (map_ne_zero_iff _ (rename_injective _ hinj)).mpr hg
  have hdeg : (rename (eT e) g).totalDegree = g.totalDegree := by
    refine le_antisymm (totalDegree_rename_le _ g) ?_
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hr hq
    rw [hq, totalDegree_mul_of_isDomain hg hq0]
    omega
  obtain ⟨a, ha⟩ := eq_mul_C_of_dvd hd hdeg hr
  have h1 := congrArg (coeff (s.mapDomain (eT e))) ha
  rw [coeff_rename_mapDomain _ hinj, coeff_C_mul] at h1
  rw [mem_support_iff] at hs ⊢
  intro h0
  rw [h0, mul_zero] at h1
  exact hs h1

noncomputable def transl (a : Fin (N + 1) → K) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  aeval fun t => if t.1 = 0 then X t + C (a t.2) else X t

/- English proof (translation)
Unfold `transl`. Rewrite using `[aeval_X]`.
-/
theorem transl_X (a : Fin (N + 1) → K) (t : Fin (D + 1) × Fin (N + 1)) :
    transl a (X t) = if t.1 = 0 then X t + C (a t.2) else X t := by
  unfold transl
  rw [aeval_X]

noncomputable def translEquiv (a : Fin (N + 1) → K) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K ≃ₐ[K] MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  AlgEquiv.ofAlgHom (transl a) (transl (-a))
    (algHom_ext fun t => by by_cases h : t.1 = 0 <;> simp [transl_X, h])
    (algHom_ext fun t => by by_cases h : t.1 = 0 <;> simp [transl_X, h])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem translEquiv_apply (a : Fin (N + 1) → K)
    (g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) : translEquiv a g = transl a g := rfl

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c =>`. Simplify using `only [algHom_C, eval_C, AlgHom.commutes, algebraMap_eq]`. Use `next p q hp hq =>`. Simplify using `only [map_add, hp, hq]`.

Use `next p t hp =>`. Take `⟨i, j⟩` from `t`. Simplify using `only [map_mul, hp, transl_X]`. Use `congr 1`. Distinguish the cases in `h : i = 0`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem eval_transl (z : Fin (D + 1) × Fin (N + 1) → K)
    (f : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval (fun t => if t.1 = 0 then 0 else z t) (transl (fun j => z (0, j)) f) = eval z f := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp only [algHom_C, eval_C, AlgHom.commutes, algebraMap_eq]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p t hp =>
    obtain ⟨i, j⟩ := t
    simp only [map_mul, hp, transl_X]
    congr 1
    by_cases h : i = 0
    · subst h
      simp
    · simp [h]

/- English proof (translation)
Establish `hz : ∀ z : Fin (D + 1) × Fin (N + 1) → K, eval (fun t => if t.1 = 0 then 0 else z t) g = 0`. Introduce `z`. Rewrite using `[eval_eq']`. Use `Finset.sum_eq_zero fun s hs => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, s (0, j) ≠ 0 := by`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h1` using `h0 s hs`. Simplify using `[bdeg, hne] at h1`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ (0, j)) (by simp [hj])`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`. Take `⟨q, hq⟩` from `hd (fun j => z (0, j))`. Rewrite using `[map_zero, ← eval_transl z g, hq, map_mul, hz, zero_mul]`.
-/
theorem eq_zero_of_transl [Infinite K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : ∀ a, g ∣ transl a g) (h0 : ∀ s ∈ g.support, 0 < bdeg 0 s) : g = 0 := by
  have hz : ∀ z : Fin (D + 1) × Fin (N + 1) → K,
      eval (fun t => if t.1 = 0 then 0 else z t) g = 0 := by
    intro z
    rw [eval_eq']
    refine Finset.sum_eq_zero fun s hs => ?_
    obtain ⟨j, hj⟩ : ∃ j, s (0, j) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := h0 s hs
      simp [bdeg, hne] at h1
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_univ (0, j)) (by simp [hj])
  apply MvPolynomial.funext
  intro z
  obtain ⟨q, hq⟩ := hd (fun j => z (0, j))
  rw [map_zero, ← eval_transl z g, hq, map_mul, hz, zero_mul]

/- English proof (translation)
Establish `hc1 : ∀ b, ∀ r ∈ g.support, bdeg b r = bdeg b s` using `fun b r hr => bdeg_eq_of_dvd b (hsc b) hr hs`. Use `split_ifs with hb`. Substitute `hb show bdeg 0 s = 0` using the available equality. Assume the negation of the conclusion as `hne`. Use `haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective`.

Establish `hg : g = 0` using `eq_zero_of_transl htr fun r hr => by`. Rewrite using `[hc1 0 r hr]`. Conclude with `Nat.pos_of_ne_zero hne`. Rewrite `hs` using `[hg]`. Simplify using `at hs`.

Establish `hD : (1 : Fin (D + 1)) ≠ 0`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Break down `D with _ | D` into its components or cases. Conclude with `Fin.ext (Nat.lt_one_iff.mp b.isLt)`.

Simplify using `[Fin.ext_iff] at h`. Establish `hb1 : bdeg b s = bdeg 1 s`. Distinguish the cases in `h1 : b = 1`. Rewrite using `[h1]`. Establish `he0 : Equiv.swap (1 : Fin (D + 1)) b 0 = 0` using `Equiv.swap_apply_of_ne_of_ne hD.symm (Ne.symm hb)`.

Establish `hmem` using `mapDomain_mem_of_dvd (Equiv.swap 1 b) (hsw _ he0) hs`. Establish `h2` using `bdeg_mapDomain (Equiv.swap (1 : Fin (D + 1)) b) 1 s`. Rewrite `h2` using `[Equiv.swap_apply_left]`. Rewrite using `[← hc1 b _ hmem]`. Conclude with `h2`.

Use `show bdeg b s = g.support.sup fun r => bdeg 1 r`. Rewrite using `[hb1]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Finset.le_sup (f := fun r => bdeg 1 r) hs`. Conclude with `Finset.sup_le fun r hr => (hc1 1 r hr).le`.
-/
theorem multiHom_of_dvd [CharZero K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hsc : ∀ b, g ∣ diag (cb b (2 : K)) g)
    (hsw : ∀ e : Equiv.Perm (Fin (D + 1)), e 0 = 0 → g ∣ rename (eT e) g)
    (htr : ∀ a, g ∣ transl a g) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) (hs : s ∈ g.support)
    (b : Fin (D + 1)) :
    ∑ j, s (b, j) = if b = 0 then 0 else g.support.sup fun r => ∑ j, r (1, j) := by
  have hc1 : ∀ b, ∀ r ∈ g.support, bdeg b r = bdeg b s := fun b r hr =>
    bdeg_eq_of_dvd b (hsc b) hr hs
  split_ifs with hb
  · subst hb
    show bdeg 0 s = 0
    by_contra hne
    haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    have hg : g = 0 := eq_zero_of_transl htr fun r hr => by
      rw [hc1 0 r hr]
      exact Nat.pos_of_ne_zero hne
    rw [hg] at hs
    simp at hs
  · have hD : (1 : Fin (D + 1)) ≠ 0 := by
      intro h
      apply hb
      rcases D with _ | D
      · exact Fin.ext (Nat.lt_one_iff.mp b.isLt)
      · simp [Fin.ext_iff] at h
    have hb1 : bdeg b s = bdeg 1 s := by
      by_cases h1 : b = 1
      · rw [h1]
      · have he0 : Equiv.swap (1 : Fin (D + 1)) b 0 = 0 :=
          Equiv.swap_apply_of_ne_of_ne hD.symm (Ne.symm hb)
        have hmem := mapDomain_mem_of_dvd (Equiv.swap 1 b) (hsw _ he0) hs
        have h2 := bdeg_mapDomain (Equiv.swap (1 : Fin (D + 1)) b) 1 s
        rw [Equiv.swap_apply_left] at h2
        rw [← hc1 b _ hmem]
        exact h2
    show bdeg b s = g.support.sup fun r => bdeg 1 r
    rw [hb1]
    apply le_antisymm
    · exact Finset.le_sup (f := fun r => bdeg 1 r) hs
    · exact Finset.sup_le fun r hr => (hc1 1 r hr).le

end Blocks

end BlockPoly
