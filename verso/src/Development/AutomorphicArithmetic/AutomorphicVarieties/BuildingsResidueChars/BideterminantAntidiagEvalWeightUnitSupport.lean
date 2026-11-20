import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ n K sz hsz I`. Establish `hrev : ∀ {s : ℕ} (hs : s ≤ n) (a : Fin n) (r : Fin s), a = Fin.rev (Fin.castLE hs r) ↔ (a : ℕ) + r + 1 = n`. Introduce `s hs a r`. Rewrite using `[Fin.ext_iff, Fin.val_rev, Fin.coe_castLE]`. Use `a.isLt` as an intermediate fact.

Use `r.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ φ : MvPolynomial (Fin n × Fin n) R →+* R, φ (bideterminant R sz hsz I) = ∏ k, (Matrix.of fun p q : Fin (sz k) => φ (X (I k p, Fin.castLE (hsz k) q))).det`. Introduce `φ`. Simplify using `only [bideterminant, initMinor, map_prod, RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hE : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I) = ∏ k, (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det`. Rewrite using `[key]`. Use `congr 1`. Use extensionality with `k`.

Use `congr 1`. Use extensionality with `p q`. Simplify using `[hrev]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `hR : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (rowAct R x.transpose (bideterminant R sz hsz I)) = ∏ k, (Matrix.of fun p q : Fin (sz k) => x (Fin.rev (Fin.castLE (hsz k) q)) (I k p)).det`. Use `(key ((eval fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0).comp (rowAct R x.transpose).toRingHom)).trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `k`. Use `congr 1`.

Use extensionality with `p q`. Simplify using `[rowAct, Matrix.transpose_apply, mul_ite, Finset.sum_ite_eq']`. Establish `hk : ∀ (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n), (Matrix.of fun p q : Fin s => x (Fin.rev (Fin.castLE hs q)) (J p)).det = (Matrix.of fun p q : Fin s => if (J p : ℕ) + q + 1 = n then (1 : R) else 0).det * ∏ q : Fin s, x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs q))`. Introduce `s hs J`. Establish `hU : (Matrix.of fun r q : Fin s => x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs r))).IsUpperTriangular`.

Introduce `r q hqr`. Simplify using `only [id, Matrix.of_apply] at hqr ⊢`. Apply `hx` to reduce the goal to its premises. Rewrite `hqr`, the goal using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.val_rev, Fin.coe_castLE]`.

Use `r.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hdU` using `Matrix.det_of_upperTriangular hU`. Simplify using `only [Matrix.of_apply] at hdU`. Rewrite using `[← hdU, ← Matrix.det_mul]`.

Use `congr 1`. Use extensionality with `p q`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]`. Establish `hJ` using `(J p).isLt`. Establish `hq` using `q.isLt`.

Distinguish the cases in `h : (J p : ℕ) + s < n`. Rewrite using `[Finset.sum_eq_zero]`. Apply `hx` to reduce the goal to its premises. Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.val_rev, Fin.coe_castLE]`.

Use linear arithmetic over natural numbers and integers. Introduce `r _`. Rewrite using `[if_neg]`. Use `r.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.sum_eq_single (⟨n - 1 - (J p : ℕ), by omega⟩ : Fin s)]`. Rewrite using `[if_pos (by simp only; omega)]`. Use `congr 1`. Use `ext`. Simplify using `only [Fin.val_rev, Fin.coe_castLE]`.

Use linear arithmetic over natural numbers and integers. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h'`. Apply `hb` to reduce the goal to its premises.

Use `ext`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.

Establish `hreg : ∀ k, ∏ q : Fin (sz k), x (Fin.rev (Fin.castLE (hsz k) q)) (Fin.rev (Fin.castLE (hsz k) q)) = ∏ i : Fin n, if ((Fin.rev i : Fin n) : ℕ) < sz k then x i i else 1`. Introduce `k`. Rewrite using `[← Finset.prod_filter]`. Use `Finset.prod_bij (fun q _ => Fin.rev (Fin.castLE (hsz k) q)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `q _`.

Simplify using the standard rewrite rules. Use `q.isLt` as an intermediate fact. Use `hsz k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `a _ b _ h`.

Simplify using `using h`. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Use `⟨⟨(Fin.rev b : ℕ), hb⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `only [Fin.val_rev, Fin.coe_castLE]`. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `q _`. Both sides reduce to the same expression.

Rewrite using `[hR, hE, Finset.prod_congr rfl (fun k _ => hk (sz k) (hsz k) (I k)), Finset.prod_mul_distrib, mul_comm]`. Use `congr 1`. Rewrite using `[Finset.prod_congr rfl (fun k _ => hreg k), Finset.prod_comm]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`.

Both sides reduce to the same expression. Introduce `hI`. Rewrite using `[hE]`. Use `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_` and prove the remaining obligations. Introduce `k _`.

Establish `hP : (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0) = (Fin.revPerm).permMatrix R`. Use extensionality with `p q`. Establish `h1` using `hI k p`. Establish `h2` using `p.isLt`. Establish `h3` using `q.isLt`.

Establish `h4` using `hsz k`. Establish `hiff : ((I k p : ℕ) + q + 1 = n) ↔ q ∈ (Fin.revPerm : Equiv.Perm (Fin (sz k))).toPEquiv p`. Simplify using `only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply, Fin.ext_iff, Fin.val_rev]`. Apply the tactic sequence `constructor <;> intro <;> omega`. Rewrite using `[Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]`.

Conclude with `if_congr hiff rfl rfl`. Rewrite using `[hP, Matrix.det_permutation]`. Conclude with `(Units.isUnit _).map (Int.castRingHom R)`. Introduce `hmono hne k p`. Rewrite `hne` using `[hE]`.

Establish `hdet : (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det ≠ 0` using `fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ k) h0)`. Establish `hlow : ∀ p : Fin (sz k), n ≤ (I k p : ℕ) + sz k`. Introduce `p`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Apply `hdet` to reduce the goal to its premises. Apply `Matrix.det_eq_zero_of_row_eq_zero p` to reduce the goal to its premises. Introduce `q`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[if_neg]`.

Use `q.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hA : ∀ d : ℕ, ∀ a b : Fin (sz k), (b : ℕ) = a + d → (I k a : ℕ) + d ≤ I k b`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero`. Introduce `a b h`. Establish `: a = b` using `Fin.ext (by omega)`. Substitute `this` using the available equality. Simplify using the standard rewrite rules.

Consider the case `succ d ih`. Introduce `a b h`. Establish `hb' : (a : ℕ) + d < sz k`. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `ih a ⟨a + d, hb'⟩ rfl`. Establish `h2 : I k ⟨a + d, hb'⟩ < I k b` using `hmono k (by rw [Fin.lt_iff_val_lt_val]; simp only; omega)`. Rewrite `h2` using `[Fin.lt_iff_val_lt_val]`. Use linear arithmetic over natural numbers and integers. Establish `hs : 0 < sz k`.

Use `p.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h0` using `hA p ⟨0, hs⟩ p (by simp)`. Establish `hl` using `hlow ⟨0, hs⟩`. Establish `h1` using `hA (sz k - 1 - p) p ⟨sz k - 1, by omega⟩ (by simp only; have := p.isLt; omega)`.

Use `(I k ⟨sz k - 1, by omega⟩).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.bideterminant_antidiag_eval_weight_unit_support :
    ∀ (R : Type) [CommRing R] (n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), (∀ x : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → x i j = 0) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (rowAct R x.transpose (bideterminant R sz hsz I)) = (∏ i, x i i ^ shapeDeg sz (Fin.rev i)) * eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)) ∧ ((∀ k p, (I k p : ℕ) + sz k = n + p) → IsUnit (eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I))) ∧ ((∀ k, StrictMono (I k)) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I) ≠ 0 → ∀ k p, (I k p : ℕ) + sz k = n + p) := by
  intro R _ n K sz hsz I
  have hrev : ∀ {s : ℕ} (hs : s ≤ n) (a : Fin n) (r : Fin s),
      a = Fin.rev (Fin.castLE hs r) ↔ (a : ℕ) + r + 1 = n := by
    intro s hs a r
    rw [Fin.ext_iff, Fin.val_rev, Fin.coe_castLE]
    have := a.isLt
    have := r.isLt
    omega
  have key : ∀ φ : MvPolynomial (Fin n × Fin n) R →+* R, φ (bideterminant R sz hsz I) =
      ∏ k, (Matrix.of fun p q : Fin (sz k) => φ (X (I k p, Fin.castLE (hsz k) q))).det := by
    intro φ
    simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
    rfl
  have hE : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)
      = ∏ k, (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det := by
    rw [key]
    congr 1
    ext k
    congr 1
    ext p q
    simp [hrev]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hR : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0)
        (rowAct R x.transpose (bideterminant R sz hsz I)) =
        ∏ k, (Matrix.of fun p q : Fin (sz k) => x (Fin.rev (Fin.castLE (hsz k) q)) (I k p)).det := by
      refine (key ((eval fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0).comp
        (rowAct R x.transpose).toRingHom)).trans ?_
      congr 1
      ext k
      congr 1
      ext p q
      simp [rowAct, Matrix.transpose_apply, mul_ite, Finset.sum_ite_eq']
    have hk : ∀ (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n),
        (Matrix.of fun p q : Fin s => x (Fin.rev (Fin.castLE hs q)) (J p)).det =
        (Matrix.of fun p q : Fin s => if (J p : ℕ) + q + 1 = n then (1 : R) else 0).det *
          ∏ q : Fin s, x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs q)) := by
      intro s hs J
      have hU : (Matrix.of fun r q : Fin s =>
          x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs r))).IsUpperTriangular := by
        intro r q hqr
        simp only [id, Matrix.of_apply] at hqr ⊢
        apply hx
        rw [Fin.lt_iff_val_lt_val] at hqr ⊢
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := r.isLt
        omega
      have hdU := Matrix.det_of_upperTriangular hU
      simp only [Matrix.of_apply] at hdU
      rw [← hdU, ← Matrix.det_mul]
      congr 1
      ext p q
      simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      have hJ := (J p).isLt
      have hq := q.isLt
      by_cases h : (J p : ℕ) + s < n
      · rw [Finset.sum_eq_zero]
        · apply hx
          rw [Fin.lt_iff_val_lt_val]
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro r _
          rw [if_neg]
          have := r.isLt
          omega
      · rw [Finset.sum_eq_single (⟨n - 1 - (J p : ℕ), by omega⟩ : Fin s)]
        · rw [if_pos (by simp only; omega)]
          congr 1
          ext
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro b _ hb
          rw [if_neg]
          intro h'
          apply hb
          ext
          simp only
          omega
        · intro h'
          exact absurd (Finset.mem_univ _) h'
    have hreg : ∀ k, ∏ q : Fin (sz k), x (Fin.rev (Fin.castLE (hsz k) q)) (Fin.rev (Fin.castLE (hsz k) q))
        = ∏ i : Fin n, if ((Fin.rev i : Fin n) : ℕ) < sz k then x i i else 1 := by
      intro k
      rw [← Finset.prod_filter]
      refine Finset.prod_bij (fun q _ => Fin.rev (Fin.castLE (hsz k) q)) ?_ ?_ ?_ ?_
      · intro q _
        simp
        have := q.isLt
        have := hsz k
        omega
      · intro a _ b _ h
        simpa using h
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨⟨(Fin.rev b : ℕ), hb⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := b.isLt
        omega
      · intro q _
        rfl
    rw [hR, hE, Finset.prod_congr rfl (fun k _ => hk (sz k) (hsz k) (I k)),
      Finset.prod_mul_distrib, mul_comm]
    congr 1
    rw [Finset.prod_congr rfl (fun k _ => hreg k), Finset.prod_comm]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  · intro hI
    rw [hE]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro k _
    have hP : (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0)
        = (Fin.revPerm).permMatrix R := by
      ext p q
      have h1 := hI k p
      have h2 := p.isLt
      have h3 := q.isLt
      have h4 := hsz k
      have hiff : ((I k p : ℕ) + q + 1 = n) ↔ q ∈ (Fin.revPerm : Equiv.Perm (Fin (sz k))).toPEquiv p := by
        simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply,
          Fin.ext_iff, Fin.val_rev]
        constructor <;> intro <;> omega
      rw [Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      exact if_congr hiff rfl rfl
    rw [hP, Matrix.det_permutation]
    exact (Units.isUnit _).map (Int.castRingHom R)
  · intro hmono hne k p
    rw [hE] at hne
    have hdet : (Matrix.of fun p q : Fin (sz k) =>
        if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det ≠ 0 :=
      fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ k) h0)
    have hlow : ∀ p : Fin (sz k), n ≤ (I k p : ℕ) + sz k := by
      intro p
      by_contra hlt
      push_neg at hlt
      apply hdet
      apply Matrix.det_eq_zero_of_row_eq_zero p
      intro q
      simp only [Matrix.of_apply]
      rw [if_neg]
      have := q.isLt
      omega
    have hA : ∀ d : ℕ, ∀ a b : Fin (sz k), (b : ℕ) = a + d → (I k a : ℕ) + d ≤ I k b := by
      intro d
      induction d with
      | zero =>
        intro a b h
        have : a = b := Fin.ext (by omega)
        subst this
        simp
      | succ d ih =>
        intro a b h
        have hb' : (a : ℕ) + d < sz k := by
          have := b.isLt
          omega
        have h1 := ih a ⟨a + d, hb'⟩ rfl
        have h2 : I k ⟨a + d, hb'⟩ < I k b := hmono k (by rw [Fin.lt_iff_val_lt_val]; simp only; omega)
        rw [Fin.lt_iff_val_lt_val] at h2
        omega
    have hs : 0 < sz k := by
      have := p.isLt
      omega
    have h0 := hA p ⟨0, hs⟩ p (by simp)
    have hl := hlow ⟨0, hs⟩
    have h1 := hA (sz k - 1 - p) p ⟨sz k - 1, by omega⟩ (by simp only; have := p.isLt; omega)
    have := (I k ⟨sz k - 1, by omega⟩).isLt
    omega
