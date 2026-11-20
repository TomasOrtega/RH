import Formalism.LocalToGlobal.ProjectiveLattices.GenSectA

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial Cardinal

open MvPolynomial in
/- English proof (translation)
Establish `hP0 : P ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hP`. Take `⟨s, hs, hsd⟩` from `Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0) (fun s : ι →₀ ℕ => s.sum fun _ e => e)`. Establish `htd : P.totalDegree = s.sum fun _ e => e` using `hsd`.

Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Rewrite `hP` using `[htd]`. Simplify using `at hP`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, s i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hs0 (Finsupp.ext h)`. Establish `hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 → (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1`. Introduce `t ht`.

Establish `hle : Finsupp.single i 1 ≤ t` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)`. Use `conv_lhs => rw [← tsub_add_cancel_of_le hle]`. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]`. Establish `hder : pderiv i P = ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (coeff t P * (t i : K))` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`. Use `⟨i, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hc` using `congrArg (coeff (s - Finsupp.single i 1)) h0`.

Rewrite `hc` using `[hder, coeff_sum, coeff_zero, Finset.sum_eq_single s]`. Rewrite `hc` using `[coeff_monomial, if_pos rfl]`. Conclude with `mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc`. Introduce `t _ hts`. Rewrite using `[coeff_monomial]`.

Use `split_ifs with heq`. Distinguish the cases in `hti : t i = 0`. Simplify using `[hti]`. It suffices to derive a contradiction. Apply `hts` to reduce the goal to its premises.

Establish `h1 : Finsupp.single i 1 ≤ t` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)`. Establish `h2 : Finsupp.single i 1 ≤ s` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)`. Rewrite using `[← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]`. Both sides reduce to the same expression. Introduce `hns`.

Conclude with `absurd hs hns`. Establish `hpos : (⊥ : ℕ) < s.sum fun _ e => e`. Rewrite using `[← htd]`. Conclude with `hP`. Rewrite using `[htd, hder]`.

Use `lt_of_le_of_lt (totalDegree_finset_sum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)` and prove the remaining obligations. Distinguish the cases in `hti : t i = 0`. Simplify `hP` using `[hti, htd]`. Use `lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_` and prove the remaining obligations. Establish `h1` using `hdeg t hti`.

Establish `h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e`. Rewrite using `[← htd]`. Conclude with `le_totalDegree ht`. Rewrite `h2` using `[h1]`. Conclude with `h2`.
-/
theorem exists_pderiv_ne_zero_lt' {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (P : MvPolynomial ι K) (hP : 0 < P.totalDegree) :
    ∃ i, pderiv i P ≠ 0 ∧ (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0)
    (fun s : ι →₀ ℕ => s.sum fun _ e => e)
  have htd : P.totalDegree = s.sum fun _ e => e := hsd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [htd] at hP
    simp at hP
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs0 (Finsupp.ext h)
  have hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 →
      (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    intro t ht
    have hle : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hder : pderiv i P =
      ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (coeff t P * (t i : K)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  refine ⟨i, ?_, ?_⟩
  · intro h0
    have hc := congrArg (coeff (s - Finsupp.single i 1)) h0
    rw [hder, coeff_sum, coeff_zero, Finset.sum_eq_single s] at hc
    · rw [coeff_monomial, if_pos rfl] at hc
      exact mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc
    · intro t _ hts
      rw [coeff_monomial]
      split_ifs with heq
      · by_cases hti : t i = 0
        · simp [hti]
        · exfalso
          apply hts
          have h1 : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)
          have h2 : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
          rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]
      · rfl
    · intro hns
      exact absurd hs hns
  · have hpos : (⊥ : ℕ) < s.sum fun _ e => e := by
      rw [← htd]
      exact hP
    rw [htd, hder]
    refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)
    by_cases hti : t i = 0
    · simpa [hti, htd] using hP
    · refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
      have h1 := hdeg t hti
      have h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e := by
        rw [← htd]
        exact le_totalDegree ht
      rw [h1] at h2
      exact h2

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

/- English proof (translation)
Set `e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0}` to `{ toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩ invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩ left_inv := fun q => by`. Take `⟨⟨a, b⟩, h⟩` from `q`. Establish `hb : b = j₀` using `(h : a ≠ 0 ∧ b = j₀).2`. Substitute `hb` using the available equality. Both sides reduce to the same expression.

Use `right_inv := fun i => rfl }`. Rewrite using `[Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]`. Simplify using the standard rewrite rules.
-/
theorem card_Z (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by
  let e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩
      invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩
      left_inv := fun q => by
        obtain ⟨⟨a, b⟩, h⟩ := q
        have hb : b = j₀ := (h : a ≠ 0 ∧ b = j₀).2
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp

/- English proof (translation)
Establish `hle : D ≤ Fintype.card (Fin (D + 1) × Fin m)`. Rewrite using `[Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Use `j₀.pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← trdeg_add_eq (R := K) (S := Ω) (A := CT Ω D j₀), htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]`.
-/
theorem trdeg_CT (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT Ω D j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by
  classical
  have hle : D ≤ Fintype.card (Fin (D + 1) × Fin m) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := j₀.pos
    nlinarith
  rw [← trdeg_add_eq (R := K) (S := Ω) (A := CT Ω D j₀), htr,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]

/- English proof (translation)
Establish `hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s)`. Introduce `y`. Rewrite using `[← AlgHom.map_adjoin]`. Conclude with `Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩`. Set `f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s)` to `{ toFun := fun y => ⟨φ y, hmem y⟩ map_one' := by ext; simp map_mul' := by intros; ext; simp map_zero' := by ext; simp map_add' := by intros; ext; simp }`.

Establish `hf : Function.Injective f` using `fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))`. Conclude with `h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)`.
-/
theorem isAlgebraic_map_adjoin {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by
  have hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s) := by
    intro y
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩
  let f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s) :=
    { toFun := fun y => ⟨φ y, hmem y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Injective f := fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))
  exact h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)

/- English proof (translation)
Establish `hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D` using `D) x j₀))) (C ω : CT Ω D j₀) := by`. Introduce `ω`. Establish `h1` using `isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT Ω D j₀)) (C_injective _ _) _ (halg ω)`. Use `IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩`.

Conclude with `hr k`. Prove the components needed by the constructor for the conclusion. Introduce `c`. Establish `hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪ Set.range (C : Ω → CT Ω D j₀))`. Proceed by induction on `c using MvPolynomial.induction_on with`.

Consider the case `C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)`. Consider the case `add p r hp hr => exact add_mem hp hr`. Consider the case `mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))`. Establish `h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪ Set.range (C : Ω → CT Ω D j₀))) c` using `isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)`. Use `IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0` and prove the remaining obligations.

Introduce and unpack `y ⟨hy | ⟨ω, rfl⟩, -⟩`. Take `⟨q, rfl⟩` from `hy`. Establish `hq : (X q : CT Ω D j₀) ∈ Algebra.adjoin K (Set.range (gs (D` using `D) x j₀)) := Algebra.subset_adjoin ⟨q.1, by rw [gs, if_neg q.2, xv_of_not q.2]⟩`. Conclude with `isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)`. Conclude with `hC ω`.
-/
theorem alg_CT (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) := by
  have hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C ω : CT Ω D j₀) := by
    intro ω
    have h1 := isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT Ω D j₀)) (C_injective _ _) _
      (halg ω)
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩
    exact hr k
  constructor
  intro c
  have hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪ Set.range (C : Ω → CT Ω D j₀)) := by
    induction c using MvPolynomial.induction_on with
    | C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
    | add p r hp hr => exact add_mem hp hr
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))
  have h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪
      Set.range (C : Ω → CT Ω D j₀))) c :=
    isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0
  rintro y ⟨hy | ⟨ω, rfl⟩, -⟩
  · obtain ⟨q, rfl⟩ := hy
    have hq : (X q : CT Ω D j₀) ∈ Algebra.adjoin K (Set.range (gs (D := D) x j₀)) :=
      Algebra.subset_adjoin ⟨q.1, by rw [gs, if_neg q.2, xv_of_not q.2]⟩
    exact isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)
  · exact hC ω

/- English proof (translation)
Assume the negation of the conclusion as `hdep`. Establish `hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧ G.totalDegree = n`. Rewrite `hdep` using `[algebraicIndependent_iff]`. Use `push Not at hdep`. Take `⟨G, h1, h2⟩` from `hdep`.

Conclude with `⟨_, G, h1, h2, rfl⟩`. Take `⟨G, hG0, hGne, hGdeg⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree → aeval (gs x j₀) H = 0 → H = 0`. Introduce `H hH h0`. Assume the negation of the conclusion as `hne`.

Rewrite `hH` using `[hGdeg]`. Conclude with `Nat.find_min hex hH ⟨H, h0, hne, rfl⟩`. Establish `hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}, ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0`. Introduce `q`. Rewrite using `[← pderiv_aeval, hG0, map_zero]`.

Establish `hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}, ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = aeval (gs x j₀) (pderiv q.1 G) - if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2)`. Introduce `q`. Repeatedly rewrite using `[pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `congr 1`. Use `split_ifs with h0`.

Conclude with `Finset.sum_eq_zero fun p _ => if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))`. Rewrite using `[Finset.sum_eq_single (q.1.1, j₀)]`. Conclude with `if_pos (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)`. Introduce `p _ hp`. Conclude with `if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hpos : 0 < G.totalDegree`. Assume the negation of the conclusion as `h`. Establish `h0 : G.totalDegree = 0` using `by omega`.

Rewrite `h0` using `[totalDegree_eq_zero_iff_eq_C]`. Rewrite `hG0` using `[h0, aeval_C]`. Establish `hc : coeff 0 G = 0` using `(algebraMap K (CT Ω D j₀)).injective (by rw [hG0, map_zero])`. Conclude with `hGne (by rw [h0, hc, C_0])`. Take `⟨p₁, hp₁ne, hp₁lt⟩` from `exists_pderiv_ne_zero_lt' G hpos`.

Establish `hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0` using `fun h => hp₁ne (hmin _ hp₁lt h)`. Establish `hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hp₁` to reduce the goal to its premises.

Distinguish the cases in `hZ : Zs j₀ p₁`. Take `⟨h1, h2⟩` from `hZ`. Take `⟨i, hi⟩` from `Fin.exists_succ_eq.mpr h1`. Establish `e : p₁ = (i.succ, j₀)` using `Prod.ext_iff.mpr ⟨hi.symm, h2⟩`. Rewrite using `[e]`.

Conclude with `hall i`. Establish `h` using `hd ⟨p₁, hZ⟩`. Rewrite `h` using `[hsum]`. Use `split_ifs at h with h0`. Rewrite `h` using `[sub_zero]`. Then use the resulting hypothesis.

Take `⟨i, hi⟩` from `Fin.exists_succ_eq.mpr h0`. Simplify using `only at h hi`. Rewrite `h` using `[← hi, hall i, zero_mul, sub_zero]`. Conclude with `h`. Take `⟨i, hi⟩` from `hexi`.

Establish `hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D` using `D) x j₀))) (C (rr x j₀ k) : CT Ω D j₀) := by`. Introduce `k`. Distinguish the cases in `hk : k = j₀`. Substitute `hk` using the available equality. Rewrite using `[rr, div_self hx₀, C_1]`.

Conclude with `isAlgebraic_one`. Establish `hq : ¬ Zs j₀ (i.succ, k)` using `fun h => hk h.2`. Establish `h` using `hd ⟨(i.succ, k), hq⟩`. Rewrite `h` using `[hsum, if_neg (Fin.succ_ne_zero i), sub_eq_zero]`. Establish `m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀))`.

Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨_, rfl⟩`. Establish `m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀))`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨_, rfl⟩`.

Use `⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `congrArg (fun f => Polynomial.coeff f 1) h0`. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero, if_pos, one_ne_zero, if_false, sub_zero] at h1`. Conclude with `hi (congrArg Subtype.val h1)`.

Rewrite using `[map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]`. Conclude with `sub_eq_zero.mpr h.symm`. Use `alg_CT x j₀ halg hr` as an intermediate fact. Establish `htb : IsTranscendenceBasis K (gs (D` using `D) x j₀) := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀) (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])`. Conclude with `hdep htb.1`.
-/
theorem gs_indep [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    AlgebraicIndependent K (gs (D := D) x j₀) := by
  classical
  by_contra hdep
  have hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧
      G.totalDegree = n := by
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨G, h1, h2⟩ := hdep
    exact ⟨_, G, h1, h2, rfl⟩
  obtain ⟨G, hG0, hGne, hGdeg⟩ := Nat.find_spec hex
  have hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree →
      aeval (gs x j₀) H = 0 → H = 0 := by
    intro H hH h0
    by_contra hne
    rw [hGdeg] at hH
    exact Nat.find_min hex hH ⟨H, h0, hne, rfl⟩
  have hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0 := by
    intro q; rw [← pderiv_aeval, hG0, map_zero]
  have hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) =
        aeval (gs x j₀) (pderiv q.1 G) -
          if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2) := by
    intro q
    simp_rw [pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with h0
    · exact Finset.sum_eq_zero fun p _ =>
        if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))
    · rw [Finset.sum_eq_single (q.1.1, j₀)]
      · exact if_pos (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)
      · intro p _ hp
        exact if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))
      · intro h; exact absurd (Finset.mem_univ _) h
  have hpos : 0 < G.totalDegree := by
    by_contra h
    have h0 : G.totalDegree = 0 := by omega
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, aeval_C] at hG0
    have hc : coeff 0 G = 0 :=
      (algebraMap K (CT Ω D j₀)).injective (by rw [hG0, map_zero])
    exact hGne (by rw [h0, hc, C_0])
  obtain ⟨p₁, hp₁ne, hp₁lt⟩ := exists_pderiv_ne_zero_lt' G hpos
  have hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0 := fun h => hp₁ne (hmin _ hp₁lt h)
  have hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp₁
    by_cases hZ : Zs j₀ p₁
    · obtain ⟨h1, h2⟩ := hZ
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h1
      have e : p₁ = (i.succ, j₀) := Prod.ext_iff.mpr ⟨hi.symm, h2⟩
      rw [e]; exact hall i
    · have h := hd ⟨p₁, hZ⟩
      rw [hsum] at h
      split_ifs at h with h0
      · rwa [sub_zero] at h
      · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
        simp only at h hi
        rw [← hi, hall i, zero_mul, sub_zero] at h
        exact h
  obtain ⟨i, hi⟩ := hexi
  have hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀) := by
    intro k
    by_cases hk : k = j₀
    · subst hk
      rw [rr, div_self hx₀, C_1]
      exact isAlgebraic_one
    · have hq : ¬ Zs j₀ (i.succ, k) := fun h => hk h.2
      have h := hd ⟨(i.succ, k), hq⟩
      rw [hsum, if_neg (Fin.succ_ne_zero i), sub_eq_zero] at h
      have m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      have m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      refine ⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun f => Polynomial.coeff f 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, if_pos, one_ne_zero, if_false, sub_zero] at h1
        exact hi (congrArg Subtype.val h1)
      · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
        exact sub_eq_zero.mpr h.symm
  have := alg_CT x j₀ halg hr
  have htb : IsTranscendenceBasis K (gs (D := D) x j₀) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀)
      (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])
  exact hdep htb.1

/- English proof (translation)
The claim follows from `((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic`.
-/
theorem gs_alg [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) :=
  ((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite
    (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic

/- English proof (translation)
Introduce `ω`. Establish `hadd` using `trdeg_add_eq (R := K) (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)`. Rewrite `hadd` using `[hbig, htr]`. Establish `h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0`. Break down `(Cardinal.add_eq_left_iff).mp hadd with h | h` into its components or cases.

Conclude with `absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))`. Conclude with `h`. Establish `halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω` using `by first`. Consider the case `exact Algebra.trdeg_eq_zero_iff.mp h0`. Consider the case `exact trdeg_eq_zero_iff.mp h0`.

Conclude with `IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)`.
-/
theorem halg_of (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by
  intro ω
  have hadd := trdeg_add_eq (R := K)
    (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)
  rw [hbig, htr] at hadd
  have h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0 := by
    rcases (Cardinal.add_eq_left_iff).mp hadd with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))
    · exact h
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω := by
    first
    | exact Algebra.trdeg_eq_zero_iff.mp h0
    | exact trdeg_eq_zero_iff.mp h0
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)

end Formalism.L2.Pj.GenSect
