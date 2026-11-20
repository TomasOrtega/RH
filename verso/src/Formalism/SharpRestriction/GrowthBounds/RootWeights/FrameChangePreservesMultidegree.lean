import Formalism.SharpRestriction.GrowthBounds.RootWeights.EBeta

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def embed_GL2_standard_swap {k : Type} [CommRing k] {r : ℕ} [NeZero r] (cc : Fin r → k) : Matrix (Fin r) (Fin r) k :=
  fun b a => (if b = a then 1 else 0) + (cc b - if b = lastIdx r then 1 else 0) * (if a = lastIdx r then 1 else 0)

def frameMatrixInverse {k : Type} [CommRing k] {r : ℕ} [NeZero r] (cc : Fin r → k) (u : k) : Matrix (Fin r) (Fin r) k :=
  fun b a => (if b = a then 1 else 0) -
    u * (cc b - if b = lastIdx r then 1 else 0) * (if a = lastIdx r then 1 else 0)

/- English proof (translation)
Simplify using `[embed_GL2_standard_swap]`.
-/
theorem frame_matrix_last_column {k : Type} [CommRing k] {r : ℕ} [NeZero r] (cc : Fin r → k) (a : Fin r) :
    embed_GL2_standard_swap cc a (lastIdx r) = cc a := by
  simp [embed_GL2_standard_swap]

/- English proof (translation)
Use extensionality with `b a`. Simplify using `only [Matrix.mul_apply, embed_GL2_standard_swap, frameMatrixInverse, Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Simplify using `only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `h1 : a = lastIdx r`. Substitute `h1` using the available equality.

Distinguish the cases in `h2 : b = lastIdx r`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Take the linear combination `(1 - cc (lastIdx r)) * hu`. Simplify using `[h2]`.

Take the linear combination `(-(cc b)) * hu`. Simplify using `[h1]`.
-/
theorem frame_matrix_mul_inverse {k : Type} [CommRing k] {r : ℕ} [NeZero r] (cc : Fin r → k) (u : k)
    (hu : cc (lastIdx r) * u = 1) : embed_GL2_standard_swap cc * frameMatrixInverse cc u = 1 := by
  ext b a
  simp only [Matrix.mul_apply, embed_GL2_standard_swap, frameMatrixInverse, Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h1 : a = lastIdx r
  · subst h1
    by_cases h2 : b = lastIdx r
    · subst h2
      simp
      linear_combination (1 - cc (lastIdx r)) * hu
    · simp [h2]
      linear_combination (-(cc b)) * hu
  · simp [h1]

open Classical in

def frameCoordinateEvaluation {R : Type} [CommRing R] {ι : Type} {r : ℕ} (LL : Letters ι) (S : Set ι) {k1 : Type} [CommRing k1]
    (ph : MvPolynomial (ι × Fin r) R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) :
    MvPolynomial (ι × Fin r) k1 →+* k1 :=
  eval₂Hom (RingHom.id k1) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ a : Fin r, ph (X (v.1, a)) * g0 a v.2
       else ∑ a : Fin r, g0inv v.2 a * ph (X (v.1, a)))
    else ph (X v)

/- English proof (translation)
Establish `hh : ∀ b c, ∑ a, g0 b a * g0inv a c = if b = c then 1 else 0`. Introduce `b c`. Use `congrFun (congrFun h b) c` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[frameCoordinateEvaluation, eBeta]`. Introduce and unpack `⟨i, c⟩`. Distinguish the cases in `hS : i ∈ S`. Distinguish the cases in `hv : LL.vec i = true`.

Simplify using `only [RingHom.comp_apply, eBeta, frameCoordinateEvaluation, eval₂Hom_X', hS, hv, if_true, map_sum, map_mul, eval₂Hom_C, RingHom.id_apply]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring` and prove the remaining obligations.

Use `_ = ph (X (i, c)) := by simp [hh]`. Simplify using `only [RingHom.comp_apply, eBeta, frameCoordinateEvaluation, eval₂Hom_X', hS, hv, if_true, map_sum, map_mul, eval₂Hom_C, RingHom.id_apply, if_false, Bool.false_eq_true]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring` and prove the remaining obligations. Use `_ = ph (X (i, c)) := by simp [hh]`. Simplify using `[frameCoordinateEvaluation, eBeta, hS]`.
-/
theorem frame_evaluation_comp_change {R : Type} [CommRing R] {ι : Type} {r : ℕ} (LL : Letters ι) (S : Set ι) {k1 : Type}
    [CommRing k1] (ph : MvPolynomial (ι × Fin r) R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1)
    (h : g0 * g0inv = 1) :
    (frameCoordinateEvaluation LL S ph g0 g0inv).comp (eBeta LL S (ph.comp C) g0 g0inv) = ph := by
  have hh : ∀ b c, ∑ a, g0 b a * g0inv a c = if b = c then 1 else 0 := by
    intro b c
    have := congrFun (congrFun h b) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [frameCoordinateEvaluation, eBeta]
  · rintro ⟨i, c⟩
    by_cases hS : i ∈ S
    · by_cases hv : LL.vec i = true
      · simp only [RingHom.comp_apply, eBeta, frameCoordinateEvaluation, eval₂Hom_X', hS, hv, if_true, map_sum, map_mul,
          eval₂Hom_C, RingHom.id_apply]
        calc ∑ a, g0inv a c * ∑ b, ph (X (i, b)) * g0 b a
            = ∑ b, ph (X (i, b)) * ∑ a, g0 b a * g0inv a c := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
          _ = ph (X (i, c)) := by simp [hh]
      · simp only [RingHom.comp_apply, eBeta, frameCoordinateEvaluation, eval₂Hom_X', hS, hv, if_true, map_sum, map_mul,
          eval₂Hom_C, RingHom.id_apply, if_false, Bool.false_eq_true]
        calc ∑ a, g0 c a * ∑ b, g0inv a b * ph (X (i, b))
            = ∑ b, (∑ a, g0 c a * g0inv a b) * ph (X (i, b)) := by
              simp only [Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
          _ = ph (X (i, c)) := by simp [hh]
    · simp [frameCoordinateEvaluation, eBeta, hS]

open Classical in

def letterDegreeWeight {ι : Type} {r : ℕ} (i : ι) : ι × Fin r → ℕ := fun v => if v.1 = i then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]`. Simplify using `[letterDegreeWeight, multideg]`.
-/
theorem letter_weight_eq_multidegree {ι : Type} [Fintype ι] {r : ℕ} (i : ι) (m : ι × Fin r →₀ ℕ) :
    Finsupp.weight (letterDegreeWeight i) m = multideg m i := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  simp [letterDegreeWeight, multideg]

/- English proof (translation)
Rewrite using `[G.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `m hm`. Rewrite using `[eBeta, eval₂Hom_monomial, RingHom.comp_apply]`. Apply `IsWeightedHomogeneous.C_mul` to reduce the goal to its premises.

Rewrite using `[← hG m hm, ← letter_weight_eq_multidegree, Finsupp.weight_apply]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `v _`. Apply `IsWeightedHomogeneous.pow` to reduce the goal to its premises. Use `split_ifs`.

Conclude with `IsWeightedHomogeneous.sum _ _ _ fun a _ => (isWeightedHomogeneous_X k1 (letterDegreeWeight i) (v.1, a)).C_mul _`. Conclude with `IsWeightedHomogeneous.sum _ _ _ fun a _ => (isWeightedHomogeneous_X k1 (letterDegreeWeight i) (v.1, a)).C_mul _`. Conclude with `isWeightedHomogeneous_X k1 (letterDegreeWeight i) v`.
-/
theorem frame_change_weighted_homogeneous {R : Type} [CommRing R] {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι)
    {k1 : Type} [CommRing k1] (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) (i : ι) (n : ℕ)
    (G : MvPolynomial (ι × Fin r) R) (hG : ∀ m ∈ G.support, multideg m i = n) :
    IsWeightedHomogeneous (letterDegreeWeight i) (eBeta LL S j g0 g0inv G) n := by
  classical
  rw [G.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [eBeta, eval₂Hom_monomial, RingHom.comp_apply]
  apply IsWeightedHomogeneous.C_mul
  rw [← hG m hm, ← letter_weight_eq_multidegree, Finsupp.weight_apply]
  apply IsWeightedHomogeneous.prod
  intro v _
  apply IsWeightedHomogeneous.pow
  split_ifs
  · exact IsWeightedHomogeneous.sum _ _ _ fun a _ => (isWeightedHomogeneous_X k1 (letterDegreeWeight i) (v.1, a)).C_mul _
  · exact IsWeightedHomogeneous.sum _ _ _ fun a _ => (isWeightedHomogeneous_X k1 (letterDegreeWeight i) (v.1, a)).C_mul _
  · exact isWeightedHomogeneous_X k1 (letterDegreeWeight i) v

/- English proof (translation)
Introduce `m hm i`. Establish `hG' : ∀ m ∈ G.support, multideg m i = d i`. Introduce `m hm`. Use `(MvPolynomial.mem_restrictSupport_iff R).1 hG` as an intermediate fact. Conclude with `this (by simpa using hm) i`.

Use `frame_change_weighted_homogeneous LL S j g0 g0inv i (d i) G hG' (mem_support_iff.1 hm)` as an intermediate fact. Rewrite `this` using `[letter_weight_eq_multidegree]`. Then use the resulting hypothesis.
-/
theorem frame_change_preserves_multidegree {R : Type} [CommRing R] {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι)
    {k1 : Type} [CommRing k1] (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin r) R) (hG : G ∈ Pol R r d) :
    ∀ m ∈ (eBeta LL S j g0 g0inv G).support, ∀ i, multideg m i = d i := by
  intro m hm i
  have hG' : ∀ m ∈ G.support, multideg m i = d i := by
    intro m hm
    have := (MvPolynomial.mem_restrictSupport_iff R).1 hG
    exact this (by simpa using hm) i
  have := frame_change_weighted_homogeneous LL S j g0 g0inv i (d i) G hG' (mem_support_iff.1 hm)
  rwa [letter_weight_eq_multidegree] at this

open Classical in
/- English proof (translation)
Unfold `eWt`. Apply the tactic sequence `rw [Finsupp.sum_fintype _ _ (by intro v; split_ifs <;> simp), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (lastIdx r)]`. Simplify using the standard rewrite rules.

Introduce `c _ hc`. Simplify using `[hc]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem last_column_weight_eq {ι : Type} [Fintype ι] {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι)
    (m : ι × Fin r →₀ ℕ) :
    eWt LL S m = ∑ i : ι, (if i ∈ S then
      (if LL.vec i then (m (i, lastIdx r) : ℤ) else -(m (i, lastIdx r) : ℤ)) else 0) := by
  unfold eWt
  rw [Finsupp.sum_fintype _ _ (by intro v; split_ifs <;> simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (lastIdx r)]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h1 : (m (A (lastIdx r), lastIdx r) : ℤ) = ∑ i : ι, (if i = A (lastIdx r) then (m (i, lastIdx r) : ℤ) else 0)` using `by simp`. Establish `hle : ∀ i, (m (i, lastIdx r) : ℤ) ≤ (d i : ℤ)`. Introduce `i`. Rewrite using `[← hm i]`. Unfold `multideg`.

Conclude with `Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)` after adjusting the coercions. Rewrite using `[last_column_weight_eq, h1, degOther, Nat.cast_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Establish `hn : (0 : ℤ) ≤ (m (i, lastIdx r) : ℤ)` using `by positivity`.

Establish `hd : (0 : ℤ) ≤ (d i : ℤ)` using `by positivity`. Distinguish the cases in `hS : i ∈ S`. Distinguish the cases in `hv : LL.vec i = true`. Distinguish the cases in `hr : i ∈ Set.range A`. Take `⟨l, rfl⟩` from `hr`.

Distinguish the cases in `hl : l = lastIdx r`. Substitute `hl` using the available equality. Simplify using `[hS, hv]`. Use `h0 l hl` as an intermediate fact. Simplify using `only [hS, hv, if_true, this]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hne : i ≠ A (lastIdx r)` using `fun h => hr ⟨_, h.symm⟩`. Simplify using `only [hS, hv, hr, hne, if_true, if_false, not_false_eq_true, and_self, zero_add]`. Conclude with `hle i`. Apply the tactic sequence `simp only [hS, hv, if_true, if_false, Bool.false_eq_true, false_and, and_false, Nat.cast_zero, add_zero] split_ifs <;> omega`.

Apply the tactic sequence `simp only [hS, if_false, false_and, Nat.cast_zero, add_zero] split_ifs <;> omega`.
-/
theorem last_column_weight_bound {ι : Type} [Fintype ι] {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι) (A : Fin r → ι)
    (d : ι → ℕ) (m : ι × Fin r →₀ ℕ) (hm : ∀ i, multideg m i = d i)
    (h0 : ∀ l, l ≠ lastIdx r → m (A l, lastIdx r) = 0) :
    eWt LL S m ≤ (m (A (lastIdx r), lastIdx r) : ℤ) + (degOther LL S A d : ℤ) := by
  classical
  have h1 : (m (A (lastIdx r), lastIdx r) : ℤ) =
      ∑ i : ι, (if i = A (lastIdx r) then (m (i, lastIdx r) : ℤ) else 0) := by simp
  have hle : ∀ i, (m (i, lastIdx r) : ℤ) ≤ (d i : ℤ) := by
    intro i
    rw [← hm i]
    unfold multideg
    exact_mod_cast Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [last_column_weight_eq, h1, degOther, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hn : (0 : ℤ) ≤ (m (i, lastIdx r) : ℤ) := by positivity
  have hd : (0 : ℤ) ≤ (d i : ℤ) := by positivity
  by_cases hS : i ∈ S
  · by_cases hv : LL.vec i = true
    · by_cases hr : i ∈ Set.range A
      · obtain ⟨l, rfl⟩ := hr
        by_cases hl : l = lastIdx r
        · subst hl
          simp [hS, hv]
        · have := h0 l hl
          simp only [hS, hv, if_true, this]
          split_ifs <;> simp
      · have hne : i ≠ A (lastIdx r) := fun h => hr ⟨_, h.symm⟩
        simp only [hS, hv, hr, hne, if_true, if_false, not_false_eq_true, and_self, zero_add]
        exact hle i
    · simp only [hS, hv, if_true, if_false, Bool.false_eq_true, false_and, and_false, Nat.cast_zero, add_zero]
      split_ifs <;> omega
  · simp only [hS, if_false, false_and, Nat.cast_zero, add_zero]
    split_ifs <;> omega

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq, map_mul, Finsupp.prod_fintype _ _ (by simp), map_prod]`. Simplify using `[frameCoordinateEvaluation]`.
-/
theorem frame_evaluation_monomial_sum {R : Type} [CommRing R] {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι)
    {k1 : Type} [CommRing k1] (ph : MvPolynomial (ι × Fin r) R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1)
    (P : MvPolynomial (ι × Fin r) k1) :
    frameCoordinateEvaluation LL S ph g0 g0inv P =
      ∑ m ∈ P.support, coeff m P * ∏ v, (frameCoordinateEvaluation LL S ph g0 g0inv (X v)) ^ (m v) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [monomial_eq, map_mul, Finsupp.prod_fintype _ _ (by simp), map_prod]
  simp [frameCoordinateEvaluation]

/- English proof (translation)
Introduce `R _ ι _ LL r _ S A hinj hA d G hG th hth hlt`. Take `⟨hne, hrel⟩` from `hC R ι r A hinj`. Set `k1` to `Localization.Away ((matA R A).adjugate (lastIdx r) (lastIdx r))`. Set `ph : MvPolynomial (ι × Fin r) R →+* k1` to `algebraMap _ k1`. Set `cc : Fin r → k1` to `fun a => ph ((matA R A).adjugate a (lastIdx r))`.

Set `u : k1` to `IsLocalization.Away.invSelf ((matA R A).adjugate (lastIdx r) (lastIdx r))`. Establish `hu : cc (lastIdx r) * u = 1` using `IsLocalization.Away.mul_invSelf _`. Establish `hg` using `frame_matrix_mul_inverse cc u hu`. Establish `himg : ph G = frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (eBeta LL S (ph.comp C) (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) G)` using `(RingHom.congr_fun (frame_evaluation_comp_change LL S ph _ _ hg) G).symm`. Establish `hX : ∀ l, frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X (A l, lastIdx r)) = if l = lastIdx r then ph (detA (R` using `R) A) else 0 := by`.

Introduce `l`. Establish `h1 : frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X (A l, lastIdx r)) = ∑ a, ph (X (A l, a)) * embed_GL2_standard_swap cc a (lastIdx r)`. Simplify using `[frameCoordinateEvaluation, (hA l).1, (hA l).2]`. Rewrite using `[h1]`. Simplify using `only [frame_matrix_last_column]`.

Establish `h2` using `congrFun (congrFun (Matrix.mul_adjugate (matA R A)) l) (lastIdx r)`. Rewrite `h2` using `[Matrix.mul_apply]`. Establish `h3` using `congrArg ph h2`. Rewrite `h3` using `[map_sum]`. Simplify using `only [map_mul] at h3`.

Use `h3.trans ?_` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Use `split_ifs`. Rewrite using `[mul_one]`. Both sides reduce to the same expression.

Rewrite using `[mul_zero, map_zero]`. Establish `hdvd : ph (detA (R` using `R) A) ^ (th - degOther LL S A d).toNat ∣ ph G := by`. Rewrite using `[himg, frame_evaluation_monomial_sum]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `m hm`.

Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Distinguish the cases in `h0 : ∀ l, l ≠ lastIdx r → m (A l, lastIdx r) = 0`. Establish `hb` using `last_column_weight_bound LL S A d m (frame_change_preserves_multidegree LL S _ _ _ d G hG m hm) h0`. Establish `hw` using `hS R ι LL r S k1 (ph.comp C) _ _ hg G th hth m hm`. Establish `hN : (th - degOther LL S A d).toNat ≤ m (A (lastIdx r), lastIdx r)` using `by omega`.

Use `(pow_dvd_pow _ hN).trans ?_` and prove the remaining obligations. Establish `h5` using `Finset.dvd_prod_of_mem (fun v => (frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X v)) ^ (m v)) (Finset.mem_univ (A (lastIdx r), lastIdx r))`. Simplify using `only [hX, if_true] at h5`. Conclude with `h5`. Use `push Not at h0`.

Take `⟨l, hl, hml⟩` from `h0`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ (A l, lastIdx r)) (by rw [hX, if_neg hl]; exact zero_pow hml)]`. Conclude with `dvd_zero _`. Take `⟨z, hz⟩` from `hdvd`. Take `⟨⟨w, s⟩, hws⟩` from `IsLocalization.surj (Submonoid.powers ((matA R A).adjugate (lastIdx r) (lastIdx r))) z`.

Take `⟨M, hM⟩` from `s.2`. Establish `hinj' : Function.Injective ph` using `IsLocalization.injective k1 (powers_le_nonZeroDivisors_of_noZeroDivisors hne)`. Establish `heq : G * ((matA R A).adjugate (lastIdx r) (lastIdx r)) ^ M = detA (R` using `R) A ^ (th - degOther LL S A d).toNat * w := by`. Apply `hinj'` to reduce the goal to its premises. Simplify using `only at hws hM`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(hrel.pow).dvd_of_dvd_mul_right ⟨w, heq⟩`.
-/
theorem height_bound_of_weights (hS : HSupp) (hC : HCop) : E1 := by
  intro R _ ι _ LL r _ S A hinj hA d G hG th hth hlt
  classical
  obtain ⟨hne, hrel⟩ := hC R ι r A hinj
  let k1 := Localization.Away ((matA R A).adjugate (lastIdx r) (lastIdx r))
  let ph : MvPolynomial (ι × Fin r) R →+* k1 := algebraMap _ k1
  let cc : Fin r → k1 := fun a => ph ((matA R A).adjugate a (lastIdx r))
  let u : k1 := IsLocalization.Away.invSelf ((matA R A).adjugate (lastIdx r) (lastIdx r))
  have hu : cc (lastIdx r) * u = 1 := IsLocalization.Away.mul_invSelf _
  have hg := frame_matrix_mul_inverse cc u hu
  have himg : ph G = frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u)
      (eBeta LL S (ph.comp C) (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) G) :=
    (RingHom.congr_fun (frame_evaluation_comp_change LL S ph _ _ hg) G).symm
  have hX : ∀ l, frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X (A l, lastIdx r)) =
      if l = lastIdx r then ph (detA (R := R) A) else 0 := by
    intro l
    have h1 : frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X (A l, lastIdx r)) =
        ∑ a, ph (X (A l, a)) * embed_GL2_standard_swap cc a (lastIdx r) := by
      simp [frameCoordinateEvaluation, (hA l).1, (hA l).2]
    rw [h1]
    simp only [frame_matrix_last_column]
    have h2 := congrFun (congrFun (Matrix.mul_adjugate (matA R A)) l) (lastIdx r)
    rw [Matrix.mul_apply] at h2
    have h3 := congrArg ph h2
    rw [map_sum] at h3
    simp only [map_mul] at h3
    refine h3.trans ?_
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; rfl
    · rw [mul_zero, map_zero]
  have hdvd : ph (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ ph G := by
    rw [himg, frame_evaluation_monomial_sum]
    apply Finset.dvd_sum
    intro m hm
    apply Dvd.dvd.mul_left
    by_cases h0 : ∀ l, l ≠ lastIdx r → m (A l, lastIdx r) = 0
    · have hb := last_column_weight_bound LL S A d m (frame_change_preserves_multidegree LL S _ _ _ d G hG m hm) h0
      have hw := hS R ι LL r S k1 (ph.comp C) _ _ hg G th hth m hm
      have hN : (th - degOther LL S A d).toNat ≤ m (A (lastIdx r), lastIdx r) := by omega
      refine (pow_dvd_pow _ hN).trans ?_
      have h5 := Finset.dvd_prod_of_mem
        (fun v => (frameCoordinateEvaluation LL S ph (embed_GL2_standard_swap cc) (frameMatrixInverse cc u) (X v)) ^ (m v))
        (Finset.mem_univ (A (lastIdx r), lastIdx r))
      simp only [hX, if_true] at h5
      exact h5
    · push Not at h0
      obtain ⟨l, hl, hml⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ (A l, lastIdx r)) (by rw [hX, if_neg hl]; exact zero_pow hml)]
      exact dvd_zero _
  obtain ⟨z, hz⟩ := hdvd
  obtain ⟨⟨w, s⟩, hws⟩ := IsLocalization.surj
    (Submonoid.powers ((matA R A).adjugate (lastIdx r) (lastIdx r))) z
  obtain ⟨M, hM⟩ := s.2
  have hinj' : Function.Injective ph :=
    IsLocalization.injective k1 (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  have heq : G * ((matA R A).adjugate (lastIdx r) (lastIdx r)) ^ M =
      detA (R := R) A ^ (th - degOther LL S A d).toNat * w := by
    apply hinj'
    simp only at hws hM
    calc ph (G * ((matA R A).adjugate (lastIdx r) (lastIdx r)) ^ M)
        = ph G * ph (s : MvPolynomial (ι × Fin r) R) := by rw [map_mul, hM]
      _ = ph (detA (R := R) A) ^ (th - degOther LL S A d).toNat *
            (z * ph (s : MvPolynomial (ι × Fin r) R)) := by rw [hz, mul_assoc]
      _ = ph (detA (R := R) A) ^ (th - degOther LL S A d).toNat * ph w := congrArg _ hws
      _ = ph (detA (R := R) A ^ (th - degOther LL S A d).toNat * w) := by rw [map_mul, map_pow]
  exact (hrel.pow).dvd_of_dvd_mul_right ⟨w, heq⟩

end Formalism.MainNotions.G.GLWeightTheory
