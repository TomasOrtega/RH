import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFCnt

noncomputable section

namespace PI.VolStabS.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

/- English proof (translation)
Unfold `PI.VolStabS.ffH`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b hb`.

Simplify using `[Pi.single_apply, hb]`.
-/
private theorem ffH_single_right {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (j : Fin M) :
    PI.VolStabS.ffH σ J x (Pi.single j 1) = ∑ i, σ (x i) * J i j := by
  unfold PI.VolStabS.ffH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

/- English proof (translation)
Simplify using `only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Use `smul_right c x y := by`. Simplify using `only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Use `herm x y := by`.

Simplify using `only [ffH, map_sum, map_mul, hσ, hJ]`. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Use `nondeg x hx := by`. Establish `hv : Matrix.vecMul (fun i => σ (x i)) J = 0`.

Use function extensionality and compare the values at `j0`. Use `hx (Pi.single j0 1)` as an intermediate fact. Simplify `this` using `[ffH, Pi.single_apply, Matrix.vecMul, dotProduct]`. Establish `hinv : (fun i => σ (x i)) = 0`. Use `congrArg (fun v => Matrix.vecMul v J⁻¹) hv` as an intermediate fact.

Simplify `this` using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one, Matrix.zero_vecMul]`. Use function extensionality and compare the values at `i`. Conclude with `σ.injective (by simpa using congrFun hinv i)`.
-/
theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

/- English proof (translation)
Rewrite using `[ffH_single_right, Fintype.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b hb`. Simplify using `[Pi.single_apply, hb]`.
-/
theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  rw [ffH_single_right, Fintype.sum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

end matrix

/- English proof (translation)
The claim follows from `{ add_right x y z := by show hV (φ x) (φ (y + z)) = hV (φ x) (φ y) + hV (φ x) (φ z) rw [map_add, hsV.add_right] smul_right c x y := by show hV (φ x) (φ (c • y)) = c * hV (φ x) (φ y) rw [map_smul, hsV.smul_right] herm x y := hsV.herm (φ x) (φ y) }`.
-/
private theorem isSq_comp_linearMap {K : Type} [Field K] {σ : K →+* K} {U V : Type}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {hV : V → V → K}
    (hsV : IsSq σ hV) (φ : U →ₗ[K] V) :
    IsSq σ (fun x y => hV (φ x) (φ y)) := {
  add_right x y z := by
    show hV (φ x) (φ (y + z)) = hV (φ x) (φ y) + hV (φ x) (φ z)
    rw [map_add, hsV.add_right]
  smul_right c x y := by
    show hV (φ x) (φ (c • y)) = c * hV (φ x) (φ y)
    rw [map_smul, hsV.smul_right]
  herm x y := hsV.herm (φ x) (φ y) }

/- English proof (translation)
Use `Nat.card_congr { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩ invFun := fun Y => ⟨b.constr K Y.1, fun x y => (isSq_comp_linearMap hsV (b.constr K Y.1)).ext_basis hsU b (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y⟩ left_inv := fun φ => by` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `b.ext` to reduce the goal to its premises. Introduce `i`. Simplify using the standard rewrite rules.

Use `right_inv := fun Y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `}`.
-/
theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y =>
        (isSq_comp_linearMap hsV (b.constr K Y.1)).ext_basis hsU b
          (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y⟩
      left_inv := fun φ => by
        apply Subtype.ext
        apply b.ext
        intro i
        simp
      right_inv := fun Y => by
        apply Subtype.ext
        funext i
        simp }

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

/- English proof (translation)
Rewrite using `[← h2]`. Conclude with `Module.card_eq_pow_finrank`.
-/
private theorem card_eq_card_sq_of_finrank_two (h2 : finrank k K = 2) :
    Fintype.card K = Fintype.card k ^ 2 := by
  rw [← h2]
  exact Module.card_eq_pow_finrank

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists k`. Take `⟨n, hprime, hn⟩` from `FiniteField.card k p`. Use `haveI : Fact p.Prime := ⟨hprime⟩`. Use `haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p`. Rewrite using `[hn]`.

Conclude with `add_pow_char_pow a b p (n : ℕ)`.
-/
private theorem add_pow_card_eq_add_pow_card (a b : K) :
    (a + b) ^ Fintype.card k = a ^ Fintype.card k + b ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hprime, hn⟩ := FiniteField.card k p
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [hn]
  exact add_pow_char_pow a b p (n : ℕ)

/- English proof (translation)
Establish `hq1 : 1 < Fintype.card k` using `Fintype.one_lt_card`. Establish `hP : (X ^ Fintype.card k - X : K[X]) ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero K hq1`. Establish `hsub : Finset.univ.image (algebraMap k K) ⊆ (X ^ Fintype.card k - X : K[X]).roots.toFinset`. Introduce `x hx`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.mp hx`.

Rewrite using `[Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow, FiniteField.pow_card, sub_self]`. Establish `hcard : (X ^ Fintype.card k - X : K[X]).roots.toFinset.card ≤ (Finset.univ.image (algebraMap k K)).card`. Rewrite using `[Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]`. Combine the equalities or inequalities in the displayed calculation. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub hcard`.

Establish `hmem : d ∈ (X ^ Fintype.card k - X : K[X]).roots.toFinset`. Rewrite using `[Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, hd, sub_self]`. Rewrite `hmem` using `[← heq]`. Take `⟨y, -, hy⟩` from `Finset.mem_image.mp hmem`. Conclude with `⟨y, hy⟩`.
-/
private theorem mem_range_algebraMap_of_pow_card_eq (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP : (X ^ Fintype.card k - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hsub : Finset.univ.image (algebraMap k K) ⊆
      (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hcard : (X ^ Fintype.card k - X : K[X]).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : K[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : K[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : d ∈ (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, hd, sub_self]
  rw [← heq] at hmem
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `hK` using `card_eq_card_sq_of_finrank_two (k := k) (K := K) h2`. Establish `hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y` using `fun y => by`. Rewrite using `[← pow_mul, ← sq, ← hK, FiniteField.pow_card]`. Establish `hfix : ∀ c : K, c ^ Fintype.card k = c → σ c = c`. Introduce `c hc`.

Take `⟨d0, rfl⟩` from `mem_range_algebraMap_of_pow_card_eq c hc`. Conclude with `σ.commutes d0`. Establish `hdich : ∀ x : K, σ x = x ∨ σ x = x ^ Fintype.card k`. Introduce `x`. Establish `hs : σ x + σ x ^ Fintype.card k = x + x ^ Fintype.card k`.

Rewrite using `[← map_pow, ← map_add]`. Conclude with `hfix _ (by rw [add_pow_card_eq_add_pow_card, hqq, add_comm])`. Establish `hm : σ x * σ x ^ Fintype.card k = x * x ^ Fintype.card k`. Rewrite using `[← map_pow, ← map_mul]`. Conclude with `hfix _ (by rw [mul_pow, hqq, mul_comm])`.

Establish `h0 : (σ x - x) * (σ x - x ^ Fintype.card k) = 0`. Take the linear combination `σ x * hs - hm`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.mp h)`. Conclude with `Or.inr (sub_eq_zero.mp h)`.

Introduce `x`. Assume the negation of the conclusion as `ha`. Establish `hq0 : Fintype.card k ≠ 0` using `Fintype.card_ne_zero`. Establish `hax : σ x = x` using `(hdich x).resolve_right ha`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, σ b ≠ b := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hne (AlgEquiv.ext fun y => by simpa using hcon y)`. Establish `hbq : σ b = b ^ Fintype.card k` using `(hdich b).resolve_left hb`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Conclude with `ha (by rw [map_zero, zero_pow hq0])`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hb (map_zero σ)`.

Break down `hdich (x * b) with h | h` into its components or cases. Rewrite `h` using `[map_mul, hax, hbq]`. Conclude with `hb (hbq.trans (mul_left_cancel₀ hx0 h))`. Rewrite `h` using `[map_mul, hax, hbq, mul_pow]`. Conclude with `ha (hax.trans (mul_right_cancel₀ (pow_ne_zero _ hb0) h))`.
-/
theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hfix : ∀ c : K, c ^ Fintype.card k = c → σ c = c := by
    intro c hc
    obtain ⟨d0, rfl⟩ := mem_range_algebraMap_of_pow_card_eq c hc
    exact σ.commutes d0
  have hdich : ∀ x : K, σ x = x ∨ σ x = x ^ Fintype.card k := by
    intro x
    have hs : σ x + σ x ^ Fintype.card k = x + x ^ Fintype.card k := by
      rw [← map_pow, ← map_add]
      exact hfix _ (by rw [add_pow_card_eq_add_pow_card, hqq, add_comm])
    have hm : σ x * σ x ^ Fintype.card k = x * x ^ Fintype.card k := by
      rw [← map_pow, ← map_mul]
      exact hfix _ (by rw [mul_pow, hqq, mul_comm])
    have h0 : (σ x - x) * (σ x - x ^ Fintype.card k) = 0 := by
      linear_combination σ x * hs - hm
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  intro x
  by_contra ha
  have hq0 : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  have hax : σ x = x := (hdich x).resolve_right ha
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgEquiv.ext fun y => by simpa using hcon y)
  have hbq : σ b = b ^ Fintype.card k := (hdich b).resolve_left hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_pow hq0])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (map_zero σ)
  rcases hdich (x * b) with h | h
  · rw [map_mul, hax, hbq] at h
    exact hb (hbq.trans (mul_left_cancel₀ hx0 h))
  · rw [map_mul, hax, hbq, mul_pow] at h
    exact ha (hax.trans (mul_right_cancel₀ (pow_ne_zero _ hb0) h))

/- English proof (translation)
The claim follows from `mem_range_algebraMap_of_pow_card_eq d hd`.
-/
theorem mem_range_of_pow (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := mem_range_algebraMap_of_pow_card_eq d hd

/- English proof (translation)
Distinguish the cases in `hd0 : d = 0`. Substitute `hd0` using the available equality. Rewrite using `[if_pos rfl, Nat.card_eq_one_iff_exists]`. Use `⟨⟨0, by simp⟩, fun y => Subtype.ext ?_⟩` and prove the remaining obligations. Break down `mul_eq_zero.mp y.2 with h | h` into its components or cases.

Conclude with `h`. Conclude with `(map_eq_zero σ).mp h`. Rewrite using `[if_neg hd0]`. Establish `hK` using `card_eq_card_sq_of_finrank_two (k := k) (K := K) h2`. Establish `hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y` using `fun y => by`.

Rewrite using `[← pow_mul, ← sq, ← hK, FiniteField.pow_card]`. Establish `hN : ∀ t : K, t * σ t = t ^ (Fintype.card k + 1)` using `fun t => by`. Rewrite using `[hfrob, pow_succ']`. Establish `hfixset : Finset.univ.filter (fun e : K => σ e = e) = Finset.univ.image (algebraMap k K)`. Use extensionality with `e`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Conclude with `mem_range_algebraMap_of_pow_card_eq e ((hfrob e).symm.trans he)`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `σ.commutes y`. Establish `hfixcard : (Finset.univ.filter (fun e : K => σ e = e)).card = Fintype.card k`. Rewrite using `[hfixset, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]`. Establish `hD : (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card + 1 = Fintype.card k`. Establish `hset : Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) = (Finset.univ.filter (fun e : K => σ e = e)).erase 0`.

Use extensionality with `e`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]`. Conclude with `and_comm`. Rewrite using `[hset, Finset.card_erase_add_one (by simp), hfixcard]`. Establish `hS : (Finset.univ.filter (fun t : K => t ≠ 0)).card + 1 = Fintype.card k ^ 2`.

Rewrite using `[Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, hK]`. Establish `hmaps : ∀ t ∈ Finset.univ.filter (fun t : K => t ≠ 0), t * σ t ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)`. Introduce `t ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢`. Use `⟨?_, mul_ne_zero ht ((map_ne_zero σ).mpr ht)⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hfrob (σ t), hfrob t, hqq, mul_comm]`. Establish `hsum` using `Finset.card_eq_sum_card_fiberwise hmaps`. Establish `hbound : ∀ e : K, ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = e)).card ≤ Fintype.card k + 1`. Introduce `e`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht`. Rewrite using `[Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos _), ← hN]`. Conclude with `ht.2`.

Use `_ ≤ Multiset.card (nthRoots (Fintype.card k + 1) e) := Multiset.toFinset_card_le _`. Use `_ ≤ Fintype.card k + 1 := card_nthRoots _ _`. Establish `htarget : Nat.card {t : K // t * σ t = d} = ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = d)).card`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`.

Use extensionality with `t`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `ht`. Use `⟨?_, ht⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hd0 (by simpa using ht.symm)`. Conclude with `fun ht => ht.2`. Rewrite using `[htarget]`. Use `le_antisymm (hbound d) (not_lt.mp fun hlt => ?_)` and prove the remaining obligations.

Establish `hdD : d ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)`. Simplify using `[hd, hd0]`. Establish `hlt2 : (Finset.univ.filter (fun t : K => t ≠ 0)).card < (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card * (Fintype.card k + 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hS`, `hlt2` using `[← hD]`.

Use polynomial arithmetic with `[hS, hlt2]`.
-/
theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, by simp⟩, fun y => Subtype.ext ?_⟩
    rcases mul_eq_zero.mp y.2 with h | h
    · exact h
    · exact (map_eq_zero σ).mp h
  rw [if_neg hd0]
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hN : ∀ t : K, t * σ t = t ^ (Fintype.card k + 1) := fun t => by
    rw [hfrob, pow_succ']
  have hfixset : Finset.univ.filter (fun e : K => σ e = e) =
      Finset.univ.image (algebraMap k K) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro he
      exact mem_range_algebraMap_of_pow_card_eq e ((hfrob e).symm.trans he)
    · rintro ⟨y, rfl⟩
      exact σ.commutes y
  have hfixcard : (Finset.univ.filter (fun e : K => σ e = e)).card = Fintype.card k := by
    rw [hfixset, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
  have hD : (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card + 1 = Fintype.card k := by
    have hset : Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) =
        (Finset.univ.filter (fun e : K => σ e = e)).erase 0 := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact and_comm
    rw [hset, Finset.card_erase_add_one (by simp), hfixcard]
  have hS : (Finset.univ.filter (fun t : K => t ≠ 0)).card + 1 = Fintype.card k ^ 2 := by
    rw [Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, hK]
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t : K => t ≠ 0),
      t * σ t ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine ⟨?_, mul_ne_zero ht ((map_ne_zero σ).mpr ht)⟩
    rw [map_mul, hfrob (σ t), hfrob t, hqq, mul_comm]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ e : K, ((Finset.univ.filter (fun t : K => t ≠ 0)).filter
      (fun t => t * σ t = e)).card ≤ Fintype.card k + 1 := by
    intro e
    calc _ ≤ (nthRoots (Fintype.card k + 1) e).toFinset.card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos _), ← hN]
          exact ht.2
      _ ≤ Multiset.card (nthRoots (Fintype.card k + 1) e) := Multiset.toFinset_card_le _
      _ ≤ Fintype.card k + 1 := card_nthRoots _ _
  have htarget : Nat.card {t : K // t * σ t = d} =
      ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = d)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      refine ⟨?_, ht⟩
      rintro rfl
      exact hd0 (by simpa using ht.symm)
    · exact fun ht => ht.2
  rw [htarget]
  refine le_antisymm (hbound d) (not_lt.mp fun hlt => ?_)
  have hdD : d ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    simp [hd, hd0]
  have hlt2 : (Finset.univ.filter (fun t : K => t ≠ 0)).card <
      (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card * (Fintype.card k + 1) := by
    calc (Finset.univ.filter (fun t : K => t ≠ 0)).card = _ := hsum
      _ < ∑ e ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0), (Fintype.card k + 1) :=
          Finset.sum_lt_sum (fun e _ => hbound e) ⟨d, hdD, hlt⟩
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  rw [← hD] at hS hlt2
  nlinarith [hS, hlt2]

end field

/- English proof (translation)
Introduce `k K _ _ _ _ σ hσ hrank hne h2k M a haM J hJ hJdet T hT hTdet`. Use `haveI : Module.Finite k K := Module.finite_of_finrank_eq_succ hrank`. Use `haveI : Finite K := Module.finite_of_finite k`. Use `letI : Fintype k := Fintype.ofFinite k`. Use `letI : Fintype K := Fintype.ofFinite K`.

Establish `hfrob` using `frob_of_ne σ hrank hne`. Establish `hσr : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x` using `fun x => hσ x`. Establish `h2K : (2 : K) ≠ 0`. Establish `h2'` using `(algebraMap k K).injective.ne h2k`. Rewrite `h2'` using `[map_ofNat, map_zero]`. Then use the resulting hypothesis.

Establish `hK : Fintype.card K = Nat.card k ^ 2`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `card_eq_card_sq_of_finrank_two hrank`. Establish `hq0 : 0 < Nat.card k` using `Nat.card_pos`. Establish `hN : ∀ d, (σ : K →+* K) d = d → Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1`.

Introduce `d hd`. Rewrite using `[Nat.card_eq_fintype_card (α := k)]`. Conclude with `card_norm_fiber σ hfrob hrank d hd`. Establish `hsV : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) J)` using `ffH_isHS hσr J hJ hJdet`. Establish `hsU : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) T)` using `ffH_isHS hσr T hT hTdet`.

Establish `e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabS.ffGram (σ : K →+* K) J X = T} = Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) = PI.VolStabS.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)}`. Apply `Nat.card_congr` to reduce the goal to its premises. Apply `Equiv.subtypeEquivRight` to reduce the goal to its premises. Introduce `X`. Simplify using `only [Pi.basisFun_apply, ffH_single]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Substitute `h` using the available equality. Both sides reduce to the same expression. Introduce `h`.

Conclude with `Matrix.ext fun i j => h i j`. Take `⟨f, hf1, hf2⟩` from `exists_orth h2K a (Fin a → K) (PI.VolStabS.ffH (σ : K →+* K) T) hsU (by simp)`. Establish `hli` using `linIndep_orth hsU.toIsSq f hf1 hf2`. Choose the witnesses or unpack the hypotheses as in `⟨b', hb'⟩ : ∃ b' : Basis (Fin a) K (Fin a → K), ∀ i, b' i = f i := by`. Break down `isEmpty_or_nonempty (Fin a) with hE | hE` into its components or cases.

Conclude with `⟨Basis.empty _, fun i => isEmptyElim i⟩`. Conclude with `⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), fun i => by simp⟩`. Establish `e2` using `card_isom hsU.toIsSq hsV.toIsSq (Pi.basisFun K (Fin a))`. Establish `e3` using `card_isom hsU.toIsSq hsV.toIsSq b'`. Establish `e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) = PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j)} = Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) = if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i …`.

Establish `hdiag : ∀ i j, PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j) = if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0`. Introduce `i j`. Rewrite using `[hb', hb']`. Use `split_ifs with hij`. Substitute `hij` using the available equality.

Both sides reduce to the same expression. Conclude with `hf1 i j hij`. Simplify using `only [hdiag]`. Establish `key` using `e1.trans (e2.symm.trans (e3.trans e4))`. Establish `final` using `card_diag (Nat.card k) hq0 hK hσr h2K hN a M haM (Fin M → K) (PI.VolStabS.ffH (σ : K →+* K) J) hsV (by simp) (fun i => PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i)) (fun i => hsU.toIsSq.self_fixed (f i)) hf2`.

Conclude with `(congrArg (fun n : ℕ => (n : ℝ)) key).trans final`.
-/
theorem fFInert_holds : FFInert := by
  intro k K _ _ _ _ σ hσ hrank hne h2k M a haM J hJ hJdet T hT hTdet
  classical
  haveI : Module.Finite k K := Module.finite_of_finrank_eq_succ hrank
  haveI : Finite K := Module.finite_of_finite k
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ hrank hne
  have hσr : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have h2' := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at h2'
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact card_eq_card_sq_of_finrank_two hrank
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob hrank d hd
  have hsV : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) J) :=
    ffH_isHS hσr J hJ hJdet
  have hsU : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) T) :=
    ffH_isHS hσr T hT hTdet
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabS.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i)
            (Pi.basisFun K (Fin a) j)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro X
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      subst h
      rfl
    · intro h
      exact Matrix.ext fun i j => h i j
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabS.ffH (σ : K →+* K) T) hsU (by simp)
  have hli := linIndep_orth hsU.toIsSq f hf1 hf2
  obtain ⟨b', hb'⟩ : ∃ b' : Basis (Fin a) K (Fin a → K), ∀ i, b' i = f i := by
    rcases isEmpty_or_nonempty (Fin a) with hE | hE
    · exact ⟨Basis.empty _, fun i => isEmptyElim i⟩
    · exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), fun i => by simp⟩
  have e2 := card_isom hsU.toIsSq hsV.toIsSq
    (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq hsV.toIsSq b'
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hdiag : ∀ i j, PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j) =
        if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      rw [hb', hb']
      split_ifs with hij
      · subst hij
        rfl
      · exact hf1 i j hij
    simp only [hdiag]
  have key := e1.trans (e2.symm.trans (e3.trans e4))
  have final := card_diag (Nat.card k) hq0 hK hσr h2K hN a M haM (Fin M → K)
    (PI.VolStabS.ffH (σ : K →+* K) J) hsV (by simp)
    (fun i => PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hf2
  exact (congrArg (fun n : ℕ => (n : ℝ)) key).trans final

end PI.VolStabS.FFHS
