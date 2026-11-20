import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdCompMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.AdjugateCornerEqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.DiscSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.TorusTransfer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Diagz

open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools.RegFour

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh2.diagz M a ha h`.
-/
private theorem diagz {K : Type} [Field K] (M : Matrix (Fin 4) (Fin 4) K) (a : Fin 4 → K)
    (ha : Function.Injective a) (h : M.charpoly = ∏ i, (X - C (a i))) :
    ∃ P Q : Matrix (Fin 4) (Fin 4) K, P * Q = 1 ∧ Q * P = 1 ∧ Q * M * P = diagonal a :=
  _root_.UpperTheory.Reformulated.B.Qh2.diagz M a ha h

/- English proof (translation)
Use `⟨Tuple.sort (fun i => - w i), ?_⟩` and prove the remaining obligations. Establish `h1` using `Tuple.monotone_sort (fun i => - w i)`. Establish `h2 : StrictMono ((fun i => - w i) ∘ Tuple.sort (fun i => - w i))` using `h1.strictMono_of_injective ((neg_injective.comp hw).comp (Equiv.injective _))`. Introduce `i j hij`. Use `h2 hij` as an intermediate fact.

Simplify using `only [Function.comp] at this`. Simplify using `using this`.
-/
private theorem sortw {n : ℕ} (w : Fin n → ℤ) (hw : Function.Injective w) :
    ∃ π : Equiv.Perm (Fin n), StrictAnti (fun i => w (π i)) := by
  refine ⟨Tuple.sort (fun i => - w i), ?_⟩
  have h1 := Tuple.monotone_sort (fun i => - w i)
  have h2 : StrictMono ((fun i => - w i) ∘ Tuple.sort (fun i => - w i)) :=
    h1.strictMono_of_injective ((neg_injective.comp hw).comp (Equiv.injective _))
  intro i j hij
  have := h2 hij
  simp only [Function.comp] at this
  simpa using this

/- English proof (translation)
Rewrite using `[← Matrix.charpoly_reindex e.symm]`. Use `h using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[Matrix.mul_diagonal]`.
-/
private theorem sep_reindex {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 4)
    (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (h : ((x.submatrix e e).map (algebraMap K (RatFunc K)) *
      diagonal (fun i => (RatFunc.X : RatFunc K) ^ w (e i))).charpoly.Separable) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  rw [← Matrix.charpoly_reindex e.symm]
  convert h using 2
  ext i j
  simp [Matrix.mul_diagonal]

/- English proof (translation)
Take `⟨π, hπ⟩` from `sortw w hw`. Apply `sep_reindex π` to reduce the goal to its premises. Apply `UpperTheory.V.AlgebraTools.disc4 K h2 _ _ hπ` to reduce the goal to its premises. Conclude with `hx _`. Rewrite using `[Matrix.adjugate_submatrix_equiv_self]`.

Conclude with `hy _`.
-/
private theorem sepA {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (hw : Function.Injective w) (hx : ∀ i, x i i ≠ 0) (hy : ∀ i, x.adjugate i i ≠ 0) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  obtain ⟨π, hπ⟩ := sortw w hw
  apply sep_reindex π
  apply UpperTheory.V.AlgebraTools.disc4 K h2 _ _ hπ
  · exact hx _
  · rw [Matrix.adjugate_submatrix_equiv_self]
    exact hy _

/- English proof (translation)
Take `⟨p, hp⟩` from `sortw (fun i => w (e (.inl i))) (hw.comp (e.injective.comp Sum.inl_injective))`. Take `⟨q, hq⟩` from `sortw (fun i => w (e (.inr i))) (hw.comp (e.injective.comp Sum.inr_injective))`. Set `e' : Fin 2 ⊕ Fin 2 ≃ Fin 4` to `(Equiv.sumCongr p q).trans e`. Set `b : Matrix (Fin 2) (Fin 2) K` to `Matrix.of fun i j => x (e (.inl (p i))) (e (.inr (q j)))`. Set `c : Matrix (Fin 2) (Fin 2) K` to `Matrix.of fun i j => x (e (.inr (q i))) (e (.inl (p j)))`.

Establish `hx : x.submatrix e' e' = fromBlocks 0 b c 0`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [e', b, c, h11, h22]`. Establish `hdet : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det ≠ 0`. Rewrite using `[← hx, Matrix.det_submatrix_equiv_self]`. Conclude with `hd`.

Establish `hdet2 : b.det * c.det ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises. Establish `h3 : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks b 0 0 c * fromBlocks 0 1 1 0`. Simplify using `[Matrix.fromBlocks_multiply]`.

Rewrite using `[h3, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]`. Apply `sep_reindex e'` to reduce the goal to its premises. Rewrite using `[hx]`. Use `UpperTheory.V.AlgebraTools.discSwap K h2 b c _ _ hp hq (h12 _ _) (h21 _ _) (left_ne_zero_of_mul hdet2) (right_ne_zero_of_mul hdet2)` as an intermediate fact. Use `this using 4` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `ext (i | i) <;> simp [e']`.
-/
private theorem sepB {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (hw : Function.Injective w) (e : Fin 2 ⊕ Fin 2 ≃ Fin 4) (hd : x.det ≠ 0)
    (h11 : ∀ i j, x (e (.inl i)) (e (.inl j)) = 0) (h22 : ∀ i j, x (e (.inr i)) (e (.inr j)) = 0)
    (h12 : ∀ i j, x (e (.inl i)) (e (.inr j)) ≠ 0) (h21 : ∀ i j, x (e (.inr i)) (e (.inl j)) ≠ 0) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  obtain ⟨p, hp⟩ := sortw (fun i => w (e (.inl i))) (hw.comp (e.injective.comp Sum.inl_injective))
  obtain ⟨q, hq⟩ := sortw (fun i => w (e (.inr i))) (hw.comp (e.injective.comp Sum.inr_injective))
  let e' : Fin 2 ⊕ Fin 2 ≃ Fin 4 := (Equiv.sumCongr p q).trans e
  let b : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x (e (.inl (p i))) (e (.inr (q j)))
  let c : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x (e (.inr (q i))) (e (.inl (p j)))
  have hx : x.submatrix e' e' = fromBlocks 0 b c 0 := by
    ext (i | i) (j | j) <;> simp [e', b, c, h11, h22]
  have hdet : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det ≠ 0 := by
    rw [← hx, Matrix.det_submatrix_equiv_self]; exact hd
  have hdet2 : b.det * c.det ≠ 0 := by
    intro h0
    apply hdet
    have h3 : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks b 0 0 c * fromBlocks 0 1 1 0 := by
      simp [Matrix.fromBlocks_multiply]
    rw [h3, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]
  apply sep_reindex e'
  rw [hx]
  have := UpperTheory.V.AlgebraTools.discSwap K h2 b c _ _ hp hq (h12 _ _) (h21 _ _) (left_ne_zero_of_mul hdet2) (right_ne_zero_of_mul hdet2)
  convert this using 4
  ext (i | i) <;> simp [e']

/- English proof (translation)
Take `⟨i1, hi, ei⟩` from `pa i0`. Take `⟨j0, s0⟩` from `ex i0`. Take `⟨j1, hj, ej⟩` from `pa j0`. Establish `hn : ¬ E i0 j0` using `fun h => h0 (se s0 (sy h))`. Set `f : Fin 2 ⊕ Fin 2 → Fin 4` to `Sum.elim ![i0, i1] ![j0, j1]`.

Establish `fl : ∀ a, E i0 (f (.inl a))`. Introduce `a`. Use `fin_cases a`. Conclude with `rf _`. Conclude with `ei`.

Establish `fr : ∀ a, E j0 (f (.inr a))`. Introduce `a`. Use `fin_cases a`. Conclude with `rf _`. Conclude with `ej`.

Establish `hlr : ∀ a b, f (.inl a) ≠ f (.inr b)`. Introduce `a b h`. Conclude with `hn (tr (fl a) (h ▸ sy (fr b)))`. Establish `finj : Function.Injective f`. Introduce and unpack `(a | a) (b | b) h`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [f]`. Conclude with `absurd h (hlr _ _)`. Conclude with `absurd h.symm (hlr _ _)`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [f]`. Establish `fbij : Function.Bijective f` using `(Fintype.bijective_iff_injective_and_card f).2 ⟨finj, by simp⟩`.

Establish `hrr : ∀ a b, ¬ S (f (.inr a)) (f (.inr b))` using `fun a b h => hn (ss s0 (se (es (fr a) h) (sy (fr b))))`. Use `⟨Equiv.ofBijective f fbij, fun a b h => h0 (se (es (fl a) h) (sy (fl b))), hrr, fun a b => se (es (sy (fl a)) s0) (fr b), fun a b => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `ex (f (.inr a))`. Take `⟨c | c, rfl⟩` from `fbij.2 k`. Conclude with `se hk (tr (sy (fl c)) (fl b))`.

Conclude with `absurd hk (hrr _ _)`.
-/
private theorem comb (E S : Fin 4 → Fin 4 → Prop) (rf : ∀ i, E i i) (sy : ∀ {i j}, E i j → E j i)
    (tr : ∀ {i j k}, E i j → E j k → E i k)
    (se : ∀ {i j k}, S i j → E j k → S i k) (es : ∀ {i j k}, E i j → S j k → S i k)
    (ss : ∀ {i j k}, S i k → S j k → E i j) (ex : ∀ i, ∃ j, S i j) (pa : ∀ i, ∃ j, j ≠ i ∧ E i j)
    (i0 : Fin 4) (h0 : ¬ S i0 i0) :
    ∃ e : Fin 2 ⊕ Fin 2 ≃ Fin 4, (∀ i j, ¬ S (e (.inl i)) (e (.inl j))) ∧ (∀ i j, ¬ S (e (.inr i)) (e (.inr j))) ∧
      (∀ i j, S (e (.inl i)) (e (.inr j))) ∧ (∀ i j, S (e (.inr i)) (e (.inl j))) := by
  obtain ⟨i1, hi, ei⟩ := pa i0
  obtain ⟨j0, s0⟩ := ex i0
  obtain ⟨j1, hj, ej⟩ := pa j0
  have hn : ¬ E i0 j0 := fun h => h0 (se s0 (sy h))
  let f : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![i0, i1] ![j0, j1]
  have fl : ∀ a, E i0 (f (.inl a)) := by
    intro a; fin_cases a
    · exact rf _
    · exact ei
  have fr : ∀ a, E j0 (f (.inr a)) := by
    intro a; fin_cases a
    · exact rf _
    · exact ej
  have hlr : ∀ a b, f (.inl a) ≠ f (.inr b) := by
    intro a b h
    exact hn (tr (fl a) (h ▸ sy (fr b)))
  have finj : Function.Injective f := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all [f]
    · exact absurd h (hlr _ _)
    · exact absurd h.symm (hlr _ _)
    · fin_cases a <;> fin_cases b <;> simp_all [f]
  have fbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨finj, by simp⟩
  have hrr : ∀ a b, ¬ S (f (.inr a)) (f (.inr b)) := fun a b h =>
    hn (ss s0 (se (es (fr a) h) (sy (fr b))))
  refine ⟨Equiv.ofBijective f fbij, fun a b h => h0 (se (es (fl a) h) (sy (fl b))), hrr,
    fun a b => se (es (sy (fl a)) s0) (fr b), fun a b => ?_⟩
  obtain ⟨k, hk⟩ := ex (f (.inr a))
  obtain ⟨c | c, rfl⟩ := fbij.2 k
  · exact se hk (tr (sy (fl c)) (fl b))
  · exact absurd hk (hrr _ _)

private def Rel {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (N : Subgroup G)
    (g : G) (i j : Fin 4) : Prop := ∃ n ∈ N, r (g * n) i j ≠ 0

section
variable {K G : Type} [Field K] [Group G] {r : G →* Matrix (Fin 4) (Fin 4) K} {N : Subgroup G}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, N.one_mem, by simpa using h⟩`.
-/
private theorem rel_of (g : G) {i j : Fin 4} (h : r g i j ≠ 0) : Rel r N g i j :=
  ⟨1, N.one_mem, by simpa using h⟩

/- English proof (translation)
Take `⟨n, hn, h1⟩` from `h1`. Take `⟨n', hn', h2⟩` from `h2`. Assume the negation of the conclusion as `hc`. Establish `h3 : (fun l => r (g * n) i l * r (h * n') l k) = 0`. Apply `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hd` to reduce the goal to its premises.

Introduce `m`. Assume the negation of the conclusion as `h4`. Apply `hc` to reduce the goal to its premises. Use `⟨h⁻¹ * (n * t ^ (m : ℕ)) * h * n', N.mul_mem (hN.conj_mem' _ (N.mul_mem hn (N.pow_mem ht _)) _) hn', ?_⟩` and prove the remaining obligations. Establish `h5 : g * h * (h⁻¹ * (n * t ^ (m : ℕ)) * h * n') = g * n * t ^ (m : ℕ) * (h * n')` using `by group`.

Rewrite using `[h5, map_mul r _ (h * n'), map_mul r (g * n), map_pow, htd, Matrix.diagonal_pow, Matrix.mul_apply]`. Use `h4 using 2 with l` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.mul_diagonal, Pi.pow_apply]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_ne_zero h1 h2 (congrFun h3 j)`.
-/
private theorem rel_comp [hN : N.Normal] {t : G} (ht : t ∈ N) {d : Fin 4 → K} (hd : Function.Injective d)
    (htd : r t = diagonal d) {g h : G} {i j k : Fin 4} (h1 : Rel r N g i j) (h2 : Rel r N h j k) :
    Rel r N (g * h) i k := by
  obtain ⟨n, hn, h1⟩ := h1
  obtain ⟨n', hn', h2⟩ := h2
  by_contra hc
  have h3 : (fun l => r (g * n) i l * r (h * n') l k) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hd
    intro m
    by_contra h4
    apply hc
    refine ⟨h⁻¹ * (n * t ^ (m : ℕ)) * h * n', N.mul_mem (hN.conj_mem' _ (N.mul_mem hn (N.pow_mem ht _)) _) hn', ?_⟩
    have h5 : g * h * (h⁻¹ * (n * t ^ (m : ℕ)) * h * n') = g * n * t ^ (m : ℕ) * (h * n') := by group
    rw [h5, map_mul r _ (h * n'), map_mul r (g * n), map_pow, htd, Matrix.diagonal_pow, Matrix.mul_apply]
    convert h4 using 2 with l
    rw [Matrix.mul_diagonal, Pi.pow_apply]; ring
  exact mul_ne_zero h1 h2 (congrFun h3 j)

/- English proof (translation)
Take `⟨n, hn, h1⟩` from `h1`. Use `⟨g⁻¹ * h * n, N.mul_mem hgh hn, ?_⟩` and prove the remaining obligations. Rewrite using `[show g * (g⁻¹ * h * n) = h * n by group]` and apply the resulting hypothesis.
-/
private theorem rel_congr {g h : G} (hgh : g⁻¹ * h ∈ N) {i j : Fin 4} (h1 : Rel r N h i j) : Rel r N g i j := by
  obtain ⟨n, hn, h1⟩ := h1
  refine ⟨g⁻¹ * h * n, N.mul_mem hgh hn, ?_⟩
  rwa [show g * (g⁻¹ * h * n) = h * n by group]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1 : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => obtain ⟨g, rfl⟩ := hx`. Conclude with `hc g`. Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul a x _ hx => simp [hx]`.

Use `h1 (Matrix.of fun _ _ => 1) (hs ▸ Submodule.mem_top)` as an intermediate fact. Simplify using `at this`.
-/
private theorem rel_span (hs : Submodule.span K (Set.range r) = ⊤) (i j : Fin 4) : ∃ g, r g i j ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hc g
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := h1 (Matrix.of fun _ _ => 1) (hs ▸ Submodule.mem_top)
  simp at this

/- English proof (translation)
Establish `h1 : (r g * r g⁻¹) i i ≠ 0` using `by rw [← map_mul]; simp`. Rewrite `h1` using `[Matrix.mul_apply]`. Take `⟨j, -, hj⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h1`. Conclude with `⟨j, left_ne_zero_of_mul hj, right_ne_zero_of_mul hj⟩`.
-/
private theorem rel_ex (g : G) (i : Fin 4) : ∃ j, r g i j ≠ 0 ∧ r g⁻¹ j i ≠ 0 := by
  have h1 : (r g * r g⁻¹) i i ≠ 0 := by rw [← map_mul]; simp
  rw [Matrix.mul_apply] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨j, left_ne_zero_of_mul hj, right_ne_zero_of_mul hj⟩

/- English proof (translation)
Take `⟨h, hh⟩` from `rel_span hs j i`. Establish `h2 : Rel r N h j i` using `rel_of h hh`. Establish `h3 : Rel r N (g * h) i i` using `rel_comp ht hd htd h1 h2`. Establish `h4 : ∀ m : ℕ, Rel r N (h * (g * h) ^ m) j i`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simpa using h2`. Consider the case `succ m ih => rw [pow_succ, ← mul_assoc]`. Conclude with `rel_comp ht hd htd ih h3`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))`.

Use `rel_congr ?_ (h4 m)` and prove the remaining obligations. Use `N.pow_index_mem (g * h)` as an intermediate fact. Rewrite `this` using `[hm, pow_succ']`. Rewrite using `[inv_inv, ← mul_assoc]` and apply the resulting hypothesis.
-/
private theorem rel_symm [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    {g : G} {i j : Fin 4} (h1 : Rel r N g i j) : Rel r N g⁻¹ j i := by
  obtain ⟨h, hh⟩ := rel_span hs j i
  have h2 : Rel r N h j i := rel_of h hh
  have h3 : Rel r N (g * h) i i := rel_comp ht hd htd h1 h2
  have h4 : ∀ m : ℕ, Rel r N (h * (g * h) ^ m) j i := by
    intro m
    induction m with
    | zero => simpa using h2
    | succ m ih => rw [pow_succ, ← mul_assoc]; exact rel_comp ht hd htd ih h3
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
  refine rel_congr ?_ (h4 m)
  have := N.pow_index_mem (g * h)
  rw [hm, pow_succ'] at this
  rwa [inv_inv, ← mul_assoc]

/- English proof (translation)
Establish `h0 : ∃ j k, j ≠ k ∧ Rel r N 1 j k`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hdiag : ∀ n ∈ N, r n = diagonal (fun i => r n i i)`. Introduce `n hn`.

Use extensionality with `j k`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hjk]`.

Assume the negation of the conclusion as `h1`. Conclude with `h j k hjk ⟨n, hn, by simpa using h1⟩`. Take `⟨g, hg, g', hg', hne⟩` from `hc`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hdiag g hg, hdiag g' hg', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`.

Simplify using `only [mul_comm]`. Take `⟨j, k, hjk, hE⟩` from `h0`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨g, hg⟩` from `rel_span hs j i`.

Establish `hj : Rel r N g j i` using `rel_of g hg`. Establish `hk : Rel r N g k i`. Use `rel_comp ht hd htd (rel_symm ht hd htd hs hE) hj` as an intermediate fact. Simplify using `using this`. Establish `key : ∀ a, Rel r N g a i → ∀ l, r g a l ≠ 0 → l = i`.

Introduce `a ha l hl`. Assume the negation of the conclusion as `hli`. Use `rel_comp ht hd htd (rel_symm ht hd htd hs ha) (rel_of (N := N) g hl)` as an intermediate fact. Conclude with `h l hli (by simpa using this)`. Take `⟨l, hl1, hl2⟩` from `rel_ex (r := r) g k`.

Establish `hli` using `key k hk l hl1`. Substitute `hli` using the available equality. Establish `h1 : (r g * r g⁻¹) j k = 0` using `by rw [← map_mul]; simp [hjk]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single l]`. Conclude with `mul_ne_zero hg hl2 h1`.

Introduce `b _ hb`. Establish `: r g j b = 0`. Assume the negation of the conclusion as `h2`. Conclude with `hb (key j hj b h2)`. Rewrite using `[this, zero_mul]`.

Simplify using the standard rewrite rules.
-/
private theorem rel_partner [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    (hc : ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) (i : Fin 4) : ∃ j, j ≠ i ∧ Rel r N 1 i j := by
  have h0 : ∃ j k, j ≠ k ∧ Rel r N 1 j k := by
    by_contra h
    push Not at h
    have hdiag : ∀ n ∈ N, r n = diagonal (fun i => r n i i) := by
      intro n hn
      ext j k
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Matrix.diagonal_apply_ne _ hjk]
        by_contra h1
        exact h j k hjk ⟨n, hn, by simpa using h1⟩
    obtain ⟨g, hg, g', hg', hne⟩ := hc
    apply hne
    rw [hdiag g hg, hdiag g' hg', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  obtain ⟨j, k, hjk, hE⟩ := h0
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := rel_span hs j i
  have hj : Rel r N g j i := rel_of g hg
  have hk : Rel r N g k i := by
    have := rel_comp ht hd htd (rel_symm ht hd htd hs hE) hj
    simpa using this
  have key : ∀ a, Rel r N g a i → ∀ l, r g a l ≠ 0 → l = i := by
    intro a ha l hl
    by_contra hli
    have := rel_comp ht hd htd (rel_symm ht hd htd hs ha) (rel_of (N := N) g hl)
    exact h l hli (by simpa using this)
  obtain ⟨l, hl1, hl2⟩ := rel_ex (r := r) g k
  have hli := key k hk l hl1
  subst hli
  have h1 : (r g * r g⁻¹) j k = 0 := by rw [← map_mul]; simp [hjk]
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact mul_ne_zero hg hl2 h1
  · intro b _ hb
    have : r g j b = 0 := by
      by_contra h2
      exact hb (key j hj b h2)
    rw [this, zero_mul]
  · simp

/- English proof (translation)
Distinguish the cases in `h : ∀ i, Rel r N σ i i`. Conclude with `Or.inl h`. Use `push Not at h`. Take `⟨i0, h0⟩` from `h`. Use `Or.inr (comb (Rel r N 1) (Rel r N σ) (fun i => rel_of 1 (by simp)) ?_ ?_ ?_ ?_ ?_ ?_ (rel_partner ht hd htd hs hc) i0 h0)` and prove the remaining obligations.

Introduce `i j h`. Simplify using `using rel_symm ht hd htd hs h`. Introduce `i j k h h'`. Simplify using `using rel_comp ht hd htd h h'`. Introduce `i j k h h'`.

Simplify using `using rel_comp ht hd htd h h'`. Introduce `i j k h h'`. Simplify using `using rel_comp ht hd htd h h'`. Introduce `i j k h h'`. Simplify using `using rel_comp ht hd htd h (rel_symm ht hd htd hs h')`.

Introduce `i`. Take `⟨j, hj, -⟩` from `rel_ex (r := r) σ i`. Conclude with `⟨j, rel_of σ hj⟩`.
-/
private theorem rel_cases [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    (hc : ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) (σ : G) :
    (∀ i, Rel r N σ i i) ∨ ∃ e : Fin 2 ⊕ Fin 2 ≃ Fin 4,
      (∀ i j, ¬ Rel r N σ (e (.inl i)) (e (.inl j))) ∧ (∀ i j, ¬ Rel r N σ (e (.inr i)) (e (.inr j))) ∧
      (∀ i j, Rel r N σ (e (.inl i)) (e (.inr j))) ∧ (∀ i j, Rel r N σ (e (.inr i)) (e (.inl j))) := by
  by_cases h : ∀ i, Rel r N σ i i
  · exact Or.inl h
  push Not at h
  obtain ⟨i0, h0⟩ := h
  refine Or.inr (comb (Rel r N 1) (Rel r N σ) (fun i => rel_of 1 (by simp)) ?_ ?_ ?_ ?_ ?_ ?_
    (rel_partner ht hd htd hs hc) i0 h0)
  · intro i j h; simpa using rel_symm ht hd htd hs h
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h (rel_symm ht hd htd hs h')
  · intro i
    obtain ⟨j, hj, -⟩ := rel_ex (r := r) σ i
    exact ⟨j, rel_of σ hj⟩

end

/- English proof (translation)
Establish `h : (r g).det * (r g⁻¹).det = 1` using `by rw [← Matrix.det_mul, ← map_mul]; simp`. Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
private theorem det_ne {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (g : G) :
    (r g).det ≠ 0 := by
  have h : (r g).det * (r g⁻¹).det = 1 := by rw [← Matrix.det_mul, ← map_mul]; simp
  exact left_ne_zero_of_mul_eq_one h

/- English proof (translation)
Establish `h : r g * r g⁻¹ = 1` using `by rw [← map_mul]; simp`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem adj_eq {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (g : G) :
    (r g).adjugate = (r g).det • r g⁻¹ := by
  have h : r g * r g⁻¹ = 1 := by rw [← map_mul]; simp
  calc (r g).adjugate = (r g).adjugate * (r g * r g⁻¹) := by rw [h, Matrix.mul_one]
    _ = (r g).det • r g⁻¹ := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul]; simp

/- English proof (translation)
Establish `h` using `congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin 4 × Fin 4 => x p.1 p.2)) (Matrix.mvPolynomialX (Fin 4) (Fin 4) K)) i) i`. Rewrite `h` using `[Matrix.mvPolynomialX_mapMatrix_eval]`. Conclude with `h`.
-/
private theorem eval_adj {K : Type} [Field K] (x : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    MvPolynomial.eval (fun p : Fin 4 × Fin 4 => x p.1 p.2)
      ((Matrix.mvPolynomialX (Fin 4) (Fin 4) K).adjugate i i) = x.adjugate i i := by
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin 4 × Fin 4 => x p.1 p.2))
    (Matrix.mvPolynomialX (Fin 4) (Fin 4) K)) i) i
  rw [Matrix.mvPolynomialX_mapMatrix_eval] at h
  exact h

/- English proof (translation)
Take `⟨N, hN, hNf, ⟨I, hI⟩, hirr⟩` from `UpperTheory.V.AlgebraTools.idCompMat K G (Fin 4) r`. Establish `hclosed : IsClosed (N : Set G)`. Establish `: (N : Set G) = ⋂ f ∈ I, {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0}`. Use extensionality with `g`. Simplify using `[hI]`.

Rewrite using `[this]`. Conclude with `isClosed_biInter fun f _ => hcl f`. Establish `hcN` using `hc N (N.isOpen_of_isClosed_of_finiteIndex hclosed) hN hNf`. Take `⟨k, hk0, -, hk⟩` from `(U ⊓ N).exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero u`. Establish `hb : ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i ^ k / a j ^ k)`.

Introduce `i j hij h`. Rewrite `h` using `[← div_pow]`. Conclude with `ha i j hij (h.of_pow hk0.ne')`. Establish `hd : Function.Injective fun i => ((a i ^ k : Kˣ) : K)`. Introduce `i j hij`.

Assume the negation of the conclusion as `h`. Apply `hb i j h` to reduce the goal to its premises. Rewrite using `[Units.ext hij, div_self']`. Conclude with `IsOfFinOrder.one`. Establish `htd : r (u ^ k) = diagonal fun i => ((a i ^ k : Kˣ) : K)`.

Rewrite using `[map_pow, hu, Matrix.diagonal_pow]`. Use `congr 1`. Take `⟨w, hw, hwr⟩` from `UpperTheory.V.AlgebraTools.relWeight Kˣ (Fin 4) (fun i => a i ^ k) hb`. Establish `main : ∃ g ∈ U, ((r (σ * g)).map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable`. Break down `rel_cases hk.2 hd htd hs hcN σ with h | ⟨e, h11, h22, h12, h21⟩` into its components or cases.

Take `⟨g, hg, hf⟩` from `hirr U hU σ (Finset.univ.image (fun i : Fin 4 => MvPolynomial.X (i, i)) ∪ Finset.univ.image (fun i : Fin 4 => (Matrix.mvPolynomialX (Fin 4) (Fin 4) K).adjugate i i)) (by`. Introduce `f hf`. Simplify using `only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf`. Break down `hf with ⟨i, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Take `⟨n, hn, h1⟩` from `h i`.

Conclude with `⟨n, hn, by simpa using h1⟩`. Take `⟨n, hn, h1⟩` from `rel_symm hk.2 hd htd hs (h i)`. Use `⟨σ⁻¹ * n⁻¹ * σ, hN.conj_mem' _ (N.inv_mem hn) σ, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_adj, adj_eq, show (σ * (σ⁻¹ * n⁻¹ * σ))⁻¹ = σ⁻¹ * n by group]`. Conclude with `mul_ne_zero (det_ne r _) h1)`.

Use `⟨g, hg.1, sepA h2 _ w hw (fun i => ?_) (fun i => ?_)⟩` and prove the remaining obligations. Simplify using `using hf (MvPolynomial.X (i, i)) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Rewrite using `[← eval_adj]`. Conclude with `hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Take `⟨g, hg, hf⟩` from `hirr U hU σ ((Finset.univ.filter fun p : Fin 4 × Fin 4 => Rel r N σ p.1 p.2).image MvPolynomial.X) (by`.

Introduce `f hf`. Simplify using `only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hf`. Take `⟨p, ⟨n, hn, h1⟩, rfl⟩` from `hf`. Conclude with `⟨n, hn, by simpa using h1⟩)`. Establish `hf' : ∀ i j, Rel r N σ i j → r (σ * g) i j ≠ 0` using `fun i j hij => by`.

Simplify `hij))` using `using hf (MvPolynomial.X (i, j)) (Finset.mem_image_of_mem _ (by simpa`. Establish `hf'' : ∀ i j, ¬ Rel r N σ i j → r (σ * g) i j = 0` using `fun i j hij => by`. Assume the negation of the conclusion as `h`. Conclude with `hij ⟨g, hg.2, h⟩`. Conclude with `⟨g, hg.1, sepB h2 _ w hw e (det_ne r _) (fun i j => hf'' _ _ (h11 i j)) (fun i j => hf'' _ _ (h22 i j)) (fun i j => hf' _ _ (h12 i j)) (fun i j => hf' _ _ (h21 i j))⟩`.

Take `⟨g, hg, hsep⟩` from `main`. Take `⟨m, hm⟩` from `UpperTheory.V.AlgebraTools.torusTransfer K (Fin 4) _ (fun i => a i ^ k) w hwr hsep`. Use `⟨g * (u ^ k) ^ m, U.mul_mem hg (U.pow_mem hk.1 m), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, map_mul, map_pow, htd, Matrix.diagonal_pow]`. Conclude with `hm`.
-/
private theorem core (K G : Type) [Field K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h2 : (2 : K) ≠ 0)
    (r : G →* Matrix (Fin 4) (Fin 4) K)
    (hcl : ∀ f : MvPolynomial (Fin 4 × Fin 4) K, IsClosed {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0})
    (hs : Submodule.span K (Set.range r) = ⊤) (u : G) (a : Fin 4 → Kˣ) (hu : r u = diagonal fun i => (a i : K))
    (ha : ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j))
    (hc : ∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g)
    (U : Subgroup G) (hU : U.FiniteIndex) (σ : G) : ∃ g ∈ U, (r (σ * g)).charpoly.Separable := by
  classical
  obtain ⟨N, hN, hNf, ⟨I, hI⟩, hirr⟩ := UpperTheory.V.AlgebraTools.idCompMat K G (Fin 4) r
  have hclosed : IsClosed (N : Set G) := by
    have : (N : Set G) = ⋂ f ∈ I, {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0} := by
      ext g; simp [hI]
    rw [this]
    exact isClosed_biInter fun f _ => hcl f
  have hcN := hc N (N.isOpen_of_isClosed_of_finiteIndex hclosed) hN hNf
  obtain ⟨k, hk0, -, hk⟩ := (U ⊓ N).exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero u
  have hb : ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i ^ k / a j ^ k) := by
    intro i j hij h
    rw [← div_pow] at h
    exact ha i j hij (h.of_pow hk0.ne')
  have hd : Function.Injective fun i => ((a i ^ k : Kˣ) : K) := by
    intro i j hij
    by_contra h
    apply hb i j h
    rw [Units.ext hij, div_self']
    exact IsOfFinOrder.one
  have htd : r (u ^ k) = diagonal fun i => ((a i ^ k : Kˣ) : K) := by
    rw [map_pow, hu, Matrix.diagonal_pow]; congr 1
  obtain ⟨w, hw, hwr⟩ := UpperTheory.V.AlgebraTools.relWeight Kˣ (Fin 4) (fun i => a i ^ k) hb
  have main : ∃ g ∈ U, ((r (σ * g)).map (algebraMap K (RatFunc K)) *
      diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
    rcases rel_cases hk.2 hd htd hs hcN σ with h | ⟨e, h11, h22, h12, h21⟩
    · obtain ⟨g, hg, hf⟩ := hirr U hU σ
        (Finset.univ.image (fun i : Fin 4 => MvPolynomial.X (i, i)) ∪
          Finset.univ.image (fun i : Fin 4 => (Matrix.mvPolynomialX (Fin 4) (Fin 4) K).adjugate i i)) (by
        intro f hf
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · obtain ⟨n, hn, h1⟩ := h i
          exact ⟨n, hn, by simpa using h1⟩
        · obtain ⟨n, hn, h1⟩ := rel_symm hk.2 hd htd hs (h i)
          refine ⟨σ⁻¹ * n⁻¹ * σ, hN.conj_mem' _ (N.inv_mem hn) σ, ?_⟩
          rw [eval_adj, adj_eq, show (σ * (σ⁻¹ * n⁻¹ * σ))⁻¹ = σ⁻¹ * n by group]
          exact mul_ne_zero (det_ne r _) h1)
      refine ⟨g, hg.1, sepA h2 _ w hw (fun i => ?_) (fun i => ?_)⟩
      · simpa using hf (MvPolynomial.X (i, i))
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      · rw [← eval_adj]
        exact hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · obtain ⟨g, hg, hf⟩ := hirr U hU σ
        ((Finset.univ.filter fun p : Fin 4 × Fin 4 => Rel r N σ p.1 p.2).image MvPolynomial.X) (by
        intro f hf
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨p, ⟨n, hn, h1⟩, rfl⟩ := hf
        exact ⟨n, hn, by simpa using h1⟩)
      have hf' : ∀ i j, Rel r N σ i j → r (σ * g) i j ≠ 0 := fun i j hij => by
        simpa using hf (MvPolynomial.X (i, j)) (Finset.mem_image_of_mem _ (by simpa using hij))
      have hf'' : ∀ i j, ¬ Rel r N σ i j → r (σ * g) i j = 0 := fun i j hij => by
        by_contra h; exact hij ⟨g, hg.2, h⟩
      exact ⟨g, hg.1, sepB h2 _ w hw e (det_ne r _) (fun i j => hf'' _ _ (h11 i j)) (fun i j => hf'' _ _ (h22 i j))
        (fun i j => hf' _ _ (h12 i j)) (fun i j => hf' _ _ (h21 i j))⟩
  obtain ⟨g, hg, hsep⟩ := main
  obtain ⟨m, hm⟩ := UpperTheory.V.AlgebraTools.torusTransfer K (Fin 4) _ (fun i => a i ^ k) w hwr hsep
  refine ⟨g * (u ^ k) ^ m, U.mul_mem hg (U.pow_mem hk.1 m), ?_⟩
  rw [← mul_assoc, map_mul, map_pow, htd, Matrix.diagonal_pow]
  exact hm

end UpperTheory.V.AlgebraTools.RegFour

/- English proof (translation)
Introduce `K G _ _ _ _ _ h2 r hcl hs ⟨u, a, hu, ha⟩ hc U hU σ`. Establish `hinj : Function.Injective fun i => (a i : K)`. Introduce `i j hij`. Assume the negation of the conclusion as `h`. Apply `ha i j h` to reduce the goal to its premises.

Rewrite using `[Units.ext hij, div_self']`. Conclude with `IsOfFinOrder.one`. Take `⟨P, Q, hPQ, hQP, hD⟩` from `RegFour.diagz (r u) _ hinj hu`. Establish `hmul : ∀ x y : Matrix (Fin 4) (Fin 4) K, Q * (x * y) * P = Q * x * P * (Q * y * P)`. Introduce `x y`.

Combine the equalities or inequalities in the displayed calculation. Establish `hback : ∀ x : Matrix (Fin 4) (Fin 4) K, P * (Q * x * P) * Q = x`. Introduce `x`. Combine the equalities or inequalities in the displayed calculation. Set `r' : G →* Matrix (Fin 4) (Fin 4) K` to `{ toFun := fun g => Q * r g * P map_one' := by simp [hQP] map_mul' := fun g h => by rw [map_mul, hmul] }`.

Establish `hr' : ∀ g, r' g = Q * r g * P` using `fun _ => rfl`. Use `Exists.imp ?_ (RegFour.core K G h2 r' ?_ ?_ u a hD ha ?_ U hU σ)` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hsep⟩`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Rewrite `hsep` using `[hr', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]`. Then use the resulting hypothesis.

Introduce `f`. Use `hcl (MvPolynomial.bind₁ (fun p : Fin 4 × Fin 4 => ∑ l, (∑ k, MvPolynomial.C (Q p.1 k) * MvPolynomial.X (k, l)) * MvPolynomial.C (P l p.2)) f) using 4 with g` and compare the differences between its conclusion and the goal. Rewrite using `[← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]`. Simplify using `only [RingHom.coe_coe, MvPolynomial.aeval_bind₁]`. Use `congr 2`.

Use function extensionality and compare the values at `p`. Simplify using `[hr', Matrix.mul_apply]`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : ∀ y ∈ Submodule.span K (Set.range r), Q * y * P ∈ Submodule.span K (Set.range r')`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨g, rfl⟩ := hy`. Conclude with `Submodule.subset_span ⟨g, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [Matrix.mul_add, Matrix.add_mul]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `Submodule.smul_mem _ c hy`. Establish `h3` using `h1 (P * x * Q) (hs ▸ Submodule.mem_top)`.

Rewrite `h3` using `[show Q * (P * x * Q) * P = (Q * P) * x * (Q * P) by simp only [Matrix.mul_assoc], hQP, Matrix.one_mul, Matrix.mul_one]`. Then use the resulting hypothesis. Introduce `N h1 h3 h4`. Take `⟨g, hg, h, hh, hne⟩` from `hc N h1 h3 h4`. Use `⟨g, hg, h, hh, fun h5 => hne ?_⟩` and prove the remaining obligations. Rewrite `h5` using `[hr', hr', ← hmul, ← hmul]`.

Rewrite using `[← hback (r g * r h), h5, hback]`.
-/
theorem UpperTheory.V.AlgebraTools.regCosetFour :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (2 : K) ≠ 0 →
      ∀ (r : G →* Matrix (Fin 4) (Fin 4) K),
      (∀ f : MvPolynomial (Fin 4 × Fin 4) K, IsClosed {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0}) →
      Submodule.span K (Set.range r) = ⊤ →
      (∃ (u : G) (a : Fin 4 → Kˣ), (r u).charpoly = ∏ i, (X - C (a i : K)) ∧ ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      (∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) →
      ∀ U : Subgroup G, U.FiniteIndex → ∀ σ : G, ∃ g ∈ U, (r (σ * g)).charpoly.Separable := by
  intro K G _ _ _ _ _ h2 r hcl hs ⟨u, a, hu, ha⟩ hc U hU σ
  have hinj : Function.Injective fun i => (a i : K) := by
    intro i j hij
    by_contra h
    apply ha i j h
    rw [Units.ext hij, div_self']
    exact IsOfFinOrder.one
  obtain ⟨P, Q, hPQ, hQP, hD⟩ := RegFour.diagz (r u) _ hinj hu
  have hmul : ∀ x y : Matrix (Fin 4) (Fin 4) K, Q * (x * y) * P = Q * x * P * (Q * y * P) := by
    intro x y
    calc Q * (x * y) * P = Q * x * (P * Q) * y * P := by rw [hPQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hback : ∀ x : Matrix (Fin 4) (Fin 4) K, P * (Q * x * P) * Q = x := by
    intro x
    calc P * (Q * x * P) * Q = (P * Q) * x * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPQ]; simp
  let r' : G →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun g => Q * r g * P
      map_one' := by simp [hQP]
      map_mul' := fun g h => by rw [map_mul, hmul] }
  have hr' : ∀ g, r' g = Q * r g * P := fun _ => rfl
  refine Exists.imp ?_ (RegFour.core K G h2 r' ?_ ?_ u a hD ha ?_ U hU σ)
  · rintro g ⟨hg, hsep⟩
    refine ⟨hg, ?_⟩
    rwa [hr', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPQ, Matrix.one_mul] at hsep
  · intro f
    convert hcl (MvPolynomial.bind₁ (fun p : Fin 4 × Fin 4 =>
      ∑ l, (∑ k, MvPolynomial.C (Q p.1 k) * MvPolynomial.X (k, l)) * MvPolynomial.C (P l p.2)) f) using 4 with g
    rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    simp only [RingHom.coe_coe, MvPolynomial.aeval_bind₁]
    congr 2
    funext p
    simp [hr', Matrix.mul_apply]
  · rw [eq_top_iff]
    intro x _
    have h1 : ∀ y ∈ Submodule.span K (Set.range r), Q * y * P ∈ Submodule.span K (Set.range r') := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨g, rfl⟩ := hy; exact Submodule.subset_span ⟨g, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hy
    have h3 := h1 (P * x * Q) (hs ▸ Submodule.mem_top)
    rwa [show Q * (P * x * Q) * P = (Q * P) * x * (Q * P) by simp only [Matrix.mul_assoc], hQP,
      Matrix.one_mul, Matrix.mul_one] at h3
  · intro N h1 h3 h4
    obtain ⟨g, hg, h, hh, hne⟩ := hc N h1 h3 h4
    refine ⟨g, hg, h, hh, fun h5 => hne ?_⟩
    rw [hr', hr', ← hmul, ← hmul] at h5
    rw [← hback (r g * r h), h5, hback]
