import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif

open Matrix Polynomial

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Node

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero`. Introduce `f hf hs hn`. Break down `hS.dv f hf hs with h | h` into its components or cases.

Simplify using `using h`. Conclude with `absurd (by simpa using h) hn`. Consider the case `succ l ih`. Introduce `f hf hs hn`. Break down `hS.dv f hf hs with h | h` into its components or cases.

Rewrite using `[pow_succ, mul_assoc]`. Conclude with `S.mul_mem (S.pow_mem hS.mem _) (S.mul_mem hS.mem h)`. Establish `hgs : star (f * ϖ⁻¹) = f * ϖ⁻¹`. Rewrite using `[star_mul', star_inv₀, hS.fix, hs]`. Establish `hgn : f * ϖ⁻¹ * (ϖ⁻¹) ^ (l + 1) ∉ S`.

Rewrite using `[mul_assoc, ← pow_succ']` and apply the resulting hypothesis. Use `ih (f * ϖ⁻¹) h hgs hgn` as an intermediate fact. Rewrite `this` using `[mul_inv, inv_inv]`. Establish `e : ϖ ^ (l + 1) * f⁻¹ = ϖ ^ l * (f⁻¹ * ϖ)` using `by ring`. Rewrite using `[e]`.

Conclude with `this`.
-/
theorem div_mem (hS : IsLocUnif S ϖ) : ∀ (l : ℕ) (f : K), f ∈ S → star f = f →
    f * (ϖ⁻¹) ^ (l + 1) ∉ S → ϖ ^ l * f⁻¹ ∈ S := by
  intro l
  induction l with
  | zero =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · simpa using h
    · exact absurd (by simpa using h) hn
  | succ l ih =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · rw [pow_succ, mul_assoc]
      exact S.mul_mem (S.pow_mem hS.mem _) (S.mul_mem hS.mem h)
    · have hgs : star (f * ϖ⁻¹) = f * ϖ⁻¹ := by
        rw [star_mul', star_inv₀, hS.fix, hs]
      have hgn : f * ϖ⁻¹ * (ϖ⁻¹) ^ (l + 1) ∉ S := by
        rwa [mul_assoc, ← pow_succ']
      have := ih (f * ϖ⁻¹) h hgs hgn
      rw [mul_inv, inv_inv] at this
      have e : ϖ ^ (l + 1) * f⁻¹ = ϖ ^ l * (f⁻¹ * ϖ) := by ring
      rw [e]
      exact this

/- English proof (translation)
Use `choose L hL using hS.arch`. Use `⟨∑ i ∈ s, L (a i), fun i hi => ?_⟩` and prove the remaining obligations. Establish `hle : L (a i) ≤ ∑ j ∈ s, L (a j)` using `Finset.single_le_sum (f := fun j => L (a j)) (fun _ _ => Nat.zero_le _) hi`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc]`. Conclude with `S.mul_mem (S.pow_mem hS.mem _) (hL _)`.
-/
theorem exists_pow (hS : IsLocUnif S ϖ) {ι : Type*} (s : Finset ι) (a : ι → K) :
    ∃ l : ℕ, ∀ i ∈ s, ϖ ^ l * a i ∈ S := by
  choose L hL using hS.arch
  refine ⟨∑ i ∈ s, L (a i), fun i hi => ?_⟩
  have hle : L (a i) ≤ ∑ j ∈ s, L (a j) :=
    Finset.single_le_sum (f := fun j => L (a j)) (fun _ _ => Nat.zero_le _) hi
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact S.mul_mem (S.pow_mem hS.mem _) (hL _)

noncomputable def pol (A B : Matrix n n K) : K[X] := det ((X : K[X]) • A.map C + B.map C)

/- English proof (translation)
Unfold `pol`. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.smul_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pol_eval (A B : Matrix n n K) (c : K) : (pol A B).eval c = det (c • A + B) := by
  unfold pol
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.smul_apply]
  ring

/- English proof (translation)
The claim follows from `Polynomial.natDegree_det_X_add_C_le A B`.
-/
theorem pol_natDegree_le (A B : Matrix n n K) : (pol A B).natDegree ≤ Fintype.card n :=
  Polynomial.natDegree_det_X_add_C_le A B

end Node

/- English proof (translation)
Take `⟨τ, hτS, hτ⟩` from `hS.tr`. Take `⟨θ, hθS, hθs, hθ0⟩` from `hS.skew`. Establish `hdetS : ∀ M : Matrix n n K, Ent S M → M.det ∈ S`. Introduce `M hM`. Establish `e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S))`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[e, ← RingHom.map_det]`. Conclude with `SetLike.coe_mem _`. Establish `hadjS : ∀ M : Matrix n n K, Ent S M → Ent S M.adjugate`.

Introduce `M hM i j`. Establish `e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S))`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[e, ← RingHom.map_adjugate]`.

Conclude with `SetLike.coe_mem _`. Establish `hnot : ϖ⁻¹ ∉ S`. Introduce `h`. Use `(hS.rad (-ϖ⁻¹) (S.neg_mem h)).1` as an intermediate fact. Apply `this` to reduce the goal to its premises.

Rewrite using `[mul_neg, mul_inv_cancel₀ hS.ne]`. Expand and normalize the polynomial expressions, which then agree. Set `N` to `Fintype.card n`. Set `s : Finset ℕ` to `Finset.range (2 * N + 1)`. Set `v : ℕ → K` to `fun k => τ + (k : K) * θ`.

Establish `hv : Set.InjOn v s`. Introduce `a _ b _ hab`. Establish `h1 : (a : K) * θ = (b : K) * θ` using `add_left_cancel hab`. Conclude with `mul_right_cancel₀ hθ0 h1` after adjusting the coercions. Establish `hvS : ∀ k, v k ∈ S` using `fun k => S.add_mem hτS (S.mul_mem (natCast_mem S k) hθS)`.

Establish `hvs : ∀ k, star (v k) = 1 - v k`. Introduce `k`. Simplify using `only [v, star_add, star_mul', star_natCast, hθs]`. Take the linear combination `hτ`. Take `⟨l, hl⟩` from `Node.exists_pow hS s (fun k => (Lagrange.basis s v k).eval 1)`.

Use `⟨l, fun X hX hd hdi => ?_⟩` and prove the remaining obligations. Set `R : K[X]` to `Node.pol (1 - X) X * Node.pol (Xᴴ - 1) 1`. Establish `hRdeg : R.degree < (s.card : WithBot ℕ)`. Establish `h1 : R.natDegree ≤ 2 * N`. Use `(Polynomial.natDegree_mul_le).trans ?_` and prove the remaining obligations.

Rewrite using `[two_mul]`. Conclude with `add_le_add (Node.pol_natDegree_le _ _) (Node.pol_natDegree_le _ _)`. Use `lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h1) ?_` and prove the remaining obligations. Simplify using `only [s, Finset.card_range]`. Conclude with `Nat.lt_succ_self _` after adjusting the coercions.

Establish `hReval : ∀ c : K, star c = 1 - c → R.eval c = (c • (1 : Matrix n n K) + star c • X).det * star ((c • (1 : Matrix n n K) + star c • X).det)`. Introduce `c hc`. Rewrite using `[Polynomial.eval_mul, Node.pol_eval, Node.pol_eval, ← Matrix.det_conjTranspose]`. Use `congr 2`. Rewrite using `[hc, smul_sub, sub_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Simplify using `only [conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_star]`. Rewrite using `[hc, smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hR1 : R.eval 1 = star X.det`.

Simplify using `only [R]`. Rewrite using `[Polynomial.eval_mul, Node.pol_eval, Node.pol_eval]`. Simplify using `[Matrix.det_conjTranspose]`. Establish `hsum : R.eval 1 = ∑ k ∈ s, R.eval (v k) * (Lagrange.basis s v k).eval 1` using `by conv_lhs => rw [Lagrange.eq_interpolate hv hRdeg]`. Rewrite using `[Lagrange.interpolate_apply, Polynomial.eval_finset_sum]`.

Simplify using `[Polynomial.eval_mul, Polynomial.eval_C]`. Establish `hX0 : X.det ≠ 0` using `hd`. Establish `hR1S : (R.eval 1)⁻¹ ∈ S`. Rewrite using `[hR1, ← star_inv₀]`. Conclude with `hS.star_mem _ hdi`.

Establish `hR10 : R.eval 1 ≠ 0`. Rewrite using `[hR1]`. Conclude with `star_ne_zero.mpr hX0`. Establish `hMS : ∀ k, Ent S (v k • (1 : Matrix n n K) + star (v k) • X)`. Introduce `k i j`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Use `S.add_mem (S.mul_mem (hvS k) ?_) (S.mul_mem (hS.star_mem _ (hvS k)) (hX i j))` and prove the remaining obligations. Use `split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`.

Establish `hex : ∃ k ∈ s, R.eval (v k) * (ϖ⁻¹) ^ (l + 1) ∉ S`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hnot` to reduce the goal to its premises. Establish `h1 : R.eval 1 * ϖ⁻¹ ∈ S`.

Establish `e : R.eval 1 * ϖ⁻¹ = ∑ k ∈ s, (R.eval (v k) * (ϖ⁻¹) ^ (l + 1)) * (ϖ ^ l * (Lagrange.basis s v k).eval 1)`. Rewrite using `[hsum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e1 : ϖ ^ l * (ϖ⁻¹) ^ (l + 1) = ϖ⁻¹`. Rewrite using `[pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS.ne, one_pow, one_mul]`.

Take the linear combination `(-(Polynomial.eval (v k) R * Polynomial.eval 1 (Lagrange.basis s v k))) * e1`. Rewrite using `[e]`. Conclude with `S.sum_mem fun k hk => S.mul_mem (hcon k hk) (hl k hk)`. Establish `e2 : ϖ⁻¹ = (R.eval 1)⁻¹ * (R.eval 1 * ϖ⁻¹)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2]`. Conclude with `S.mul_mem hR1S h1`. Take `⟨k, hk, hkn⟩` from `hex`. Use `set M := v k • (1 : Matrix n n K) + star (v k) • X with hMdef`. Establish `hfk : R.eval (v k) = M.det * star M.det` using `hReval (v k) (hvs k)`.

Establish `hfS : R.eval (v k) ∈ S`. Rewrite using `[hfk]`. Conclude with `S.mul_mem (hdetS M (hMS k)) (hS.star_mem _ (hdetS M (hMS k)))`. Establish `hfs : star (R.eval (v k)) = R.eval (v k)`. Rewrite using `[hfk, star_mul', star_star, mul_comm]`.

Establish `hf0 : R.eval (v k) ≠ 0`. Introduce `h0`. Apply `hkn` to reduce the goal to its premises. Rewrite using `[h0, zero_mul]`. Conclude with `S.zero_mem`.

Establish `hdiv` using `Node.div_mem hS l _ hfS hfs hkn`. Establish `hM0 : M.det ≠ 0`. Introduce `h0`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[hfk, h0, zero_mul]`.

Establish `hcS : ϖ ^ l * M.det⁻¹ ∈ S`. Establish `e : ϖ ^ l * M.det⁻¹ = ϖ ^ l * (R.eval (v k))⁻¹ * star M.det`. Rewrite using `[hfk]`. Establish `: star M.det ≠ 0` using `star_ne_zero.mpr hM0`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `S.mul_mem hdiv (hS.star_mem _ (hdetS M (hMS k)))`. Use `⟨v k, hvS k, by rw [hvs k]; ring, (ϖ ^ l * M.det⁻¹) • M.adjugate, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `S.mul_mem hcS (hadjS M (hMS k) i j)`. Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]`. Use `congr 1`. Rewrite using `[← hMdef]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_node [CharZero K] (hS : IsLocUnif S ϖ) (n : Type*) [Fintype n] [DecidableEq n] :
    ∃ l : ℕ, ∀ X : Matrix n n K, Ent S X → X.det ≠ 0 → X.det⁻¹ ∈ S →
      ∃ c ∈ S, c + star c = 1 ∧ ∃ W' : Matrix n n K, Ent S W' ∧
        (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K) := by
  obtain ⟨τ, hτS, hτ⟩ := hS.tr
  obtain ⟨θ, hθS, hθs, hθ0⟩ := hS.skew
  have hdetS : ∀ M : Matrix n n K, Ent S M → M.det ∈ S := by
    intro M hM
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hadjS : ∀ M : Matrix n n K, Ent S M → Ent S M.adjugate := by
    intro M hM i j
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _
  have hnot : ϖ⁻¹ ∉ S := by
    intro h
    have := (hS.rad (-ϖ⁻¹) (S.neg_mem h)).1
    apply this
    rw [mul_neg, mul_inv_cancel₀ hS.ne]
    ring
  let N := Fintype.card n
  let s : Finset ℕ := Finset.range (2 * N + 1)
  let v : ℕ → K := fun k => τ + (k : K) * θ
  have hv : Set.InjOn v s := by
    intro a _ b _ hab
    have h1 : (a : K) * θ = (b : K) * θ := add_left_cancel hab
    exact_mod_cast mul_right_cancel₀ hθ0 h1
  have hvS : ∀ k, v k ∈ S := fun k => S.add_mem hτS (S.mul_mem (natCast_mem S k) hθS)
  have hvs : ∀ k, star (v k) = 1 - v k := by
    intro k
    simp only [v, star_add, star_mul', star_natCast, hθs]
    linear_combination hτ
  obtain ⟨l, hl⟩ := Node.exists_pow hS s (fun k => (Lagrange.basis s v k).eval 1)
  refine ⟨l, fun X hX hd hdi => ?_⟩
  let R : K[X] := Node.pol (1 - X) X * Node.pol (Xᴴ - 1) 1
  have hRdeg : R.degree < (s.card : WithBot ℕ) := by
    have h1 : R.natDegree ≤ 2 * N := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [two_mul]
      exact add_le_add (Node.pol_natDegree_le _ _) (Node.pol_natDegree_le _ _)
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h1) ?_
    simp only [s, Finset.card_range]
    exact_mod_cast Nat.lt_succ_self _
  have hReval : ∀ c : K, star c = 1 - c →
      R.eval c = (c • (1 : Matrix n n K) + star c • X).det *
        star ((c • (1 : Matrix n n K) + star c • X).det) := by
    intro c hc
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval, ← Matrix.det_conjTranspose]
    congr 2
    · rw [hc, smul_sub, sub_smul, one_smul]; abel
    · simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_star]
      rw [hc, smul_sub, sub_smul, one_smul]; abel
  have hR1 : R.eval 1 = star X.det := by
    simp only [R]
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval]
    simp [Matrix.det_conjTranspose]
  have hsum : R.eval 1 = ∑ k ∈ s, R.eval (v k) * (Lagrange.basis s v k).eval 1 := by
    conv_lhs => rw [Lagrange.eq_interpolate hv hRdeg]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hX0 : X.det ≠ 0 := hd
  have hR1S : (R.eval 1)⁻¹ ∈ S := by
    rw [hR1, ← star_inv₀]
    exact hS.star_mem _ hdi
  have hR10 : R.eval 1 ≠ 0 := by
    rw [hR1]; exact star_ne_zero.mpr hX0
  have hMS : ∀ k, Ent S (v k • (1 : Matrix n n K) + star (v k) • X) := by
    intro k i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine S.add_mem (S.mul_mem (hvS k) ?_) (S.mul_mem (hS.star_mem _ (hvS k)) (hX i j))
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hex : ∃ k ∈ s, R.eval (v k) * (ϖ⁻¹) ^ (l + 1) ∉ S := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    have h1 : R.eval 1 * ϖ⁻¹ ∈ S := by
      have e : R.eval 1 * ϖ⁻¹ =
          ∑ k ∈ s, (R.eval (v k) * (ϖ⁻¹) ^ (l + 1)) * (ϖ ^ l * (Lagrange.basis s v k).eval 1) := by
        rw [hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ϖ ^ l * (ϖ⁻¹) ^ (l + 1) = ϖ⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS.ne, one_pow, one_mul]
        linear_combination (-(Polynomial.eval (v k) R * Polynomial.eval 1 (Lagrange.basis s v k))) * e1
      rw [e]
      exact S.sum_mem fun k hk => S.mul_mem (hcon k hk) (hl k hk)
    have e2 : ϖ⁻¹ = (R.eval 1)⁻¹ * (R.eval 1 * ϖ⁻¹) := by
      field_simp
    rw [e2]
    exact S.mul_mem hR1S h1
  obtain ⟨k, hk, hkn⟩ := hex
  set M := v k • (1 : Matrix n n K) + star (v k) • X with hMdef
  have hfk : R.eval (v k) = M.det * star M.det := hReval (v k) (hvs k)
  have hfS : R.eval (v k) ∈ S := by
    rw [hfk]; exact S.mul_mem (hdetS M (hMS k)) (hS.star_mem _ (hdetS M (hMS k)))
  have hfs : star (R.eval (v k)) = R.eval (v k) := by
    rw [hfk, star_mul', star_star, mul_comm]
  have hf0 : R.eval (v k) ≠ 0 := by
    intro h0; apply hkn; rw [h0, zero_mul]; exact S.zero_mem
  have hdiv := Node.div_mem hS l _ hfS hfs hkn
  have hM0 : M.det ≠ 0 := by
    intro h0; apply hf0; rw [hfk, h0, zero_mul]
  have hcS : ϖ ^ l * M.det⁻¹ ∈ S := by
    have e : ϖ ^ l * M.det⁻¹ = ϖ ^ l * (R.eval (v k))⁻¹ * star M.det := by
      rw [hfk]
      have : star M.det ≠ 0 := star_ne_zero.mpr hM0
      field_simp
    rw [e]
    exact S.mul_mem hdiv (hS.star_mem _ (hdetS M (hMS k)))
  refine ⟨v k, hvS k, by rw [hvs k]; ring, (ϖ ^ l * M.det⁻¹) • M.adjugate, ?_, ?_⟩
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hcS (hadjS M (hMS k) i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1
    rw [← hMdef]
    field_simp

end Formalism.HermitianLattices.Ext.L3.HU
