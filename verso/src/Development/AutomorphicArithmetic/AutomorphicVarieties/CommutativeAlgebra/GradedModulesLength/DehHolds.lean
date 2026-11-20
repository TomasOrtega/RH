import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Introduce `O A _ _ _ 𝒜 _ I hI d w f h hd hf hh hmem`. Take `⟨i, hi, y, hy, hsum⟩` from `Submodule.mem_sup.mp hmem`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Use `set c : ℤ → A := fun j => (DirectSum.decompose 𝒜 u j : A) with hc`. Establish `hcomp : ∀ j : ℤ, (DirectSum.decompose 𝒜 h (j + d) : A) - c j * f + c (j + d) ∈ I`.

Introduce `j`. Establish `h1 : (DirectSum.decompose 𝒜 i (j + d) : A) ∈ I` using `hI (j + d) hi`. Establish `h2 : i = h - u * f + u` using `by rw [← hsum]; ring`. Establish `h3 : (DirectSum.decompose 𝒜 (u * f) (j + d) : A) = c j * f` using `DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hf`. Rewrite `h1` using `[h2, DirectSum.decompose_add, DirectSum.decompose_sub, DirectSum.add_apply, DirectSum.sub_apply, Submodule.coe_add, Submodule.coe_sub, h3]`.

Conclude with `h1`. Set `q` to `Ideal.Quotient.mk I`. Establish `hne : ∀ j : ℤ, j + d ≠ w → q (c (j + d)) = q (c j) * q f`. Introduce `j hj`. Establish `h1` using `hcomp j`.

Rewrite `h1` using `[DirectSum.decompose_of_mem_ne 𝒜 hh (Ne.symm hj)]`. Establish `h2` using `(Ideal.Quotient.eq_zero_iff_mem).mpr h1`. Simplify using `only [map_add, map_sub, map_mul, map_zero] at h2`. Take the linear combination `h2`. Establish `heq : q (c w) = q (c (w - d)) * q f - q h`.

Establish `h1` using `hcomp (w - d)`. Rewrite `h1` using `[sub_add_cancel, DirectSum.decompose_of_mem_same 𝒜 hh]`. Establish `h2` using `(Ideal.Quotient.eq_zero_iff_mem).mpr h1`. Simplify using `only [map_add, map_sub, map_mul] at h2`. Take the linear combination `h2`.

Establish `hfin : ∀ e : ℤ, e ≠ 0 → ∀ a : ℤ, ∃ n : ℕ, c (a + n * e) = 0`. Introduce `e he a`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hinj : Function.Injective (fun n : ℕ => a + (n : ℤ) * e)`.

Introduce `m n hmn`. Establish `h1 : (m : ℤ) * e = n * e` using `add_left_cancel hmn`. Conclude with `mul_right_cancel₀ he h1` after adjusting the coercions. Use `Set.infinite_of_injective_forall_mem hinj (s := ((DirectSum.decompose 𝒜 u).support : Set ℤ)) ?_ (Finset.finite_toSet _)` and prove the remaining obligations. Introduce `n`.

Rewrite using `[Finset.mem_coe, DFinsupp.mem_support_iff]`. Introduce `h0`. Apply `hcon n` to reduce the goal to its premises. Simplify using `only [hc]`. Rewrite using `[h0]`.

Both sides reduce to the same expression. Establish `hA : ∀ k : ℕ, q (c (w - d)) = q (c (w - d + k * (-d))) * q f ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `e1 : w - d + (k : ℤ) * (-d) = (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d` using `by push_cast; ring`. Establish `e2 : (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d ≠ w`. Rewrite using `[← e1]`. Introduce `h0`.

Establish `h1 : ((k : ℤ) + 1) * d = 0` using `by linear_combination -h0`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `hd h2`. Rewrite using `[ih, e1, hne _ e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : q (c (w - d)) = 0`. Take `⟨n, hn⟩` from `hfin (-d) (neg_ne_zero.mpr hd) (w - d)`. Rewrite using `[hA n, hn]`. Simplify using the standard rewrite rules.

Establish `hB : ∀ k : ℕ, q (c (w + k * d)) = - (q f ^ k * q h)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [heq, h0]`. Consider the case `succ k ih`.

Establish `e1 : w + ((k + 1 : ℕ) : ℤ) * d = (w + (k : ℤ) * d) + d` using `by push_cast; ring`. Establish `e2 : (w + (k : ℤ) * d) + d ≠ w`. Introduce `h0`. Establish `h1 : ((k : ℤ) + 1) * d = 0` using `by linear_combination h0`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases.

Use linear arithmetic over natural numbers and integers. Conclude with `hd h2`. Rewrite using `[e1, hne _ e2, ih]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, hn⟩` from `hfin d hd w`.

Use `⟨n, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩` and prove the remaining obligations. Establish `h1` using `hB n`. Rewrite `h1` using `[hn, map_zero]`. Rewrite using `[map_mul, map_pow]`. Conclude with `neg_eq_zero.mp h1.symm`.
-/
theorem UpperTheory.V.Alg.M.deh_holds :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (I : Ideal A),
      I.IsHomogeneous 𝒜 → ∀ (d w : ℤ) (f h : A), d ≠ 0 → f ∈ 𝒜 d → h ∈ 𝒜 w → h ∈ I ⊔ Ideal.span {f - 1} → ∃ n : ℕ, f ^ n * h ∈ I := by
  classical
  intro O A _ _ _ 𝒜 _ I hI d w f h hd hf hh hmem
  obtain ⟨i, hi, y, hy, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  set c : ℤ → A := fun j => (DirectSum.decompose 𝒜 u j : A) with hc
  have hcomp : ∀ j : ℤ, (DirectSum.decompose 𝒜 h (j + d) : A) - c j * f + c (j + d) ∈ I := by
    intro j
    have h1 : (DirectSum.decompose 𝒜 i (j + d) : A) ∈ I := hI (j + d) hi
    have h2 : i = h - u * f + u := by rw [← hsum]; ring
    have h3 : (DirectSum.decompose 𝒜 (u * f) (j + d) : A) = c j * f :=
      DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hf
    rw [h2, DirectSum.decompose_add, DirectSum.decompose_sub, DirectSum.add_apply,
      DirectSum.sub_apply, Submodule.coe_add, Submodule.coe_sub, h3] at h1
    exact h1
  let q := Ideal.Quotient.mk I
  have hne : ∀ j : ℤ, j + d ≠ w → q (c (j + d)) = q (c j) * q f := by
    intro j hj
    have h1 := hcomp j
    rw [DirectSum.decompose_of_mem_ne 𝒜 hh (Ne.symm hj)] at h1
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr h1
    simp only [map_add, map_sub, map_mul, map_zero] at h2
    linear_combination h2
  have heq : q (c w) = q (c (w - d)) * q f - q h := by
    have h1 := hcomp (w - d)
    rw [sub_add_cancel, DirectSum.decompose_of_mem_same 𝒜 hh] at h1
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr h1
    simp only [map_add, map_sub, map_mul] at h2
    linear_combination h2
  have hfin : ∀ e : ℤ, e ≠ 0 → ∀ a : ℤ, ∃ n : ℕ, c (a + n * e) = 0 := by
    intro e he a
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun n : ℕ => a + (n : ℤ) * e) := by
      intro m n hmn
      have h1 : (m : ℤ) * e = n * e := add_left_cancel hmn
      exact_mod_cast mul_right_cancel₀ he h1
    refine Set.infinite_of_injective_forall_mem hinj
      (s := ((DirectSum.decompose 𝒜 u).support : Set ℤ)) ?_ (Finset.finite_toSet _)
    intro n
    rw [Finset.mem_coe, DFinsupp.mem_support_iff]
    intro h0
    apply hcon n
    simp only [hc]
    rw [h0]; rfl
  have hA : ∀ k : ℕ, q (c (w - d)) = q (c (w - d + k * (-d))) * q f ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : w - d + (k : ℤ) * (-d) = (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d := by
        push_cast; ring
      have e2 : (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d ≠ w := by
        rw [← e1]
        intro h0
        have h1 : ((k : ℤ) + 1) * d = 0 := by linear_combination -h0
        rcases mul_eq_zero.mp h1 with h2 | h2
        · omega
        · exact hd h2
      rw [ih, e1, hne _ e2]; ring
  have h0 : q (c (w - d)) = 0 := by
    obtain ⟨n, hn⟩ := hfin (-d) (neg_ne_zero.mpr hd) (w - d)
    rw [hA n, hn]; simp
  have hB : ∀ k : ℕ, q (c (w + k * d)) = - (q f ^ k * q h) := by
    intro k
    induction k with
    | zero => simp [heq, h0]
    | succ k ih =>
      have e1 : w + ((k + 1 : ℕ) : ℤ) * d = (w + (k : ℤ) * d) + d := by
        push_cast; ring
      have e2 : (w + (k : ℤ) * d) + d ≠ w := by
        intro h0
        have h1 : ((k : ℤ) + 1) * d = 0 := by linear_combination h0
        rcases mul_eq_zero.mp h1 with h2 | h2
        · omega
        · exact hd h2
      rw [e1, hne _ e2, ih]; ring
  obtain ⟨n, hn⟩ := hfin d hd w
  refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  have h1 := hB n
  rw [hn, map_zero] at h1
  rw [map_mul, map_pow]
  exact neg_eq_zero.mp h1.symm
