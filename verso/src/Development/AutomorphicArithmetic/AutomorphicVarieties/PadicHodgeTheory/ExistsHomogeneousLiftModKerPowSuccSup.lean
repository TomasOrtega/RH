import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
Take `⟨p, hp, i, hi, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[mul_add]`. Use `Submodule.add_mem_sup ?_ (I.mul_mem_left u hi)` and prove the remaining obligations. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hu hp`.
-/
private theorem mul_mem_pow_sup {R : Type} [CommRing R] (P I : Ideal R) (m k : ℕ) (u v : R)
    (hu : u ∈ P ^ m) (hv : v ∈ P ^ k ⊔ I) : u * v ∈ P ^ (m + k) ⊔ I := by
  obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.mp hv
  rw [mul_add]
  refine Submodule.add_mem_sup ?_ (I.mul_mem_left u hi)
  rw [pow_add]
  exact Ideal.mul_mem_mul hu hp

/- English proof (translation)
Introduce `O R _ _ _ _ I x n t ht hyp`. Establish `htK : ∀ i, t i ∈ RingHom.ker x` using `fun i => RingHom.mem_ker.mpr (ht i)`. Establish `key : ∀ N : ℕ, ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O), e ≠ 0 ∧ h.IsHomogeneous N ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ N ∧ e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero`. Introduce `a _`. Use `⟨1, MvPolynomial.C (x a), one_ne_zero, MvPolynomial.isHomogeneous_C _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.

Apply `Ideal.mem_sup_left` to reduce the goal to its premises. Rewrite using `[zero_add, pow_one, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Consider the case `succ N ih`. Introduce `a ha`.

Rewrite `ha` using `[pow_succ]`. Use `Submodule.mul_induction_on (C := fun a => ∃ (e : O) (h : MvPolynomial (Fin n) O), e ≠ 0 ∧ h.IsHomogeneous (N + 1) ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ∧ e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1 + 1) ⊔ I) ha ?_ ?_` and prove the remaining obligations. Introduce `b hb c hc`. Take `⟨e1, h1, he1, hh1, hm1, hs1⟩` from `ih b hb`. Establish `hxc : x c = 0` using `RingHom.mem_ker.mp hc`.

Take `⟨e2, o, he2, hs2⟩` from `hyp c hxc`. Establish `haL : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i) = ∑ i, o i • t i`. Simplify using `[map_sum, Algebra.smul_def]`. Establish `hLK : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i) ∈ RingHom.ker x`. Rewrite using `[haL]`.

Conclude with `Ideal.sum_mem _ (fun i _ => by`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (htK i))`. Use `⟨e1 * e2, h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i, mul_ne_zero he1 he2, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hh1.mul (MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _))`.

Rewrite using `[map_mul, pow_succ]`. Conclude with `Ideal.mul_mem_mul hm1 hLK`. Establish `eq : (e1 * e2) • (b * c) - MvPolynomial.aeval t (h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i) = (e2 • c) * (e1 • b - MvPolynomial.aeval t h1) + MvPolynomial.aeval t h1 * (e2 • c - ∑ i, o i • t i)`. Rewrite using `[map_mul, haL]`. Simplify using `only [Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `hc' : e2 • c ∈ RingHom.ker x ^ 1`. Rewrite using `[pow_one, Algebra.smul_def]`.

Conclude with `Ideal.mul_mem_left _ _ hc`. Use `mul_mem_pow_sup (RingHom.ker x) I 1 (N + 1) _ _ hc' hs1` as an intermediate fact. Rewrite `this` using `[show 1 + (N + 1) = N + 1 + 1 by omega]`. Then use the resulting hypothesis. Use `mul_mem_pow_sup (RingHom.ker x) I N 2 _ _ hm1 hs2` as an intermediate fact. Rewrite `this` using `[show N + 2 = N + 1 + 1 by omega]`. Then use the resulting hypothesis.

Introduce and unpack `a1 a2 ⟨e1, h1, he1, hh1, hm1, hs1⟩ ⟨e2, h2, he2, hh2, hm2, hs2⟩`. Use `⟨e1 * e2, MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2, mul_ne_zero he1 he2, (hh1.C_mul _).add (hh2.C_mul _), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_C]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm1) (Ideal.mul_mem_left _ _ hm2)`. Establish `eq : (e1 * e2) • (a1 + a2) - MvPolynomial.aeval t (MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2) = e2 • (e1 • a1 - MvPolynomial.aeval t h1) + e1 • (e2 • a2 - MvPolynomial.aeval t h2)`.

Simplify using `only [map_add, map_mul, MvPolynomial.aeval_C, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Conclude with `Ideal.mul_mem_left _ _ hs1`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ hs2`. Introduce `N a ha`. Take `⟨e, h, he, hh, _, hs⟩` from `key N a ha`.

Conclude with `⟨e, h, he, hh, hs⟩`.
-/
theorem UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (t : Fin n → R), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) → ∀ (N : ℕ), ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O), e ≠ 0 ∧ h.IsHomogeneous N ∧ e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
  intro O R _ _ _ _ I x n t ht hyp
  have htK : ∀ i, t i ∈ RingHom.ker x := fun i => RingHom.mem_ker.mpr (ht i)
  have key : ∀ N : ℕ, ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O),
      e ≠ 0 ∧ h.IsHomogeneous N ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ N ∧
      e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
    intro N
    induction N with
    | zero =>
      intro a _
      refine ⟨1, MvPolynomial.C (x a), one_ne_zero, MvPolynomial.isHomogeneous_C _ _, ?_, ?_⟩
      · rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · apply Ideal.mem_sup_left
        rw [zero_add, pow_one, RingHom.mem_ker]
        simp
    | succ N ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on (C := fun a => ∃ (e : O) (h : MvPolynomial (Fin n) O),
        e ≠ 0 ∧ h.IsHomogeneous (N + 1) ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ∧
        e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1 + 1) ⊔ I) ha ?_ ?_
      · intro b hb c hc
        obtain ⟨e1, h1, he1, hh1, hm1, hs1⟩ := ih b hb
        have hxc : x c = 0 := RingHom.mem_ker.mp hc
        obtain ⟨e2, o, he2, hs2⟩ := hyp c hxc
        have haL : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            = ∑ i, o i • t i := by
          simp [map_sum, Algebra.smul_def]
        have hLK : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            ∈ RingHom.ker x := by
          rw [haL]
          exact Ideal.sum_mem _ (fun i _ => by
            rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ (htK i))
        refine ⟨e1 * e2, h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i,
          mul_ne_zero he1 he2, ?_, ?_, ?_⟩
        · exact hh1.mul (MvPolynomial.IsHomogeneous.sum _ _ _
            (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _))
        · rw [map_mul, pow_succ]
          exact Ideal.mul_mem_mul hm1 hLK
        · have eq : (e1 * e2) • (b * c) - MvPolynomial.aeval t
                (h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
              = (e2 • c) * (e1 • b - MvPolynomial.aeval t h1)
                + MvPolynomial.aeval t h1 * (e2 • c - ∑ i, o i • t i) := by
            rw [map_mul, haL]
            simp only [Algebra.smul_def, map_mul]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · have hc' : e2 • c ∈ RingHom.ker x ^ 1 := by
              rw [pow_one, Algebra.smul_def]
              exact Ideal.mul_mem_left _ _ hc
            have := mul_mem_pow_sup (RingHom.ker x) I 1 (N + 1) _ _ hc' hs1
            rwa [show 1 + (N + 1) = N + 1 + 1 by omega] at this
          · have := mul_mem_pow_sup (RingHom.ker x) I N 2 _ _ hm1 hs2
            rwa [show N + 2 = N + 1 + 1 by omega] at this
      · rintro a1 a2 ⟨e1, h1, he1, hh1, hm1, hs1⟩ ⟨e2, h2, he2, hh2, hm2, hs2⟩
        refine ⟨e1 * e2, MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2, mul_ne_zero he1 he2,
          (hh1.C_mul _).add (hh2.C_mul _), ?_, ?_⟩
        · rw [map_add, map_mul, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm1) (Ideal.mul_mem_left _ _ hm2)
        · have eq : (e1 * e2) • (a1 + a2) - MvPolynomial.aeval t
                (MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2)
              = e2 • (e1 • a1 - MvPolynomial.aeval t h1)
                + e1 • (e2 • a2 - MvPolynomial.aeval t h2) := by
            simp only [map_add, map_mul, MvPolynomial.aeval_C, Algebra.smul_def]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs1
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs2
  intro N a ha
  obtain ⟨e, h, he, hh, _, hs⟩ := key N a ha
  exact ⟨e, h, he, hh, hs⟩
