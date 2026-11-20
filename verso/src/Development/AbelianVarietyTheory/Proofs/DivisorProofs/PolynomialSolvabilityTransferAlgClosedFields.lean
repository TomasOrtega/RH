import Mathlib
open MvPolynomial

namespace GlobalTheory.PointTransfer

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)`. Conclude with `⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩`.
-/
theorem exists_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    [Algebra.FiniteType F A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `he : zeroLocus Ω I = ∅`. Rewrite using `[Set.eq_empty_iff_forall_notMem]`. Introduce `y hy`. Conclude with `h ⟨y, fun f hf => hy f hf⟩`.

Establish `h2` using `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I`. Rewrite `h2` using `[he, MvPolynomial.vanishingIdeal_empty]`. Conclude with `hI (Ideal.radical_eq_top.1 h2.symm)`.
-/
theorem exists_common_zero {Ω τ : Type} [Field Ω] [IsAlgClosed Ω] [Finite τ]
    (I : Ideal (MvPolynomial τ Ω)) (hI : I ≠ ⊤) : ∃ y : τ → Ω, ∀ f ∈ I, aeval y f = 0 := by
  by_contra h
  have he : zeroLocus Ω I = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h ⟨y, fun f hf => hy f hf⟩
  have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I
  rw [he, MvPolynomial.vanishingIdeal_empty] at h2
  exact hI (Ideal.radical_eq_top.1 h2.symm)

noncomputable def partialEval {F A σ τ : Type} [CommRing F] [CommRing A] [Algebra F A] (u : σ → A) :
    MvPolynomial (σ ⊕ τ) F →ₐ[F] MvPolynomial τ A :=
  aeval (Sum.elim (fun s => C (u s)) X)

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [partialEval, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp]`.

Apply the tactic sequence `cases i <;> simp [partialEval]`.
-/
theorem eval₂Hom_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (y : τ → B) (g : MvPolynomial (σ ⊕ τ) F) :
    eval₂Hom (ψ : A →+* B) y (partialEval u g) = aeval (Sum.elim (fun s => ψ (u s)) y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [partialEval, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp]`.

Apply the tactic sequence `cases i <;> simp [partialEval]`.
-/
theorem map_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (g : MvPolynomial (σ ⊕ τ) F) :
    MvPolynomial.map (ψ : A →+* B) (partialEval u g) = partialEval (fun s => ψ (u s)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

/- English proof (translation)
Establish `hI : J.map (partialEval (F` using `F) (τ := τ) u) ≠ ⊤ := by`. Introduce `htop`. Establish `h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω) ((partialEval (F` using `F) (τ := τ) u) '' (J : Set _)) := by`. Establish `: (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F` using `F) (τ := τ) u) := by`. Rewrite using `[htop]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `this`. Take `⟨n, c, g, hsum⟩` from `Submodule.mem_span_set'.1 h1`. Use `choose g' hg'J hg' using fun i => (g i).2`. Set `S : Set Ω` to `Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)`.

Establish `hS : S.Finite` using `(Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)`. Set `A : Subalgebra F Ω` to `Algebra.adjoin F S`. Use `haveI : Algebra.FiniteType F A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)`. Take `⟨ψ⟩` from `exists_algHom_algebraicClosure F A`. Set `uA : σ → A` to `fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩`.

Establish `hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ` using `τ) (A.val : A →+* Ω)) := by`. Introduce `i`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `a ha`. Conclude with `⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩`.

Use `choose c' hc' using hc`. Establish `hid : ∑ i, c' i * partialEval uA (g' i) = 1`. Apply `MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[map_one, ← hsum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]`. Both sides reduce to the same expression. Take `⟨y, hy⟩` from `H (fun s => ψ (uA s)) (by`. Introduce `p hp`. Establish `h0 : aeval uA p = 0`.

Apply `Subtype.val_injective` to reduce the goal to its premises. Use `DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p` as an intermediate fact. Conclude with `this.trans (hu p hp)`. Use `DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p` as an intermediate fact. Rewrite using `[← this, AlgHom.comp_apply, h0, map_zero])`.

Use `congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid` as an intermediate fact. Rewrite `this` using `[map_one, map_sum, Finset.sum_eq_zero]`. Conclude with `zero_ne_one this`. Introduce `i _`. Rewrite using `[map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]`.

Take `⟨y, hy⟩` from `exists_common_zero _ hI`. Use `⟨y, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h` using `hy _ (Ideal.mem_map_of_mem _ hg)`. Establish `h2` using `eval₂Hom_partialEval (AlgHom.id F Ω) u y g`. Conclude with `h2.symm.trans h`.
-/
theorem solvable_transfer (F σ τ : Type) [Field F] [Finite σ] [Finite τ]
    (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F))
    (H : ∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) →
      ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω)
    (hu : ∀ g ∈ P, aeval u g = 0) :
    ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  have hI : J.map (partialEval (F := F) (τ := τ) u) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω)
        ((partialEval (F := F) (τ := τ) u) '' (J : Set _)) := by
      have : (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F := F) (τ := τ) u) := by
        rw [htop]; trivial
      exact this
    obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
    choose g' hg'J hg' using fun i => (g i).2
    let S : Set Ω := Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)
    have hS : S.Finite :=
      (Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)
    let A : Subalgebra F Ω := Algebra.adjoin F S
    haveI : Algebra.FiniteType F A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
    obtain ⟨ψ⟩ := exists_algHom_algebraicClosure F A
    let uA : σ → A := fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩
    have hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ := τ) (A.val : A →+* Ω)) := by
      intro i
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩
    choose c' hc' using hc
    have hid : ∑ i, c' i * partialEval uA (g' i) = 1 := by
      apply MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective
      rw [map_one, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]
      rfl
    obtain ⟨y, hy⟩ := H (fun s => ψ (uA s)) (by
      intro p hp
      have h0 : aeval uA p = 0 := by
        apply Subtype.val_injective
        have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p
        exact this.trans (hu p hp)
      have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p
      rw [← this, AlgHom.comp_apply, h0, map_zero])
    have := congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid
    rw [map_one, map_sum, Finset.sum_eq_zero] at this
    · exact zero_ne_one this
    · intro i _
      rw [map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]
  obtain ⟨y, hy⟩ := exists_common_zero _ hI
  refine ⟨y, fun g hg => ?_⟩
  have h := hy _ (Ideal.mem_map_of_mem _ hg)
  have h2 := eval₂Hom_partialEval (AlgHom.id F Ω) u y g
  exact h2.symm.trans h

end GlobalTheory.PointTransfer
