import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Use `Module.Projective.of_split (LinearMap.range P.mulVecLin).subtype P.mulVecLin.rangeRestrict ?_` and prove the remaining obligations. Use extensionality with `⟨v, w, rfl⟩ j`. Simplify using `[Matrix.mulVec_mulVec, hP]`.
-/
theorem range_idempotent_projective {A : Type} [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) : Module.Projective A (LinearMap.range P.mulVecLin) := by
  refine Module.Projective.of_split (LinearMap.range P.mulVecLin).subtype P.mulVecLin.rangeRestrict ?_
  ext ⟨v, w, rfl⟩ j
  simp [Matrix.mulVec_mulVec, hP]

/- English proof (translation)
Introduce `A _ I _ n P hP m`. Set `V : Set (PrimeSpectrum A)` to `⋂ i, {q | Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m}`. Establish `hV : IsClopen V`. Use `isClopen_iInter_of_finite fun i => ?_` and prove the remaining obligations. Use `range_idempotent_projective n (P i) (hP i)` as an intermediate fact.

Use `Module.finitePresentation_of_projective A (LinearMap.range (P i).mulVecLin)` as an intermediate fact. Conclude with `(Module.isLocallyConstant_rankAtStalk (R := A) (M := LinearMap.range (P i).mulVecLin)).isClopen_fiber m`. Take `⟨e, x, hmul, hadd, hVe⟩` from `PrimeSpectrum.isClopen_iff_mul_add.mp hV`. Use `⟨x, fun T _ f => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ q : PrimeSpectrum A, q ∈ V ↔ e ∉ q.asIdeal`.

Introduce `q`. Rewrite using `[hVe]`. Both sides reduce to the same expression. Establish `hmem' : ∀ q : PrimeSpectrum A, q ∈ V ↔ ∀ i, Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m`. Introduce `q`.

Simplify using `[V]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `hxx : f x * f x = f x`. Establish `: x * x = x`.

Establish `h1 : x = x * (e + x)` using `by rw [hadd, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, this]`. Establish `hnil : IsNilpotent (f x)`. Rewrite using `[← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]`.

Introduce `(Q : Ideal T) hQ`. Use `haveI : Q.IsPrime := hQ`. Set `k` to `AlgebraicClosure (FractionRing (T ⧸ Q))`. Set `h : T →+* k` to `(algebraMap (FractionRing (T ⧸ Q)) k).comp ((algebraMap (T ⧸ Q) (FractionRing (T ⧸ Q))).comp (Ideal.Quotient.mk Q))`. Establish `hker : RingHom.ker h = Q`.

Use extensionality with `t`. Simplify using `only [h, RingHom.mem_ker, RingHom.comp_apply]`. Rewrite using `[map_eq_zero_iff _ (algebraMap (FractionRing (T ⧸ Q)) k).injective, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hq` using `(hmem _).mp ((hmem' _).mpr (H k h))`. Establish `: e * x ∈ RingHom.ker (h.comp f)` using `by rw [hmul]; exact Ideal.zero_mem _`.

Break down `(RingHom.ker_isPrime (h.comp f)).mem_or_mem this with he | hx` into its components or cases. Conclude with `absurd he hq`. Rewrite `hx` using `[RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker]`. Conclude with `hx`. Take `⟨N, hN⟩` from `hnil`.

Establish `: ∀ j : ℕ, f x ^ (j + 1) = f x`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, ih, hxx]`.

Break down `N with _ | N` into its components or cases. Simplify using `at hN`. Conclude with `(subsingleton_of_zero_eq_one hN.symm).elim _ _`. Rewrite `hN` using `[this]`. Conclude with `hN`.

Introduce `hx k _ _ h i`. Use `((hmem' _).mp ?_) i` and prove the remaining obligations. Rewrite using `[hmem]`. Use `show e ∉ RingHom.ker (h.comp f)`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply]`.

Establish `: f e = 1`. Use `congrArg f hadd` as an intermediate fact. Rewrite `this` using `[map_add, hx, add_zero, map_one]`. Conclude with `this`. Rewrite using `[this, map_one]`.

Conclude with `one_ne_zero`.
-/
theorem exists_rank_ideal_of_idempotent : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  intro A _ I _ n P hP m
  let V : Set (PrimeSpectrum A) :=
    ⋂ i, {q | Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m}
  have hV : IsClopen V := by
    refine isClopen_iInter_of_finite fun i => ?_
    have := range_idempotent_projective n (P i) (hP i)
    have := Module.finitePresentation_of_projective A (LinearMap.range (P i).mulVecLin)
    exact (Module.isLocallyConstant_rankAtStalk (R := A)
      (M := LinearMap.range (P i).mulVecLin)).isClopen_fiber m
  obtain ⟨e, x, hmul, hadd, hVe⟩ := PrimeSpectrum.isClopen_iff_mul_add.mp hV
  refine ⟨x, fun T _ f => ?_⟩
  have hmem : ∀ q : PrimeSpectrum A, q ∈ V ↔ e ∉ q.asIdeal := by
    intro q; rw [hVe]; rfl
  have hmem' : ∀ q : PrimeSpectrum A, q ∈ V ↔ ∀ i, Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m := by
    intro q; simp [V]
  constructor
  · intro H
    have hxx : f x * f x = f x := by
      have : x * x = x := by
        have h1 : x = x * (e + x) := by rw [hadd, mul_one]
        calc x * x = x * (e + x) - x * e := by ring
          _ = x := by rw [← h1, mul_comm x e, hmul, sub_zero]
      rw [← map_mul, this]
    have hnil : IsNilpotent (f x) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
      intro (Q : Ideal T) hQ
      haveI : Q.IsPrime := hQ
      let k := AlgebraicClosure (FractionRing (T ⧸ Q))
      let h : T →+* k := (algebraMap (FractionRing (T ⧸ Q)) k).comp
        ((algebraMap (T ⧸ Q) (FractionRing (T ⧸ Q))).comp (Ideal.Quotient.mk Q))
      have hker : RingHom.ker h = Q := by
        ext t
        simp only [h, RingHom.mem_ker, RingHom.comp_apply]
        rw [map_eq_zero_iff _ (algebraMap (FractionRing (T ⧸ Q)) k).injective,
          IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      have hq := (hmem _).mp ((hmem' _).mpr (H k h))
      have : e * x ∈ RingHom.ker (h.comp f) := by rw [hmul]; exact Ideal.zero_mem _
      rcases (RingHom.ker_isPrime (h.comp f)).mem_or_mem this with he | hx
      · exact absurd he hq
      · rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker] at hx
        exact hx
    obtain ⟨N, hN⟩ := hnil
    have : ∀ j : ℕ, f x ^ (j + 1) = f x := by
      intro j; induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, hxx]
    rcases N with _ | N
    · simp at hN; exact (subsingleton_of_zero_eq_one hN.symm).elim _ _
    · rw [this] at hN; exact hN
  · intro hx k _ _ h i
    refine ((hmem' _).mp ?_) i
    rw [hmem]
    show e ∉ RingHom.ker (h.comp f)
    rw [RingHom.mem_ker, RingHom.comp_apply]
    have : f e = 1 := by
      have := congrArg f hadd
      rw [map_add, hx, add_zero, map_one] at this; exact this
    rw [this, map_one]; exact one_ne_zero

end GlobalTheory
