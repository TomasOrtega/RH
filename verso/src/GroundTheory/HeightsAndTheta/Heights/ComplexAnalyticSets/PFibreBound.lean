import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

namespace FibreBound

/- English proof (translation)
Establish `h : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[pullback]`. Introduce `i`.

Simplify using `[pullback, linPoly, Matrix.mulVec, dotProduct]`. Conclude with `congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f P) h`.
-/
theorem eval_pullback (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [pullback]
    · intro i; simp [pullback, linPoly, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f P) h

/- English proof (translation)
Set `p : (Fin n → ℂ) → (Fin n → ℂ) → Polynomial ℂ` to `fun x x' => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j - x' j)`. Establish `hp : ∀ x x', x ≠ x' → p x x' ≠ 0`. Introduce `x x' hne h`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Establish `hc` using `congrArg (fun q => Polynomial.coeff q (j : ℕ)) h`. Simplify using `only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc`. Rewrite `hc` using `[Finset.sum_eq_single j]`. Simplify `hc` using `[sub_eq_zero]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Conclude with `fun h => hb (Fin.ext h)`. Simplify using the standard rewrite rules. Establish `hev : ∀ x x' (t : ℂ), (p x x').eval t = ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ)`. Introduce `x x' t`.

Simplify using `only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]`. Take `⟨t, ht⟩` from `Infinite.exists_notMem_finset (((T ×ˢ T).filter (fun z => z.1 ≠ z.2)).biUnion (fun z => (p z.1 z.2).roots.toFinset))`. Use `⟨fun j => t ^ (j : ℕ), ?_⟩` and prove the remaining obligations. Introduce `x hx x' hx' hxx'`. Assume the negation of the conclusion as `hne`.

Apply `ht` to reduce the goal to its premises. Simplify using `only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]`. Use `⟨(x, x'), ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hx'⟩, hne⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots (hp x x' hne), Polynomial.IsRoot, hev]`. Establish `hs : ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) = (∑ j : Fin n, t ^ (j : ℕ) * x j) - ∑ j : Fin n, t ^ (j : ℕ) * x' j`.

Rewrite using `[← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[hs]`. Conclude with `sub_eq_zero.mpr hxx'`.
-/
theorem exists_linear_injOn (T : Finset (Fin n → ℂ)) :
    ∃ c : Fin n → ℂ, Set.InjOn (fun x : Fin n → ℂ => ∑ j, c j * x j) T := by
  classical
  let p : (Fin n → ℂ) → (Fin n → ℂ) → Polynomial ℂ := fun x x' =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j - x' j)
  have hp : ∀ x x', x ≠ x' → p x x' ≠ 0 := by
    intro x x' hne h
    apply hne
    funext j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ x x' (t : ℂ), (p x x').eval t = ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) := by
    intro x x' t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (((T ×ˢ T).filter (fun z => z.1 ≠ z.2)).biUnion (fun z => (p z.1 z.2).roots.toFinset))
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  intro x hx x' hx' hxx'
  by_contra hne
  apply ht
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
  refine ⟨(x, x'), ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hx'⟩, hne⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp x x' hne), Polynomial.IsRoot, hev]
  have hs : ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) =
      (∑ j : Fin n, t ^ (j : ℕ) * x j) - ∑ j : Fin n, t ^ (j : ℕ) * x' j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; exact sub_eq_zero.mpr hxx'

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `(projHom J A).toRingHom.toAlgebra`. Set `_ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `Algebra.toModule`. Establish `: Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `hA.finite`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `Algebra.IsIntegral.of_finite _ _`. Take `⟨f, hfm, hf⟩` from `Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s`.

Establish `: IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)) (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J))` using `TensorProduct.isScalarTower_left`. Establish `: Module.Free (FractionRing (MvPolynomial (Fin d) ℂ)) (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J))` using `Module.Free.of_divisionRing _ _`. Set `t : TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` to `Algebra.TensorProduct.includeRight s`. Establish `hq : minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t ∣ f.map (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)))`. Apply `minpoly.dvd` to reduce the goal to its premises.

Rewrite using `[Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hf, map_zero]`. Take `⟨g, hg⟩` from `IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (MvPolynomial (Fin d) ℂ)) hfm hq`. Establish `hqm : (minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t).Monic` using `minpoly.monic (IsIntegral.of_finite _ t)`. Rewrite `hg` using `[hqm.leadingCoeff, Polynomial.C_1, mul_one]`. Establish `hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)))` using `IsFractionRing.injective _ _`.

Use `⟨g, Polynomial.monic_of_injective hinj (hg ▸ hqm), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.natDegree_map_eq_of_injective hinj, hg]`. Conclude with `minpoly.natDegree_le t`. Establish `h1 : TensorProduct.mk (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) 1 (Polynomial.aeval s g) = 0`. Rewrite using `[TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_map_algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)), hg]`.

Conclude with `minpoly.aeval _ t`. Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors (MvPolynomial (Fin d) ℂ)) (TensorProduct.mk _ (FractionRing (MvPolynomial (Fin d) ℂ)) _ 1)).mp h1`. Rewrite `hc` using `[Submonoid.smul_def, Algebra.smul_def]`. Use `(mul_eq_zero.mp hc).resolve_left ?_` and prove the remaining obligations. Introduce `h0`.

Apply `nonZeroDivisors.coe_ne_zero c` to reduce the goal to its premises. Apply `hA.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h0`.
-/
theorem exists_monic_aeval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (s : MvPolynomial (Fin n) ℂ ⧸ J) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ),
      g.Monic ∧ g.natDegree ≤ projDegree J A ∧ Polynomial.aeval s g = 0 := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s
  have : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := TensorProduct.isScalarTower_left
  have : Module.Free (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := Module.Free.of_divisionRing _ _
  let t : TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.TensorProduct.includeRight s
  have hq : minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t ∣
      f.map (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hf,
      map_zero]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (MvPolynomial (Fin d) ℂ)) hfm hq
  have hqm : (minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t).Monic :=
    minpoly.monic (IsIntegral.of_finite _ t)
  rw [hqm.leadingCoeff, Polynomial.C_1, mul_one] at hg
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) :=
    IsFractionRing.injective _ _
  refine ⟨g, Polynomial.monic_of_injective hinj (hg ▸ hqm), ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hg]
    exact minpoly.natDegree_le t
  · have h1 : TensorProduct.mk (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J) 1 (Polynomial.aeval s g) = 0 := by
      rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply,
        ← Polynomial.aeval_algHom_apply,
        ← Polynomial.aeval_map_algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)), hg]
      exact minpoly.aeval _ t
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (MvPolynomial (Fin d) ℂ))
      (TensorProduct.mk _ (FractionRing (MvPolynomial (Fin d) ℂ)) _ 1)).mp h1
    rw [Submonoid.smul_def, Algebra.smul_def] at hc
    refine (mul_eq_zero.mp hc).resolve_left ?_
    intro h0
    apply nonZeroDivisors.coe_ne_zero c
    apply hA.injective
    rw [map_zero]
    exact h0

/- English proof (translation)
Introduce `n d J A hJ _ hA y`. Use `hJ` as an intermediate fact. Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `(projHom J A).toRingHom.toAlgebra`. Set `_ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `Algebra.toModule`. Establish `: Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `hA.finite`.

Establish `: Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `Algebra.IsIntegral.of_finite _ _`. Establish `hbound : ∀ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ fibre J A y → T.card ≤ projDegree J A`. Introduce `T hT`. Take `⟨c, hc⟩` from `exists_linear_injOn T`. Take `⟨g, hgm, hgd, hg⟩` from `exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (∑ j, C (c j) * X j))`.

Establish `hgy : (g.map (MvPolynomial.eval y)).Monic` using `hgm.map _`. Establish `hroot : ∀ x ∈ T, (∑ j, c j * x j) ∈ (g.map (MvPolynomial.eval y)).roots.toFinset`. Introduce `x hx`. Take `⟨hxJ, hxA⟩` from `hT (Finset.mem_coe.mpr hx)`. Set `ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ` to `Ideal.Quotient.lift J (eval x) (fun q hq => hxJ q hq)`.

Establish `hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = MvPolynomial.eval y`. Use `RingHom.ext fun P => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ev (Ideal.Quotient.mk J (pullback A P)) = _`. Rewrite using `[Ideal.Quotient.lift_mk, eval_pullback, hxA]`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hgy.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]`.

Establish `h` using `congrArg ev hg`. Rewrite `h` using `[Polynomial.aeval_def, Polynomial.hom_eval₂, hev, map_zero]`. Establish `hs : ev (Ideal.Quotient.mk J (∑ j, C (c j) * X j)) = ∑ j, c j * x j`. Express the relevant statement in the definitionally equal form `eval x (∑ j, C (c j) * X j) = _`. Simplify using the standard rewrite rules.

Rewrite `h` using `[hs]`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation. Introduce `v hv`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hv`.

Conclude with `hroot x hx)`. Use `_ ≤ Multiset.card (g.map (MvPolynomial.eval y)).roots := Multiset.toFinset_card_le _`. Use `_ ≤ (g.map (MvPolynomial.eval y)).natDegree := Polynomial.card_roots' _`. Use `_ = g.natDegree := hgm.natDegree_map _`. Use `_ ≤ projDegree J A := hgd`.

Establish `hne : (fibre J A y).Nonempty`. Establish `hmax : (RingHom.ker (MvPolynomial.eval y)).IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, eval_C _⟩)`. Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (MvPolynomial.eval y)) (by`. Introduce `P hP`. Establish `hP0 : P = 0` using `hA.injective (by rw [map_zero]; exact hP)`.

Rewrite using `[hP0]`. Conclude with `Ideal.zero_mem _)`. Use `hQ` as an intermediate fact. Establish `hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨x, hx⟩` from `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hQ'`.

Establish `hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval x q = 0`. Introduce `q hq`. Establish `hq' : q ∈ Q.comap (Ideal.Quotient.mk J)` using `hq`. Rewrite `hq'` using `[hx]`. Conclude with `(MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'`.

Use `⟨x, fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact Q.zero_mem), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1 : X i - C (y i) ∈ RingHom.ker (MvPolynomial.eval y)` using `by simp [RingHom.mem_ker]`. Rewrite `h1` using `[← hQc]`. Establish `h2` using `hmem (pullback A (X i - C (y i))) h1`.

Rewrite `h2` using `[eval_pullback]`. Simplify `h2` using `[sub_eq_zero]`. Establish `hfin : (fibre J A y).Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨T, hT, hcard⟩` from `Set.Infinite.exists_subset_card_eq hinf (projDegree J A + 1)`.

Use `hbound T hT` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨hne, hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`. Conclude with `hbound _ (by simp)`.
-/
theorem proof : FibreBound.Statement := by
  intro n d J A hJ _ hA y
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  have hbound : ∀ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ fibre J A y →
      T.card ≤ projDegree J A := by
    intro T hT
    obtain ⟨c, hc⟩ := exists_linear_injOn T
    obtain ⟨g, hgm, hgd, hg⟩ :=
      exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (∑ j, C (c j) * X j))
    have hgy : (g.map (MvPolynomial.eval y)).Monic := hgm.map _
    have hroot : ∀ x ∈ T, (∑ j, c j * x j) ∈ (g.map (MvPolynomial.eval y)).roots.toFinset := by
      intro x hx
      obtain ⟨hxJ, hxA⟩ := hT (Finset.mem_coe.mpr hx)
      let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ :=
        Ideal.Quotient.lift J (eval x) (fun q hq => hxJ q hq)
      have hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) =
          MvPolynomial.eval y := by
        refine RingHom.ext fun P => ?_
        change ev (Ideal.Quotient.mk J (pullback A P)) = _
        rw [Ideal.Quotient.lift_mk, eval_pullback, hxA]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgy.ne_zero, Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have h := congrArg ev hg
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hev, map_zero] at h
      have hs : ev (Ideal.Quotient.mk J (∑ j, C (c j) * X j)) = ∑ j, c j * x j := by
        change eval x (∑ j, C (c j) * X j) = _
        simp
      rw [hs] at h
      exact h
    calc T.card = (T.image fun x => ∑ j, c j * x j).card := (Finset.card_image_of_injOn hc).symm
      _ ≤ (g.map (MvPolynomial.eval y)).roots.toFinset.card := Finset.card_le_card (by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
          exact hroot x hx)
      _ ≤ Multiset.card (g.map (MvPolynomial.eval y)).roots := Multiset.toFinset_card_le _
      _ ≤ (g.map (MvPolynomial.eval y)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := hgm.natDegree_map _
      _ ≤ projDegree J A := hgd
  have hne : (fibre J A y).Nonempty := by
    have hmax : (RingHom.ker (MvPolynomial.eval y)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, eval_C _⟩)
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (MvPolynomial.eval y)) (by
        intro P hP
        have hP0 : P = 0 := hA.injective (by rw [map_zero]; exact hP)
        rw [hP0]; exact Ideal.zero_mem _)
    have := hQ
    have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hQ'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    refine ⟨x, fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact Q.zero_mem), ?_⟩
    funext i
    have h1 : X i - C (y i) ∈ RingHom.ker (MvPolynomial.eval y) := by simp [RingHom.mem_ker]
    rw [← hQc] at h1
    have h2 := hmem (pullback A (X i - C (y i))) h1
    rw [eval_pullback] at h2
    simpa [sub_eq_zero] using h2
  have hfin : (fibre J A y).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (projDegree J A + 1)
    have := hbound T hT
    omega
  refine ⟨hne, hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ (by simp)

end FibreBound

end

end GroundTheory.Heights₂.Heights.ComplexSets
