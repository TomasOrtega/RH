import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial Cardinal

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ x hx hinj P _`. Set `φ : A[X] →ₐ[A] B` to `aeval x`. Establish `hφ : Function.Surjective φ`. Introduce `b`. Establish `hb : b ∈ (aeval x : A[X] →ₐ[A] B).range`.

Rewrite using `[← Algebra.adjoin_singleton_eq_range_aeval, hx]`. Conclude with `Algebra.mem_top`. Conclude with `hb`. Set `P' : Ideal A[X]` to `P.comap (φ : A[X] →+* B)`. Establish `hP' : P.under A = P'.under A`.

Use extensionality with `a`. Simplify using `[P', φ, Ideal.under, Ideal.mem_comap]`. Establish `: P'.LiesOver (P.under A)` using `⟨hP'⟩`. Establish `H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤ ofENat (P.under A).height + 1`. Establish `key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q], ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1`.

Introduce `q _ _`. Take `rfl : q = P'.under A` from `Ideal.LiesOver.over`. Conclude with `h₁ A P'`. Conclude with `key _`. Establish `htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) = lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P))`.

Set `f : A[X] ⧸ P' →+* B ⧸ P` to `Ideal.quotientMap P (φ : A[X] →+* B) le_rfl`. Establish `hf : Function.Bijective f` using `⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩`. Use `AlgEquiv.lift_trdeg_eq (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)` and prove the remaining obligations. Introduce `a`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Simplify using `[f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]`. Establish `H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤ ofENat (P.under A).height + 1`. Use `Cardinal.lift_le.{v}.mpr H₁` as an intermediate fact. Simplify `this` using `only [lift_add, lift_ofENat, lift_one, htr]`. Rewrite using `[← Cardinal.lift_le.{u}]`.

Simplify using `only [lift_add, lift_ofENat]`. Distinguish the cases in `hker : RingHom.ker φ = ⊥`. Establish `hinjφ : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot _).mpr hker`. Set `e : A[X] ≃ₐ[A] B` to `AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩`. Establish `hh : P'.height = P.height` using `RingEquiv.height_comap (e : A[X] ≃+* B) P`.

Establish `ht : lift.{u} (Algebra.trdeg A B) = 1`. Rewrite using `[← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]`. Rewrite using `[ht, ← hh]`. Conclude with `H₁'`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hφ`.

Set `Q : Ideal (A[X] ⧸ RingHom.ker φ)` to `P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)`. Establish `hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P'`. Use extensionality with `f`. Simplify using `[Q, P', e, Ideal.mem_comap]`. Establish `H₂` using `h₂ A[X] (RingHom.ker φ) hker Q`.

Rewrite `H₂` using `[hQ, RingEquiv.height_comap]`. Establish `H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤ ofENat (P.under A).height + 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ofENat_add, ofENat_one]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl`. Use `_ ≤ _ := H₁'`. Conclude with `(Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add`.
-/
theorem DimensionInequalityOneGenerator.proof (h₁ : PolynomialDimensionInequality.Statement.{u})
    (h₂ : QuotientHeightAddOne.Statement.{u}) : DimensionInequalityOneGenerator.Statement.{u, v} := by
  intro A B _ _ _ _ _ _ x hx hinj P _

  let φ : A[X] →ₐ[A] B := aeval x
  have hφ : Function.Surjective φ := by
    intro b
    have hb : b ∈ (aeval x : A[X] →ₐ[A] B).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
    exact hb

  let P' : Ideal A[X] := P.comap (φ : A[X] →+* B)
  have hP' : P.under A = P'.under A := by
    ext a; simp [P', φ, Ideal.under, Ideal.mem_comap]
  have : P'.LiesOver (P.under A) := ⟨hP'⟩

  have H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤
      ofENat (P.under A).height + 1 := by
    have key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q],
        ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1 := by
      intro q _ _
      obtain rfl : q = P'.under A := Ideal.LiesOver.over
      exact h₁ A P'
    exact key _

  have htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) =
      lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
    let f : A[X] ⧸ P' →+* B ⧸ P := Ideal.quotientMap P (φ : A[X] →+* B) le_rfl
    have hf : Function.Bijective f :=
      ⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩
    refine AlgEquiv.lift_trdeg_eq
      (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]

  have H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤
      ofENat (P.under A).height + 1 := by
    have := Cardinal.lift_le.{v}.mpr H₁
    simpa only [lift_add, lift_ofENat, lift_one, htr] using this
  rw [← Cardinal.lift_le.{u}]
  simp only [lift_add, lift_ofENat]
  by_cases hker : RingHom.ker φ = ⊥
  ·
    have hinjφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩
    have hh : P'.height = P.height := RingEquiv.height_comap (e : A[X] ≃+* B) P
    have ht : lift.{u} (Algebra.trdeg A B) = 1 := by
      rw [← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]
    rw [ht, ← hh]
    exact H₁'
  ·
    let e := Ideal.quotientKerAlgEquivOfSurjective hφ
    let Q : Ideal (A[X] ⧸ RingHom.ker φ) := P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)
    have hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P' := by
      ext f; simp [Q, P', e, Ideal.mem_comap]
    have H₂ := h₂ A[X] (RingHom.ker φ) hker Q
    rw [hQ, RingEquiv.height_comap] at H₂
    have H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤
        ofENat (P.under A).height + 1 :=
      calc ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1
          = ofENat (P.height + 1) + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
            rw [ofENat_add, ofENat_one]; ring
        _ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) :=
            add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl
        _ ≤ _ := H₁'
    exact (Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
