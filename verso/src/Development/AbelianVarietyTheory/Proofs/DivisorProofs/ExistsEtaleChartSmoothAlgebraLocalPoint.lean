import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open IsLocalRing

noncomputable section
namespace GlobalTheory.DenseSec

open KaehlerDifferential
open scoped TensorProduct

/- English proof (translation)
Establish `h1 : Subsingleton Ω[B⁄P]`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `map_surjective R P B x`. Conclude with `(exact_mapBaseChange_map R P B y).mpr (h.2 y)`. Establish `h2 : Subsingleton (Algebra.H1Cotangent P B)`.

Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Establish `h3 : Algebra.H1Cotangent.δ R P B x = 0`. Apply `h.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩`.

Take `⟨y, rfl⟩` from `(Algebra.H1Cotangent.exact_map_δ R P B x).mp h3`. Rewrite using `[Subsingleton.elim y 0, map_zero]`. Conclude with `⟨h1, h2⟩`.
-/
theorem formallyEtale_of_bijective_kaehler_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

/- English proof (translation)
Introduce `R _ _ A _ _ _ ε`. Set `p : Ideal A` to `(maximalIdeal R).comap ε`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Take `⟨κ, a, b, hb⟩` from `Module.exists_basis_of_span_of_flat _ (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)`. Set `t : κ → A` to `fun i => a i - algebraMap R A (ε (a i))`.

Establish `hDt : ∀ i, D R A (t i) = D R A (a i)` using `by intro i; simp [t]`. Establish `hεt : ∀ i, ε (t i) = 0` using `by intro i; simp [t]`. Set `e : (κ →₀ A) →ₗ[A] Ω[A⁄R]` to `Finsupp.linearCombination A fun i : κ ↦ D R A (t i)`. Set `l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p)` to `Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))`. Set `l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R]` to `map R R A (Localization.AtPrime p)`.

Set `eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R]` to `IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e`. Establish `: eₚ = b.repr.symm`. Use extensionality with `i`. Use `trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1`. Simplify using `[eₚ, -IsLocalizedModule.map_apply, l₁]`.

Simplify using `[l₂, e, hb, hDt]`. Establish `heₚ : Function.Bijective eₚ` using `this ▸ b.repr.symm.bijective`. Establish `: Finite κ` using `Module.Finite.finite_basis b`. Take `⟨g, hg, h⟩` from `Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ`. Set `l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g)` to `Finsupp.mapRange.linearMap (Algebra.linearMap A _)`.

Set `l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R]` to `map R R A (Localization.Away g)`. Rewrite `h` using `[← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ]`. Set `eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R]` to `IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e`. Set `bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]` to `.ofRepr (LinearEquiv.ofBijective eₜ' h).symm`. Establish `hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i))`.

Introduce `i`. Establish `h1 : bB i = eₜ' (Finsupp.single i 1)`. Both sides reduce to the same expression. Rewrite using `[h1]`. Use `trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1`.

Simplify using `[eₜ', -IsLocalizedModule.map_apply, l₁ₜ]`. Simplify using `[l₂ₜ, e]`. Set `eκ : κ ≃ Fin (Nat.card κ)` to `Finite.equivFin κ`. Use `⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩` and prove the remaining obligations. Establish `hg' : ε g ∉ maximalIdeal R` using `hg`.

Conclude with `(IsLocalRing.notMem_maximalIdeal.mp hg')`. Unfold `EtChart`. Use `letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) := ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra`. Use `show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)`. Establish `hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)` using `IsScalarTower.of_algebraMap_eq fun r => by`.

Express the relevant statement in the definitionally equal form `algebraMap R (Localization.Away g) r = algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))`. Rewrite using `[MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]`. Establish `hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) = algebraMap A (Localization.Away g) (t (eκ.symm i))`. Introduce `i`. Express the relevant statement in the definitionally equal form `algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _`.

Rewrite using `[MvPolynomial.aeval_X]`. Both sides reduce to the same expression. Use `haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)`. Use `haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)`. Set `P` to `MvPolynomial (Fin (Nat.card κ)) R`.

Set `bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R])` to `(mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)`. Set `bB'` to `bB.reindex eκ`. Establish `hbij : Function.Bijective (mapBaseChange R P (Localization.Away g))`. Establish `: mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap`. Use `bP.ext fun i => ?_` and prove the remaining obligations.

Rewrite using `[LinearEquiv.coe_coe, Module.Basis.equiv_apply]`. Simplify using `[bP, bB', hbB, ← hX, P]`. Rewrite using `[this]`. Conclude with `(bP.equiv bB' (Equiv.refl _)).bijective`. Use `haveI : Algebra.FormallyEtale P (Localization.Away g) := formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij`.

Use `haveI : Algebra.FinitePresentation R (Localization.Away g) := Algebra.FinitePresentation.trans R A (Localization.Away g)`. Use `haveI : Algebra.FinitePresentation P (Localization.Away g) := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem exists_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  intro R _ _ A _ _ _ ε
  classical
  let p : Ideal A := (maximalIdeal R).comap ε
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let t : κ → A := fun i => a i - algebraMap R A (ε (a i))
  have hDt : ∀ i, D R A (t i) = D R A (a i) := by intro i; simp [t]
  have hεt : ∀ i, ε (t i) = 0 := by intro i; simp [t]
  let e : (κ →₀ A) →ₗ[A] Ω[A⁄R] :=
    Finsupp.linearCombination A fun i : κ ↦ D R A (t i)
  let l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R] := map R R A (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, hDt]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] :=
    map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i)) := by
    intro i
    have h1 : bB i = eₜ' (Finsupp.single i 1) := by
      rfl
    rw [h1]
    trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1
    · simp [eₜ', -IsLocalizedModule.map_apply, l₁ₜ]
    · simp [l₂ₜ, e]
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩
  · have hg' : ε g ∉ maximalIdeal R := hg
    exact (IsLocalRing.notMem_maximalIdeal.mp hg')
  · unfold EtChart
    letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra
    show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)
    have hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R (Localization.Away g) r =
          algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
    have hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) =
        algebraMap A (Localization.Away g) (t (eκ.symm i)) := by
      intro i
      change algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X]; rfl
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)
    let P := MvPolynomial (Fin (Nat.card κ)) R
    let bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R]) :=
      (mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)
    let bB' := bB.reindex eκ
    have hbij : Function.Bijective (mapBaseChange R P (Localization.Away g)) := by
      have : mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap := by
        refine bP.ext fun i => ?_
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bP, bB', hbB, ← hX, P]
      rw [this]
      exact (bP.equiv bB' (Equiv.refl _)).bijective
    haveI : Algebra.FormallyEtale P (Localization.Away g) :=
      formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.trans R A (Localization.Away g)
    haveI : Algebra.FinitePresentation P (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)
    exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.DenseSec
