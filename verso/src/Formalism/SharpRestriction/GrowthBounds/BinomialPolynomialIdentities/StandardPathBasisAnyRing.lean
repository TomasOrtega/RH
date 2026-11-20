import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv

noncomputable section
open MvPolynomial Finset
open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hT` using `restPathTo`. Establish `hF` using `restPathFrom`. Establish `hS` using `restStd`. Establish `hP` using `restPsi`. Establish `hPol` using `restPol`.

Take `⟨hLI, hSp⟩` from `Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis n N (isV LL) (Bn B) R`. Establish `hinj : Function.Injective (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap` using `rename_injective _ (iv_inj N n)`. Establish `hfun : (fun x : WIdx n N LL B => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap (Psi R x.1.1.mu x.1.2)) = (fun y : Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) => Formalism.InvariantFactorPaths.Gel …`. Use function extensionality and compare the values at `x`. Conclude with `rename_Psi hT hF hS hP R x`.

Prove the components needed by the constructor for the conclusion. Establish `h1` using `hLI.comp (e17 hT hF hS n N LL B) (e17 hT hF hS n N LL B).injective`. Rewrite `h1` using `[← hfun]`. Conclude with `LinearIndependent.of_comp _ h1`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises.

Rewrite using `[hPol R n N B, ← hSp, Submodule.map_span]`. Use `congr 1`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨P, I, hI, rfl⟩, rfl⟩`.

Conclude with `⟨e17 hT hF hS n N LL B ⟨(P, I), hI⟩, (congrFun hfun ⟨(P, I), hI⟩).symm⟩`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨x, rfl⟩` from `(e17 hT hF hS n N LL B).surjective y`. Conclude with `⟨Psi R x.1.1.mu x.1.2, ⟨x.1.1, x.1.2, x.2, rfl⟩, congrFun hfun x⟩`.
-/
theorem standardPath_basis_any_ring (R : Type) [CommRing R] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    LinearIndependent R (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
      Psi R x.1.1.mu x.1.2) ∧
    Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Pol R n B := by
  have hT := restPathTo
  have hF := restPathFrom
  have hS := restStd
  have hP := restPsi
  have hPol := restPol
  obtain ⟨hLI, hSp⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis n N (isV LL) (Bn B) R
  have hinj : Function.Injective
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap :=
    rename_injective _ (iv_inj N n)
  have hfun : (fun x : WIdx n N LL B =>
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap
        (Psi R x.1.1.mu x.1.2)) =
      (fun y : Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) => Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) y.1.1 N y.1.2) ∘
        (e17 hT hF hS n N LL B) := by
    funext x
    exact rename_Psi hT hF hS hP R x
  constructor
  · have h1 := hLI.comp (e17 hT hF hS n N LL B) (e17 hT hF hS n N LL B).injective
    rw [← hfun] at h1
    exact LinearIndependent.of_comp _ h1
  · apply Submodule.map_injective_of_injective hinj
    rw [hPol R n N B, ← hSp, Submodule.map_span]
    congr 1
    ext G
    constructor
    · rintro ⟨_, ⟨P, I, hI, rfl⟩, rfl⟩
      exact ⟨e17 hT hF hS n N LL B ⟨(P, I), hI⟩, (congrFun hfun ⟨(P, I), hI⟩).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e17 hT hF hS n N LL B).surjective y
      exact ⟨Psi R x.1.1.mu x.1.2, ⟨x.1.1, x.1.2, x.2, rfl⟩, congrFun hfun x⟩

/- English proof (translation)
Use `Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.pathIdxFinite n N (isV LL) (Bn B)` as an intermediate fact. Conclude with `Finite.of_equiv _ (e17 restPathTo restPathFrom restStd n N LL B).symm`.
-/
theorem standardPath_index_finite (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Finite {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} := by
  have := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.pathIdxFinite n N (isV LL) (Bn B)
  exact Finite.of_equiv _ (e17 restPathTo restPathFrom restStd n N LL B).symm

end Formalism.MainNotions.G.ColumnFamilies
