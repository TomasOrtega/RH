import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafDimBoundPf

/- English proof (translation)
Use `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_` and prove the remaining obligations. Introduce `P Q hPQ`. Establish `hle : P.asIdeal ≤ Q.asIdeal` using `hPQ.le`. Use `lt_of_le_of_ne (fun x hx => hle hx) ?_` and prove the remaining obligations. Introduce `h`.

Apply `hPQ.ne` to reduce the goal to its premises. Use `Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle (congrArg PrimeSpectrum.asIdeal h)` as an intermediate fact. Conclude with `PrimeSpectrum.ext this`.
-/
theorem dim_le_of_quasiFinite (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.QuasiFinite A S] : ringKrullDim S ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := hPQ.le
  refine lt_of_le_of_ne (fun x hx => hle hx) ?_
  intro h
  apply hPQ.ne
  have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)
  exact PrimeSpectrum.ext this

/- English proof (translation)
Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S`. Set `_ : Algebra (MvPolynomial (Fin 1) R) S` to `g.toRingHom.toAlgebra`. Establish `: Algebra.Etale (MvPolynomial (Fin 1) R) S` using `hg`. Establish `h1` using `dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S`. Rewrite `h1` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing]`.

Simplify using `using h1`.
-/
theorem dim_le_of_stdSmooth1 (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] : ringKrullDim S ≤ ringKrullDim R + 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S
  let _ : Algebra (MvPolynomial (Fin 1) R) S := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) R) S := hg
  have h1 := dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at h1
  simpa using h1

/- English proof (translation)
Establish `h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V))` using `(Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq`. Rewrite using `[h1]`. Conclude with `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _`.
-/
theorem dim_affineOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim (V : Set X) = ringKrullDim Γ(X, V) := by
  have h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V)) :=
    (Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq
  rw [h1]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/- English proof (translation)
Rewrite using `[← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]`. Conclude with `topologicalKrullDim_subspace_le _ _`.
-/
theorem dim_affineOpen_Spec_le (A : CommRingCat.{0}) {U : (Spec A).Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(Spec A, U) ≤ ringKrullDim A := by
  rw [← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]
  exact topologicalKrullDim_subspace_le _ _

/- English proof (translation)
Introduce `k _ Ω _ _ R hR D0 q hq`. Establish `: IsNoetherianRing R` using `isNoetherianRing_of_fg hR`. Apply `GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen` to reduce the goal to its premises. Introduce `x`. Take `⟨U, hU, V, hV, hx, e, hs⟩` from `hq.exists_isStandardSmoothOfRelativeDimension x`.

Establish `: IsNoetherianRing Γ(Sp R, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `_ : Algebra Γ(Sp R, U) Γ(D0, V)` to `(q.appLE U V e).hom.toAlgebra`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V)` using `hs`. Use `⟨(V : Set D0), V.isOpen, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[dim_affineOpen hV]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `dim_affineOpen_Spec_le (CommRingCat.of R) hU`.
-/
theorem LeafDimBound_of : LateralTheory.E.LeafDescendVCut.LeafDimBound := by
  intro k _ Ω _ _ R hR D0 q hq
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := hq.exists_isStandardSmoothOfRelativeDimension x
  have : IsNoetherianRing Γ(Sp R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Sp R, U) Γ(D0, V) := (q.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V) := hs
  refine ⟨(V : Set D0), V.isOpen, hx, ?_⟩
  rw [dim_affineOpen hV]
  calc ringKrullDim Γ(D0, V) ≤ ringKrullDim Γ(Sp R, U) + 1 := dim_le_of_stdSmooth1 _ _
    _ ≤ ringKrullDim R + 1 := by
      gcongr
      exact dim_affineOpen_Spec_le (CommRingCat.of R) hU

end LateralTheory.E.LeafDimBoundPf
