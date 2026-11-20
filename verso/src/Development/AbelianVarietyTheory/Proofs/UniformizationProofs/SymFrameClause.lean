import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.SymFrameClause

/- English proof (translation)
Establish `hLaw : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hL` using `A.isLB`. Set `T` to `TFK (R := R) F`. Establish `: Subsingleton T.left` using `inferInstanceAs (Subsingleton (PrimeSpectrum F))`. Take `⟨p⟩ : Nonempty T.left` from `inferInstanceAs (Nonempty (PrimeSpectrum F))`.

Establish `hu : IsUnit ((N : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤))`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm`. Rewrite using `[← map_natCast e]`. Use `(IsUnit.mk0 _ ?_).map e` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap R (FractionRing R))]`.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (Nat.cast_ne_zero.2 hN.pos.ne')`. Take `⟨hex, -⟩` from `hLaw.symLift _ A N hN hu T x hx`. Take `⟨V, hV, θ₀, hθ₀⟩` from `hex p`. Take `⟨h, hh⟩` from `GlobalLift.exists_section (T := T) hV`. Take `⟨θ, hθ⟩` from `GlobalLift.exists_symLift_pull hL h hθ₀`.

Rewrite `hθ` using `[← Category.assoc, hh, Category.id_comp]`. Conclude with `⟨θ, hθ⟩`.
-/
theorem exists_symLift (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N : ℕ) (hN : Odd N) (x : TFK (R := R) F ⟶ A.A) (hx : x ^ N = 1) :
    ∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N x θ := by
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((N : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 hN.pos.ne')
  obtain ⟨hex, -⟩ := hLaw.symLift _ A N hN hu T x hx
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  exact ⟨θ, hθ⟩

/- English proof (translation)
Introduce `R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN p`. Use `⟨GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R I hI D F N hN p, fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨f, hf, hpow⟩` from `GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN.pos`. Use `exists_symLift R A F N hN x ?_` and prove the remaining obligations. Rewrite using `[(hf.1 p x).1 hx]`.

Conclude with `hpow p`. Conclude with `GlobalTheory.UT.symLift_acts_as_phi GlobalTheory.firstFiveLaws R I hI D A G hG U F N hN p x hx`.
-/
theorem symFrame_clause : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.SymFrame U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN p
  refine ⟨GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R I hI D F N hN p, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hpow⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN.pos
    refine exists_symLift R A F N hN x ?_
    rw [(hf.1 p x).1 hx]
    exact hpow p
  · exact GlobalTheory.UT.symLift_acts_as_phi GlobalTheory.firstFiveLaws R I hI D A G hG U F N hN p x hx

end GlobalTheory.SymFrameClause
