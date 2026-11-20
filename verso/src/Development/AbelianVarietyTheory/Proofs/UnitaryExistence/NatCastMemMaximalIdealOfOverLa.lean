import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

open IsDedekindDomain

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_prime_mem_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem natCast_mem_maximalIdeal_of_overLa {K : Type} [Field K] [NumberField K]
    {la : HeightOneSpectrum (𝓞 K)} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {io : K →+* K'} {e : ℕ} (ho : OverLa la V io e)
    {n : ℕ} (hn : n ≠ 0) (hmem : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal) :
    (n : V) ∈ IsLocalRing.maximalIdeal V := by
  by_contra hV
  have hK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn
  have h1 : valV V ((n : ℕ) : K') = 1 := by
    have h : ((n : ℕ) : K') = algebraMap V K' (n : V) := (map_natCast _ n).symm
    rw [valV, h]
    apply le_antisymm (HeightOneSpectrum.valuation_le_one _ _)
    rw [← not_lt, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hV
  have h2 : la.valuation K ((n : ℕ) : K) < 1 := by
    have h : ((n : ℕ) : K) = algebraMap (𝓞 K) K (n : 𝓞 K) := (map_natCast _ n).symm
    rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have h3 : WithZero.log (la.valuation K ((n : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 hK) one_ne_zero).2 h2
    simpa using this
  have h4 := ho.2 ((n : ℕ) : K)
  rw [map_natCast, vV, h1, vLa, WithZero.log_one] at h4
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos he (neg_pos.2 h3)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem modelAtSt_of_good : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ la, Formalism.L2.Pj.ModelAtSt Xo c la := by
  intro hP hN E _ _ _ H Dw l Xo c hpq hg la
  exact Formalism.L2.Pj.modelAtSt_of (Formalism.L2.Pj.partIAt_of hP hN Xo c hpq) hg la

end GlobalTheory.Frames
