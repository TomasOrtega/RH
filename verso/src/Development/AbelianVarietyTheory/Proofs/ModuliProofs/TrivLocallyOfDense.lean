import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFieldPullbackAppTopBijectiveAndTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawReduced

/- English proof (translation)
Introduce `R _ _ X f M hM hSm hPr hGI hPB hD p`. Use `haveI := hPr`. Use `haveI := hGI`. Establish `hP : Nonempty (Perf f M)` using `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB M hM`. Establish `hQ : Nonempty (Perf f (pw M (-1)))` using `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB _ (isLB_pw hM (-1))`.

Establish `hC` using `GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI`. Establish `hAll` using `hD.closure_eq.symm.trans hC.closure_eq`. Establish `hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}`. Introduce `q`. Rewrite using `[← hAll]`.

Conclude with `Set.mem_univ q`. Take `⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩` from `hmem p`. Take `⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩` from `GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr`. Take `⟨r, I, hr, -, hI⟩` from `GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀`. Use `⟨r, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hrp`. Apply `hr` to reduce the goal to its premises. Establish `hrk : r ∈ RingHom.ker g₀` using `by rw [hk₀, hk]; exact hrp`. Conclude with `RingHom.mem_ker.1 hrk`. Establish `hvan : ∀ x ∈ I, x * r = 0`.

Introduce `x hx`. Apply `IsReduced.eq_zero` to reduce the goal to its premises. Rewrite using `[← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]`. Introduce `J hJ`. Set `q : PrimeSpectrum R` to `⟨J, hJ⟩`.

Distinguish the cases in `hrJ : r ∈ J`. Conclude with `J.mul_mem_left x hrJ`. Apply `J.mul_mem_right r` to reduce the goal to its premises. Take `⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩` from `hmem q`. Establish `hu : IsUnit (gq r)`.

Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `hrk : r ∈ RingHom.ker gq` using `RingHom.mem_ker.2 h0`. Rewrite `hrk` using `[hkq]`. Conclude with `hrJ hrk`.

Use `((hI L gq Xq πq fq hpbq hu).1 htrq) hx` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker]`. Use `show x ∈ q.asIdeal`. Rewrite using `[← hkq]`. Conclude with `this`.

Introduce `R' _ g' X' π f' hpb' hu'`. Use `(hI R' g' X' π f' hpb' hu').2 ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[RingHom.mem_ker]`. Establish `h0 : g' x * g' r = 0` using `by rw [← map_mul, hvan x hx, map_zero]`.

Conclude with `(hu'.mul_left_eq_zero).1 h0`.
-/
theorem triv_locally_of_dense : ∀ (R : Type) [CommRing R] [IsReduced R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Smooth f → IsProper f → GeometricallyIntegral f → IsProjBy f → Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → Triv (M.pull π) := by
  intro R _ _ X f M hM hSm hPr hGI hPB hD p
  haveI := hPr
  haveI := hGI

  have hP : Nonempty (Perf f M) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB M hM
  have hQ : Nonempty (Perf f (pw M (-1))) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB _ (isLB_pw hM (-1))

  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI
  have hAll := hD.closure_eq.symm.trans hC.closure_eq
  have hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K)
      (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
    intro q; rw [← hAll]; exact Set.mem_univ q

  obtain ⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩ := hmem p
  obtain ⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩ :=
    GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr
  obtain ⟨r, I, hr, -, hI⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance
    K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀
  refine ⟨r, ?_, ?_⟩
  · intro hrp
    apply hr
    have hrk : r ∈ RingHom.ker g₀ := by rw [hk₀, hk]; exact hrp
    exact RingHom.mem_ker.1 hrk

  have hvan : ∀ x ∈ I, x * r = 0 := by
    intro x hx
    apply IsReduced.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum R := ⟨J, hJ⟩
    by_cases hrJ : r ∈ J
    · exact J.mul_mem_left x hrJ
    · apply J.mul_mem_right r
      obtain ⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩ := hmem q
      have hu : IsUnit (gq r) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hrk : r ∈ RingHom.ker gq := RingHom.mem_ker.2 h0
        rw [hkq] at hrk
        exact hrJ hrk
      have := ((hI L gq Xq πq fq hpbq hu).1 htrq) hx
      rw [RingHom.mem_ker] at this
      show x ∈ q.asIdeal
      rw [← hkq]; exact this
  intro R' _ g' X' π f' hpb' hu'
  refine (hI R' g' X' π f' hpb' hu').2 ?_
  intro x hx
  rw [RingHom.mem_ker]
  have h0 : g' x * g' r = 0 := by rw [← map_mul, hvan x hx, map_zero]
  exact (hu'.mul_left_eq_zero).1 h0

end GlobalTheory.SeesawReduced
