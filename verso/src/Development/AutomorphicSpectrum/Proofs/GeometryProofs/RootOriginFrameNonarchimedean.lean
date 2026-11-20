import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VVAlgNonneg
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev _ _ hGood la T io e y evT zT t hInt zV hR hu`. Take `⟨-, -, hinv⟩` from `hu`. Take `⟨s, hs⟩` from `RingHom.mem_range.1 hinv`. Establish `hgen : IsCptGen Or.𝔐.ξ` using `Or.𝔐.tie.gen`. Establish `hv : ValAt Or.𝔐.ξ zV ((p : RM.Ω)⁻¹) ((Scheme.stalkClosedPointTo zV).hom s)` using `⟨Or.𝔐.all _, s, hs, rfl⟩`.

Establish `hv'` using `LieTangent.valAt_base hgen (algebraMap T.V T.Fr) hv`. Establish `hcst : Or.𝔐.cst ((p : c.F)⁻¹) = (p : RM.Ω)⁻¹` using `by simp`. Establish `hmem` using `hGood.1 ((p : c.F)⁻¹)`. Establish `hla : (p : 𝓞 c.F) ∈ la.asIdeal` using `hInt.1`. Establish `hOver : OverLa la T.V io e` using `hInt.2.1`.

Establish `hev : evT ⟨_, hmem⟩ = io ((p : c.F)⁻¹)` using `hInt.2.2.2.2.1 _ hmem`. Establish `hr` using `hR ⟨_, hmem⟩`. Rewrite `hr` using `[hev]`. Express the relevant statement in the definitionally equal form `ValAt _ _ (Or.𝔐.cst ((p : c.F)⁻¹)) _ at hr`. Rewrite `hr` using `[hcst]`.

Establish `heq` using `LieTangent.valAt_unique hgen hv' hr`. Establish `hp0 : (p : c.F) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Establish `h1 : la.valuation c.F (p : c.F) < 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 c.F) c.F)]`. Conclude with `(la.valuation_lt_one_iff_mem _).2 hla`.

Establish `h2` using `(WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1`. Rewrite `h2` using `[WithZero.log_one]`. Establish `h3 : 0 < vLa la (p : c.F)` using `by unfold vLa; omega`. Establish `h4 : 0 < vV T.V (io (p : c.F))`. Rewrite using `[hOver.2]`.

Conclude with `mul_pos (by exact_mod_cast hOver.1) h3`. Establish `h5 : vV T.V (io ((p : c.F)⁻¹)) = - vV T.V (io (p : c.F))`. Simplify using `[vV, map_inv₀]`. Establish `h6` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.vV_alg_nonneg T ((Scheme.stalkClosedPointTo zV).hom s)`. Rewrite `h6` using `[heq, h5]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem inFibre_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev _ _ hGood la T io e y evT zT t hInt zV hR hu
  obtain ⟨-, -, hinv⟩ := hu
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 hinv
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hv : ValAt Or.𝔐.ξ zV ((p : RM.Ω)⁻¹) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨Or.𝔐.all _, s, hs, rfl⟩
  have hv' := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) hv
  have hcst : Or.𝔐.cst ((p : c.F)⁻¹) = (p : RM.Ω)⁻¹ := by simp
  have hmem := hGood.1 ((p : c.F)⁻¹)
  have hla : (p : 𝓞 c.F) ∈ la.asIdeal := hInt.1
  have hOver : OverLa la T.V io e := hInt.2.1
  have hev : evT ⟨_, hmem⟩ = io ((p : c.F)⁻¹) := hInt.2.2.2.2.1 _ hmem
  have hr := hR ⟨_, hmem⟩
  rw [hev] at hr
  change ValAt _ _ (Or.𝔐.cst ((p : c.F)⁻¹)) _ at hr
  rw [hcst] at hr
  have heq := LieTangent.valAt_unique hgen hv' hr
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : la.valuation c.F (p : c.F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (la.valuation_lt_one_iff_mem _).2 hla
  have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 < vLa la (p : c.F) := by unfold vLa; omega
  have h4 : 0 < vV T.V (io (p : c.F)) := by
    rw [hOver.2]
    exact mul_pos (by exact_mod_cast hOver.1) h3
  have h5 : vV T.V (io ((p : c.F)⁻¹)) = - vV T.V (io (p : c.F)) := by
    simp [vV, map_inv₀]
  have h6 := ReciprocityTheory.ChartRestriction.G.PullbackSections.vV_alg_nonneg T ((Scheme.stalkClosedPointTo zV).hom s)
  rw [heq, h5] at h6
  omega

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
