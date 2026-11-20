import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedSpaceLeSupEigenspaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
/- English proof (translation)
Introduce `D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P hk`. Take `⟨hj1, hj2, hk1, hk2, hsp, hP0⟩` from `hk`. Establish `hPSb : P ∉ In.Sb`. Introduce `h`. Apply `hP0` to reduce the goal to its premises.

Establish `h1 : P ∈ (T.S0 i : Set (PlE D.host))`. Rewrite using `[Sp.ringSpec_excludedPlaces_eq i]`. Conclude with `Or.inr (hSb h)`. Conclude with `h1`. Establish `hZ` using `GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide D T S In i j b k P hj1 hj2 (GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector D S In j k P hj1 hj2 hk1 hk2 hsp hPSb)`.

Establish `hker : V0T D T S In.rho In.chi In.θ i j b ≤ LinearMap.ker (phiKop D T S In i j b k P)`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`. Use `LinearMap.congr_fun hZ y` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix D T S In i j b y hy]`.

Conclude with `this`. Use `hker.trans ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (readT D T i b)` using `(readT D T i b).injective`. Establish `hpol : (evPol D S In j k P).map (readT D T i b) = ∏ r ∈ (evRoots D S In j k P).image (readT D T i b), (X - C r)`. Rewrite using `[evPol, Polynomial.map_prod, Finset.prod_image (fun x _ y _ h => hinj h)]`.

Simplify using the standard rewrite rules. Rewrite using `[phiKop, hpol, GlobalTheory.JointDiag.ker_prod]`. Use `iSup₂_le fun r hr => ?_` and prove the remaining obligations. Take `⟨r0, hr0, rfl⟩` from `Finset.mem_image.mp hr`. Take `⟨σ, hσ, rfl⟩` from `Finset.mem_image.mp hr0`.

Establish `hσ' : σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}` using `(Finset.mem_filter.mp hσ).2`. Use `le_trans ?_ (le_iSup₂_of_le σ hσ' le_rfl)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hkT_eq, LinearMap.smul_apply, hx, smul_smul]`.
-/
theorem v0t_le_supr_eigenspace : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P hk
  obtain ⟨hj1, hj2, hk1, hk2, hsp, hP0⟩ := hk
  have hPSb : P ∉ In.Sb := by
    intro h
    apply hP0
    have h1 : P ∈ (T.S0 i : Set (PlE D.host)) := by
      rw [Sp.ringSpec_excludedPlaces_eq i]
      exact Or.inr (hSb h)
    exact h1
  have hZ := GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide D T S In i j b k P hj1 hj2 (GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector D S In j k P hj1 hj2 hk1 hk2 hsp hPSb)
  have hker : V0T D T S In.rho In.chi In.θ i j b ≤ LinearMap.ker (phiKop D T S In i j b k P) := by
    rintro x ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker]
    have := LinearMap.congr_fun hZ y
    rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix D T S In i j b y hy] at this
    exact this
  refine hker.trans ?_
  classical
  have hinj : Function.Injective (readT D T i b) := (readT D T i b).injective
  have hpol : (evPol D S In j k P).map (readT D T i b) =
      ∏ r ∈ (evRoots D S In j k P).image (readT D T i b), (X - C r) := by
    rw [evPol, Polynomial.map_prod, Finset.prod_image (fun x _ y _ h => hinj h)]
    simp
  rw [phiKop, hpol, GlobalTheory.JointDiag.ker_prod]
  refine iSup₂_le fun r hr => ?_
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hr0
  have hσ' : σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ} := (Finset.mem_filter.mp hσ).2
  refine le_trans ?_ (le_iSup₂_of_le σ hσ' le_rfl)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [hkT_eq, LinearMap.smul_apply, hx, smul_smul]
end GlobalTheory.HeightCounting.FormsStep
end
