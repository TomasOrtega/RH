import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellOfIsFrameMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

open MonObj in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx σ C hC`. Establish `hxU : spMap (ev (z ≫ toBase TF Z) U.1 hU) ≫ LogKS.chart U = z ≫ toBase TF Z` using `FlagMod.spMap_ev (z ≫ toBase TF Z) U.2 hU`. Establish `htan : ∀ j, IsTanAtG TF.Y.t (z ≫ toBase TF Z) (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))` using `fun j => by`. Use `GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (z ≫ toBase TF Z) U.1 hU) (hv.1 (e ⟨σ, j⟩))` as an intermediate fact. Rewrite `this` using `[hxU]`. Then use the resulting hypothesis.

Use `choose B hB using fun j => GlobalTheory.FlagEmb.EigSpread.exists_lf (htan j)`. Establish `hsum : ∀ i, ∑ j, C i j • B j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i` using `fun i => by`. Establish `h` using `hC i`. Simplify using `only [← hB] at h`. Conclude with `(GlobalTheory.FlagEmb.EigSpread.comb_lf B (C i) _).1 h`.

Take `⟨Wm, hW⟩` from `TF.X.F.uAt_split k (z ≫ inc₀ TF.X Z) hk σ`. Set `ρ` to `(Matrix.mulVecLin Wm).comp (FlagMod.vec (TF.X.F.M k).toMChart (z ≫ toBase TF Z) (TF.X.F.inM hk hx)).symm.toLinearMap`. Establish `hρ : ∀ i, ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) = Pi.single i 1` using `fun i => by`. Use function extensionality and compare the values at `l`. Establish `h` using `congrFun (congrFun hW l) i`.

Rewrite `h` using `[Matrix.mul_apply]`. Simplify using `only [ρ, FlagMod.Frames.vecAt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[h, Matrix.one_apply, Pi.single_apply]`. Set `B' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z ≫ toBase TF Z) TF.Y.t.G` to `fun j => B j`. Establish `hsum' : ∀ i, ∑ j, C i j • B' j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i` using `hsum`.

Set `D : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S` to `Matrix.of fun j l => ρ (B' j) l`. Establish `hCD : C * D = 1`. Use extensionality with `i l`. Establish `h : ρ (∑ j, C i j • B' j) = ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)` using `congrArg ρ (hsum' i)`. Rewrite `h` using `[hρ, map_sum]`.

Establish `h2` using `congrFun h l`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2`. Establish `h3 : (if i = l then (1 : S) else 0) = (Pi.single i (1 : S) : Fin (Dw.mult σ) → S) l`. Rewrite using `[Pi.single_apply]`. Conclude with `if_congr eq_comm rfl rfl`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply, h3]`. Conclude with `h2`. Conclude with `IsUnit.of_mul_eq_one D.det (by rw [← Matrix.det_mul, hCD, Matrix.det_one])`.
-/
theorem isUnit_det_of_isCombAtG_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx σ C hC
  have hxU : spMap (ev (z ≫ toBase TF Z) U.1 hU) ≫ LogKS.chart U = z ≫ toBase TF Z :=
    FlagMod.spMap_ev (z ≫ toBase TF Z) U.2 hU
  have htan : ∀ j, IsTanAtG TF.Y.t (z ≫ toBase TF Z)
      (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) := fun j => by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (z ≫ toBase TF Z) U.1 hU) (hv.1 (e ⟨σ, j⟩))
    rwa [hxU] at this
  choose B hB using fun j => GlobalTheory.FlagEmb.EigSpread.exists_lf (htan j)
  have hsum : ∀ i, ∑ j, C i j • B j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := fun i => by
    have h := hC i
    simp only [← hB] at h
    exact (GlobalTheory.FlagEmb.EigSpread.comb_lf B (C i) _).1 h
  obtain ⟨Wm, hW⟩ := TF.X.F.uAt_split k (z ≫ inc₀ TF.X Z) hk σ
  let ρ := (Matrix.mulVecLin Wm).comp
    (FlagMod.vec (TF.X.F.M k).toMChart (z ≫ toBase TF Z) (TF.X.F.inM hk hx)).symm.toLinearMap
  have hρ : ∀ i, ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) = Pi.single i 1 := fun i => by
    funext l
    have h := congrFun (congrFun hW l) i
    rw [Matrix.mul_apply] at h
    simp only [ρ, FlagMod.Frames.vecAt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [h, Matrix.one_apply, Pi.single_apply]
  let B' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z ≫ toBase TF Z) TF.Y.t.G := fun j => B j
  have hsum' : ∀ i, ∑ j, C i j • B' j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := hsum
  let D : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := Matrix.of fun j l => ρ (B' j) l
  have hCD : C * D = 1 := by
    ext i l
    have h : ρ (∑ j, C i j • B' j) = ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) := congrArg ρ (hsum' i)
    rw [hρ, map_sum] at h
    have h2 := congrFun h l
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (if i = l then (1 : S) else 0) = (Pi.single i (1 : S) : Fin (Dw.mult σ) → S) l := by
      rw [Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, h3]
    exact h2
  exact IsUnit.of_mul_eq_one D.det (by rw [← Matrix.det_mul, hCD, Matrix.det_one])

end GlobalTheory.LogPole
