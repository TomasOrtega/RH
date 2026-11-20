import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemIdVOfLines
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimAtOfMonoId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatOStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.SeeSaw
open scoped Pointwise

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Take `⟨_hc, he, -⟩` from `hF.hJ ρ h`. Establish `e1 : colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) * (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p))`. Use function extensionality and compare the values at `k`. Simplify using `only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]`. Rewrite using `[e1]`.

Establish `e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1))` using `G.sp.colLat (2 * ρ + 1) (by omega) (by omega)`. Rewrite using `[e2]`. Conclude with `(GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a).2 ha`.
-/
theorem lineV (F : GlobalTheory.Asc.Frames G) (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (p : Fin ρ) (v : Pl D) (a : AE D)
    (ha : a ∈ idV (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)) v) :
    colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  obtain ⟨_hc, he, -⟩ := hF.hJ ρ h
  have e1 : colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
      (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
  rw [e1]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  rw [e2]
  exact (GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
    (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a).2 ha

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨_hc, he, -⟩` from `hF.hB σ h'`. Take `⟨hsupp, hsm⟩` from `GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul _ _ I v y hy`. Establish `hc : ((F.dB σ h').pX *ᵥ y) p ∈ idAt D (· = v)`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hsupp k)`.

Establish `hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)`. Establish `hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (by`. Unfold `Places.modulBar`. Introduce `h0`. Apply `G.pl.modul_ne_bot sc` to reduce the goal to its premises.

Establish `h1` using `congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0`. Simplify using `using h1)`. Establish `hA : G.pl.stA sc ≠ 0` using `mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')`. Establish `hB : G.pl.stAbar sc ≠ 0` using `mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)`. Establish `hb : FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p) ≠ 0` using `mul_ne_zero (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))) (mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))`.

Establish `key` using `(GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v I⁻¹ _ (inv_ne_zero hI) hb _ hc).1 fun s hs => by`. Establish `h1` using `((hm _).1 (hsm s hs)).1 p`. Rewrite `h1` using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Establish `e1 : colMul (F.dB σ h').jX p (s * ((F.dB σ h').pX *ᵥ y) p) = fun k => s * ((F.dB σ h').pX *ᵥ y) p * incA D ((-D.host.xi0) ^ (p.1 + 1) * (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))`. Use function extensionality and compare the values at `k`.

Simplify using `only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]`. Rewrite `h1` using `[e1]`. Establish `e2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat (G.Λ (.core (2 * σ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1))` using `G.sp.colLat (2 * σ + 2) (by omega) h'`. Rewrite `h1` using `[e2]`. Rewrite using `[mul_comm (((F.dB σ h').pX *ᵥ y) p) s]`.

Conclude with `(GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v _).1 h1`. Rewrite `key` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem lineW (F : GlobalTheory.Asc.Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (v : Pl D)
    (hm : MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v) (p : Fin σ) (I : FI D) (hI : I ≠ 0)
    (y : Fin (G.V (.grid (2 * σ + 2) 0)).rank → AE D) (hy : y ∈ latMul _ {a | a ∈ I} (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) :
    ((F.dB σ h').pX *ᵥ y) p ∈ idV (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p) * I) v := by
  obtain ⟨_hc, he, -⟩ := hF.hB σ h'
  obtain ⟨hsupp, hsm⟩ := GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul _ _ I v y hy
  have hc : ((F.dB σ h').pX *ᵥ y) p ∈ idAt D (· = v) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hsupp k)
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      unfold Places.modulBar
      intro h0
      apply G.pl.modul_ne_bot sc
      have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
      simpa using h1)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hb : FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p) ≠ 0 :=
    mul_ne_zero (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
      (mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key := (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v I⁻¹ _ (inv_ne_zero hI) hb _ hc).1 fun s hs => by
    have h1 := ((hm _).1 (hsm s hs)).1 p
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
    have e1 : colMul (F.dB σ h').jX p (s * ((F.dB σ h').pX *ᵥ y) p) = fun k => s * ((F.dB σ h').pX *ᵥ y) p *
        incA D ((-D.host.xi0) ^ (p.1 + 1) * (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1] at h1
    have e2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat (G.Λ (.core (2 * σ + 2)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) := G.sp.colLat (2 * σ + 2) (by omega) h'
    rw [e2] at h1
    rw [mul_comm (((F.dB σ h').pX *ᵥ y) p) s]
    exact (GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v _).1 h1
  rwa [inv_inv] at key

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.SeeSaw
open scoped Pointwise

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA1 v hv i j hij`. Take `⟨-, -, -, -, f5, -, -⟩` from `GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v`. Establish `hiσ : i.1 < σ` using `by have := j.2; omega`. Establish `hii : (⟨i.1, hiσ⟩ : Fin σ).castSucc = i` using `Fin.ext rfl`. Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`.

Establish `e0 : u.1.1 i j = (u.1.1 - 1) i j` using `by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Rewrite using `[e0]`. Use `set N := u.1.1 - 1 with hNdef`. Use `set s := idem D (· = v) * N i j with hsdef`. Establish `hs : s ∈ idAt D (· = v)` using `Ideal.mul_mem_right _ _ (idem_mem_idAt _)`.

Establish `hN0 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)`. Establish `hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (by`. Unfold `Places.modulBar`. Introduce `h0`. Apply `G.pl.modul_ne_bot sc` to reduce the goal to its premises.

Establish `h1` using `congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0`. Simplify using `using h1)`. Establish `hAA : D.host.AA ≠ 0` using `GlobalTheory.CuspCharLattice.host_AA_ne_zero _`. Establish `hA : G.pl.stA sc ≠ 0` using `mul_ne_zero hAA (inv_ne_zero hN')`. Establish `hB : G.pl.stAbar sc ≠ 0` using `mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN0)`.

Establish `hx : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0` using `fun n => by`. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))`. Establish `hst : ∀ c (p : Fin c), stairId (G.pl.stA sc) (G.pl.stAbar sc) c p ≠ 0` using `fun c p => mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))`. Use `set 𝔟V : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) (Fin.castLE (by omega) j) with h𝔟V`.

Establish `hbV : 𝔟V ≠ 0` using `mul_ne_zero (hx _) (hst _ _)`. Establish `hV : ∀ a ∈ idV 𝔟V v, colMul (F.dJ (σ + 1) h).jX j a ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v)` using `fun a ha => lineV F hF (σ + 1) h j v a ha`. Establish `hsupp : ∀ a ∈ idV 𝔟V v, a ∈ idAt D (· = v)` using `fun a ha => GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul (F.dJ (σ + 1) h) (hV a ha)`. Establish `hmW` using `(((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 σ h').2.1 v).1`. Use `set 𝔟W1 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) * D.host.AA with h𝔟W1`.

Use `set 𝔟W2 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) with h𝔟W2`. Establish `hbW1 : 𝔟W1 ≠ 0` using `mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hAA`. Establish `hbW2 : 𝔟W2 ≠ 0` using `mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hN0`. Establish `hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2)` using `hA1`. Establish `eY : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') = xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX` using `by show (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX = _`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`. Establish `hloc` using `GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow`. Establish `sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0))` using `(G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd`. Establish `sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0))` using `(G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd`. Establish `hmem` using `((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2`.

Establish `hY1 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v), (xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈ latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v)`. Introduce `y hy`. Establish `h1` using `hmem y hy`. Establish `hyid` using `latV_idAt hy`. Establish `ey : idem D (· = v) • y = y` using `funext fun k => (mem_idAt_iff _ _).1 (hyid k)`.

Rewrite `h1` using `[eY, Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey]`. Then use the resulting hypothesis. Establish `r1` using `mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ (latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) 𝔟V 𝔟W1 ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ D.host.AA hAA y hy) N hY1`. Rewrite `r1` using `[hii]`. Establish `hs1 : s ∈ idV (𝔟W1 * 𝔟V⁻¹) v` using `(GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W1 hbV hbW1 s hs).1 fun a ha => by`. Rewrite using `[hsdef, mul_comm (idem D (· = v)) (N i j), mul_assoc, (mem_idAt_iff _ a).1 (hsupp a ha)]`.

Conclude with `r1 a ha`. Take `⟨e, he, -⟩` from `W.cosVec_is`. Establish `hY2 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v), (xFB F σ h' ⬝ (e • N) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈ latMul _ {a | a ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)} (G.Λ (.grid (2 * σ + 2) 0)) (· = v)`. Introduce `y hy`. Establish `h1` using `GlobalTheory.T.depthLatticeRow_mulVec_mem_modulus_scaledCompletion D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) e he _ hrow v y hy`.

Rewrite `h1` using `[eY, ← Matrix.smul_mul, ← Matrix.mul_smul]`. Then use the resulting hypothesis. Establish `r2` using `mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ 𝔟V 𝔟W2 ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ _ hN0 y hy) (e • N) hY2`. Rewrite `r2` using `[hii]`. Establish `hs2 : e * s ∈ idV (𝔟W2 * 𝔟V⁻¹) v` using `(GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W2 hbV hbW2 (e * s) (Ideal.mul_mem_left _ _ hs)).1 fun a ha => by`. Establish `h3` using `r2 a ha`.

Rewrite `h3` using `[Matrix.smul_apply, smul_eq_mul]`. Establish `e4 : e * s * a = e * N i j * (idem D (· = v) * a)` using `by rw [hsdef]; ring`. Rewrite using `[e4, (mem_idAt_iff _ a).1 (hsupp a ha)]`. Conclude with `h3`. Establish `e5 : 2 * (σ + 1) + 1 - 1 - j.1 = 2 * σ + 2 - 1 - i.1` using `by omega`.

Establish `q1 : 𝔟W1 * 𝔟V⁻¹ = dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹`. Rewrite using `[h𝔟W1, h𝔟V]`. Simplify using `only [stairId, Fin.val_castLE]`. Rewrite using `[e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, dI, Places.stAbar]`. Expand and normalize the polynomial expressions, which then agree.

Establish `q2 : 𝔟W2 * 𝔟V⁻¹ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar`. Rewrite using `[h𝔟W2, h𝔟V]`. Simplify using `only [stairId, Fin.val_castLE]`. Rewrite using `[e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, Places.stAbar]`. Rewrite using `[show ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * (D.host.AAbar * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar * (((G.pl.modul sc : Ideal (𝓞 D. …`.

Rewrite `hs1` using `[q1]`. Rewrite `hs2` using `[q2]`. Establish `hdI` using `GlobalTheory.T.ideal_membership_off_modulus D hq T L μ0 hL sc G W M hM v hv e he s hs hs1 hs2`. Establish `h6` using `(f5 s hs).1 hdI (idem D (· = v)) (idem_mem_intAt _)`. Rewrite `h6` using `[hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self]`. Then use the resulting hypothesis.
-/
theorem unipotent_character_trivial_at_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → ∀ v ∈ G.pl.S0, ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * u.1.1 i j) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA1 v hv i j hij
  obtain ⟨-, -, -, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v
  have hiσ : i.1 < σ := by have := j.2; omega
  have hii : (⟨i.1, hiσ⟩ : Fin σ).castSucc = i := Fin.ext rfl
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have e0 : u.1.1 i j = (u.1.1 - 1) i j := by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [e0]
  set N := u.1.1 - 1 with hNdef
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have hN0 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      unfold Places.modulBar
      intro h0
      apply G.pl.modul_ne_bot sc
      have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
      simpa using h1)
  have hAA : D.host.AA ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero hAA (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN0)
  have hx : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))
  have hst : ∀ c (p : Fin c), stairId (G.pl.stA sc) (G.pl.stAbar sc) c p ≠ 0 := fun c p =>
    mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

  set 𝔟V : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) (Fin.castLE (by omega) j) with h𝔟V
  have hbV : 𝔟V ≠ 0 := mul_ne_zero (hx _) (hst _ _)
  have hV : ∀ a ∈ idV 𝔟V v, colMul (F.dJ (σ + 1) h).jX j a ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v) :=
    fun a ha => lineV F hF (σ + 1) h j v a ha
  have hsupp : ∀ a ∈ idV 𝔟V v, a ∈ idAt D (· = v) := fun a ha =>
    GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul (F.dJ (σ + 1) h) (hV a ha)
  have hmW := (((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 σ h').2.1 v).1
  set 𝔟W1 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) * D.host.AA with h𝔟W1
  set 𝔟W2 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) *
    ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) with h𝔟W2
  have hbW1 : 𝔟W1 ≠ 0 := mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hAA
  have hbW2 : 𝔟W2 ≠ 0 := mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hN0

  have hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2) := hA1
  have eY : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') = xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX := by
    show (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX = _
    rw [Matrix.mul_sub, Matrix.mul_one]

  have hloc := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow
  have sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have hmem := ((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2
  have hY1 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v),
      (xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈ latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro y hy
    have h1 := hmem y hy
    have hyid := latV_idAt hy
    have ey : idem D (· = v) • y = y := funext fun k => (mem_idAt_iff _ _).1 (hyid k)
    rwa [eY, Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey] at h1
  have r1 := mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ (latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) 𝔟V 𝔟W1
    ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ D.host.AA hAA y hy) N hY1
  rw [hii] at r1
  have hs1 : s ∈ idV (𝔟W1 * 𝔟V⁻¹) v := (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W1 hbV hbW1 s hs).1 fun a ha => by
    rw [hsdef, mul_comm (idem D (· = v)) (N i j), mul_assoc, (mem_idAt_iff _ a).1 (hsupp a ha)]
    exact r1 a ha

  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hY2 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v),
      (xFB F σ h' ⬝ (e • N) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈
        latMul _ {a | a ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)} (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro y hy
    have h1 := GlobalTheory.T.depthLatticeRow_mulVec_mem_modulus_scaledCompletion D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) e he _ hrow v y hy
    rwa [eY, ← Matrix.smul_mul, ← Matrix.mul_smul] at h1
  have r2 := mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ 𝔟V 𝔟W2
    ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ _ hN0 y hy) (e • N) hY2
  rw [hii] at r2
  have hs2 : e * s ∈ idV (𝔟W2 * 𝔟V⁻¹) v :=
    (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W2 hbV hbW2 (e * s) (Ideal.mul_mem_left _ _ hs)).1 fun a ha => by
      have h3 := r2 a ha
      rw [Matrix.smul_apply, smul_eq_mul] at h3
      have e4 : e * s * a = e * N i j * (idem D (· = v) * a) := by rw [hsdef]; ring
      rw [e4, (mem_idAt_iff _ a).1 (hsupp a ha)]
      exact h3

  have e5 : 2 * (σ + 1) + 1 - 1 - j.1 = 2 * σ + 2 - 1 - i.1 := by omega
  have q1 : 𝔟W1 * 𝔟V⁻¹ = dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹ := by
    rw [h𝔟W1, h𝔟V]
    simp only [stairId, Fin.val_castLE]
    rw [e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, dI, Places.stAbar]
    ring
  have q2 : 𝔟W2 * 𝔟V⁻¹ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar := by
    rw [h𝔟W2, h𝔟V]
    simp only [stairId, Fin.val_castLE]
    rw [e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, Places.stAbar]
    rw [show ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 *
        (D.host.AAbar * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) =
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar *
          (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) by ring,
      mul_inv_cancel₀ hN0, mul_one]
  rw [q1] at hs1
  rw [q2] at hs2
  have hdI := GlobalTheory.T.ideal_membership_off_modulus D hq T L μ0 hL sc G W M hM v hv e he s hs hs1 hs2
  have h6 := (f5 s hs).1 hdI (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij`. Take `⟨hgood, -⟩` from `GlobalTheory.T.standard_frames_successive_levels D hq T L μ0 hL sc G W M hM F hF σ h h' v hv`. Establish `hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2)` using `hA`. Establish `hloc` using `GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow`. Establish `sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0))` using `(G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd`.

Establish `sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0))` using `(G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd`. Establish `hmem` using `((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2`. Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`. Establish `e0 : u.1.1 i j = (u.1.1 - 1) i j` using `by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Rewrite using `[e0]`.

Apply the tactic sequence `refine psiE_idem_entry W.ψ_std (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ _ hgood.monoW hgood.prim hgood.cols _ ?_ i j hij`. Introduce `y hy`. Establish `h1` using `hmem y hy`. Establish `e1 : (idem D (· = v) • (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h')) *ᵥ y = (xFB F σ h' ⬝ (u.1.1 - 1) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y`. Establish `hyid` using `latV_idAt hy`.

Establish `ey : idem D (· = v) • y = y` using `funext fun k => (mem_idAt_iff _ _).1 (hyid k)`. Rewrite using `[Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey]`. Use `show ((xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y = _`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`. Rewrite `h1` using `[e1]`. Then use the resulting hypothesis.
-/
theorem unipotent_character_trivial_off_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u : UX D (σ + 1), xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → ∀ v ∉ G.pl.S0,
      ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (idem D (· = v) * u.1.1 i j) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij
  obtain ⟨hgood, -⟩ := GlobalTheory.T.standard_frames_successive_levels D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  have hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2) := hA
  have hloc := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow
  have sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have hmem := ((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have e0 : u.1.1 i j = (u.1.1 - 1) i j := by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [e0]
  refine psiE_idem_entry W.ψ_std (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ _ hgood.monoW hgood.prim hgood.cols _ ?_ i j hij
  intro y hy
  have h1 := hmem y hy
  have e1 : (idem D (· = v) • (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h')) *ᵥ y =
      (xFB F σ h' ⬝ (u.1.1 - 1) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y := by
    have hyid := latV_idAt hy
    have ey : idem D (· = v) • y = y := funext fun k => (mem_idAt_iff _ _).1 (hyid k)
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey]
    show ((xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y = _
    rw [Matrix.mul_sub, Matrix.mul_one]
  rwa [e1] at h1

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA`. Establish `key : ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1` using `fun i j hij => by`. Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`. Establish `hs : u.1.1 i j ∈ idAt D (fun _ => True)`. Use `hu i j` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Then use the resulting hypothesis. Use `PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 hs fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ G.pl.S0`. Conclude with `unipotent_character_trivial_at_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA v hv i j hij`. Conclude with `unipotent_character_trivial_off_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij`.

Unfold `psiUni upSum`. Use `Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul]) (psiE_zero W.ψ) fun i _ => ?_` and prove the remaining obligations. Use `Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul]) (psiE_zero W.ψ) fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hij`. Conclude with `key i j hij`.

Conclude with `psiE_zero W.ψ`.
-/
theorem psiUni_pcFB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ →
      psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA
  have key : ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have hs : u.1.1 i j ∈ idAt D (fun _ => True) := by
      have := hu i j
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    refine PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 hs fun v _ => ?_
    by_cases hv : v ∈ G.pl.S0
    · exact unipotent_character_trivial_at_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA v hv i j hij
    · exact unipotent_character_trivial_off_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero W.ψ

end GlobalTheory.UniStepFB
