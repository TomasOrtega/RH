import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.FlipScalStep

def flipInv {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * incA D ((m : D.host.E)⁻¹) + cA D e * (m : AE D) + (1 - e - cA D e)

/- English proof (translation)
Take `⟨hee, hec, -⟩` from `he`. Establish `hcc : cA D e * cA D e = cA D e` using `by rw [← map_mul, hee]`. Establish `hmE : ((m : D.host.E)) ≠ 0` using `Nat.cast_ne_zero.2 hm`. Establish `hinc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1`. Rewrite using `[← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]`.

Unfold `flipElt flipInv`. Take the linear combination `(e + cA D e) * hinc + ((m : AE D) * incA D ((m : D.host.E)⁻¹) - m - incA D ((m : D.host.E)⁻¹) + 1) * (hee + hcc) + ((m : AE D) ^ 2 - 2 * m + incA D ((m : D.host.E)⁻¹) ^ 2 - 2 * incA D ((m : D.host.E)⁻¹) + 2) * hec`.
-/
theorem flipElt_mul_flipInv {D : D7} {e : AE D} (he : IsSplitIdem D e) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * flipInv e m = 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]
  unfold flipElt flipInv
  linear_combination (e + cA D e) * hinc
    + ((m : AE D) * incA D ((m : D.host.E)⁻¹) - m - incA D ((m : D.host.E)⁻¹) + 1) * (hee + hcc)
    + ((m : AE D) ^ 2 - 2 * m + incA D ((m : D.host.E)⁻¹) ^ 2 - 2 * incA D ((m : D.host.E)⁻¹) + 2) * hec

/- English proof (translation)
Establish `hmul : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1`. Unfold `Formalism.L2.Theta.mt`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `hfb : (flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) * (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = 1`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, flipElt_mul_flipInv he hm, one_smul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mt_inv_eq {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.mt V g⁻¹ = flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hmul : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hfb : (flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) *
      (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, flipElt_mul_flipInv he hm, one_smul]
  calc Formalism.L2.Theta.mt V g⁻¹ = Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g *
        (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))) := by rw [hg, hfb, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hmul, Matrix.one_mul]

/- English proof (translation)
Take `⟨hee, hec, -⟩` from `he`. Establish `hcc : cA D e * cA D e = cA D e` using `by rw [← map_mul, hee]`. Unfold `flipInv`. Take the linear combination `(incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hcc + ((m : AE D) + incA D ((m : D.host.E)⁻¹) - 2) * hec`.
-/
theorem mul_flipInv_sub {D : D7} {e : AE D} (he : IsSplitIdem D e) (m : ℕ) :
    (e + cA D e) * (flipInv e m - 1) = flipInv e m - 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  unfold flipInv
  linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hcc
    + ((m : AE D) + incA D ((m : D.host.E)⁻¹) - 2) * hec

/- English proof (translation)
Take `⟨hee, hec, -⟩` from `he`. Establish `heb : e * flipInv e m = e * incA D ((m : D.host.E)⁻¹)`. Unfold `flipInv`. Take the linear combination `(incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hec`. Proceed by induction on `n with`.

Consider the case `zero => rfl`. Consider the case `succ n ih`. Take the linear combination `flipInv e m * ih + incA D ((m : D.host.E)⁻¹) ^ n * heb`.
-/
theorem idem_mul_flipInv_pow {D : D7} {e : AE D} (he : IsSplitIdem D e) (m n : ℕ) :
    e * flipInv e m ^ n = e * incA D ((m : D.host.E)⁻¹) ^ n := by
  obtain ⟨hee, hec, -⟩ := he
  have heb : e * flipInv e m = e * incA D ((m : D.host.E)⁻¹) := by
    unfold flipInv
    linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hec
  induction n with
  | zero => rfl
  | succ n ih =>
    linear_combination flipInv e m * ih + incA D ((m : D.host.E)⁻¹) ^ n * heb

/- English proof (translation)
Introduce `i j`. Rewrite using `[mt_inv_eq V g e he hm hg, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem suppAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.SuppAt e V g⁻¹ := by
  intro i j
  rw [mt_inv_eq V g e he hm hg, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc (e + cA D e) * (flipInv e m * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      = ((e + cA D e) * (flipInv e m - 1)) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by ring
    _ = _ := by rw [mul_flipInv_sub he m]; ring

/- English proof (translation)
Unfold `Formalism.L2.Theta.IsDetAt`. Rewrite using `[mt_inv_eq V g e he hm hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, idem_mul_flipInv_pow he m]`. Unfold `IsFlipDet at hx`. Establish `hee` using `he.1`. Establish `hmE : ((m : D.host.E)) ≠ 0` using `Nat.cast_ne_zero.2 hm`.

Establish `hinc : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1`. Rewrite using `[← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ hmE, map_one]`. Establish `hpow : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1`. Rewrite using `[← mul_pow, hinc, one_pow]`. Establish `hy : (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1`.

Take the linear combination `(2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hee + e ^ 2 * hpow`. Take the linear combination `(e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * hx - (x : AE D) * hy`.
-/
theorem isDetAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    {x : (AE D)ˣ} (hx : IsFlipDet V e m x) : Formalism.L2.Theta.IsDetAt e V g⁻¹ x := by
  unfold Formalism.L2.Theta.IsDetAt
  rw [mt_inv_eq V g e he hm hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    idem_mul_flipInv_pow he m]
  unfold IsFlipDet at hx
  have hee := he.1
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ hmE, map_one]
  have hpow : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
    rw [← mul_pow, hinc, one_pow]
  have hy : (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1 := by
    linear_combination (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hee + e ^ 2 * hpow
  linear_combination (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * hx - (x : AE D) * hy

/- English proof (translation)
Introduce `D ψ V W χV χW om hW P e m g x ℓ hP hm hg hx hℓ`. Establish `he : IsSplitIdem D e` using `hP.1`. Establish `hm1 : Formalism.L2.Theta.mt W (1 : GA D W) = 1`. Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one, Units.val_one]`.

Establish `h1 : Formalism.L2.Theta.SuppAt e W 1` using `fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]`. Establish `h1' : Formalism.L2.Theta.IsDetAt e W 1 1`. Unfold `Formalism.L2.Theta.IsDetAt`. Rewrite using `[hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]`. Take `⟨r, hr, H⟩` from `hW.om_split e he g⁻¹ 1 (suppAt_inv V g e he hm hg) h1 x 1 (isDetAt_inv V g e he hm hg hx) h1'`.

Use `⟨r, hr, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[H ℓ (fun u hu f hf => hℓ u hu f hf) f hf, splitFacO, map_one, mul_one, Circle.coe_inv]`.
-/
theorem om_inv_flip_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW P e m g x ℓ hP hm hg hx hℓ
  have he : IsSplitIdem D e := hP.1
  have hm1 : Formalism.L2.Theta.mt W (1 : GA D W) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : Formalism.L2.Theta.SuppAt e W 1 := fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]
  have h1' : Formalism.L2.Theta.IsDetAt e W 1 1 := by
    unfold Formalism.L2.Theta.IsDetAt
    rw [hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]
  obtain ⟨r, hr, H⟩ := hW.om_split e he g⁻¹ 1 (suppAt_inv V g e he hm hg) h1 x 1 (isDetAt_inv V g e he hm hg hx) h1'
  refine ⟨r, hr, fun f hf => ?_⟩
  rw [H ℓ (fun u hu f hf => hℓ u hu f hf) f hf, splitFacO, map_one, mul_one, Circle.coe_inv]

end GlobalTheory.LevelSeries.FlipScalStep
end
