import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.GRHaar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance krCpt (n : ℕ) : CompactSpace (KR n) := kRCpt n

def phi (m : ℕ) (e : ℤ) (w : ℂ) (u : GR n) : ℂ := F0 m 0 e u * ((hLoc u : ℝ) : ℂ) ^ w

def tw (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (X : M2 n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ) ∂μK

def cw (m : ℕ) (e : ℤ) (ν : Measure (GR n)) (μK : Measure (KR n)) (β : M2 n → ℝ) (w : ℂ) : ℂ :=
  ∫ u : GR n, phi m e w u * tw m e μK β (mR u) ∂ν

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

/- English proof (translation)
Establish `h` using `integral_mul_left_eq_self (μ := μK) (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * (mR (k₀ : GR n) * X)) : ℂ)) k₀`. Rewrite using `[tw, ← h, tw, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Establish `hk0 : (mR (k₀ : GR n))ᴴ * mR (k₀ : GR n) = 1` using `k₀.2.2`. Establish `hmul` using `((mult n m 0 e).1 (k₀ : GR n) (k : GR n) k.2).1`.

Simplify using `only [Subgroup.coe_mul, mR_mul]`. Rewrite using `[hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mR (k₀ : GR n))ᴴ, hk0, Matrix.one_mul, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tw_left (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsMulLeftInvariant] (β : M2 n → ℝ) (k₀ : KR n) (X : M2 n) :
    tw m e μK β (mR (k₀ : GR n) * X) = (F0 m 0 e (k₀ : GR n))⁻¹ * tw m e μK β X := by
  have h := integral_mul_left_eq_self (μ := μK)
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * (mR (k₀ : GR n) * X)) : ℂ)) k₀
  rw [tw, ← h, tw, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hk0 : (mR (k₀ : GR n))ᴴ * mR (k₀ : GR n) = 1 := k₀.2.2
  have hmul := ((mult n m 0 e).1 (k₀ : GR n) (k : GR n) k.2).1
  simp only [Subgroup.coe_mul, mR_mul]
  rw [hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mR (k₀ : GR n))ᴴ, hk0, Matrix.one_mul,
    mul_inv]
  ring

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl⟩` from `iwa n y`. Establish `hnn : ∀ g : GR n, 0 ≤ hLoc g` using `fun g => by unfold hLoc; positivity`. Establish `hphi : ∀ g : GR n, phi m e w (p * g) = phi m e w p * phi m e w g`. Introduce `g`. Take `⟨h1, h2⟩` from `(mult n m 0 e).2 p g hp`.

Simplify using `only [phi, h1, h2, Complex.ofReal_mul]`. Rewrite using `[Complex.mul_cpow_ofReal_nonneg (hnn p) (hnn g)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : phi m e w (p * k) = phi m e w p * F0 m 0 e k`. Take `⟨h1, h2⟩` from `(mult n m 0 e).1 p k hk`.

Simplify using `only [phi, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hone : F0 m 0 e (1 : GR n) = 1`. Establish `h1 : toBlocks₂₁ (1 : M2 n) = 0`. Use extensionality with `i j`.

Simplify using `[Matrix.toBlocks₂₁, Matrix.one_apply]`. Establish `h2 : toBlocks₂₂ (1 : M2 n) = 1`. Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]`. Simplify using `[F0, mR, f0, u1, u2, h1, h2]`.

Establish `hF : F0 m 0 e k * F0 m 0 e k⁻¹ = 1`. Rewrite using `[← ((mult n m 0 e).1 k k⁻¹ (inv_mem hk)).1, mul_inv_cancel, hone]`. Establish `htw : ∀ u : GR n, tw m e μK β (mR (k⁻¹ * u)) = F0 m 0 e k * tw m e μK β (mR u)`. Introduce `u`. Rewrite using `[mR_mul]`.

Establish `h` using `tw_left m e μK β (⟨k⁻¹, inv_mem hk⟩ : KR n) (mR u)`. Simplify using `only at h`. Rewrite using `[h, inv_eq_of_mul_eq_one_left hF]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `u`. Rewrite using `[show p * k * (k⁻¹ * u) = p * u by group, hphi, htw]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = cw m e ν μK β w * phi m e w (p * k) := by`. Rewrite using `[integral_const_mul, hK]`.

Unfold `cw`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conv_phi (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsMulLeftInvariant] (μK : Measure (KR n)) [μK.IsMulLeftInvariant]
    (β : M2 n → ℝ) (w : ℂ) (y : GR n) :
    ∫ u : GR n, phi m e w (y * u) * tw m e μK β (mR u) ∂ν = cw m e ν μK β w * phi m e w y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  have hnn : ∀ g : GR n, 0 ≤ hLoc g := fun g => by unfold hLoc; positivity
  have hphi : ∀ g : GR n, phi m e w (p * g) = phi m e w p * phi m e w g := by
    intro g
    obtain ⟨h1, h2⟩ := (mult n m 0 e).2 p g hp
    simp only [phi, h1, h2, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (hnn p) (hnn g)]
    ring
  have hK : phi m e w (p * k) = phi m e w p * F0 m 0 e k := by
    obtain ⟨h1, h2⟩ := (mult n m 0 e).1 p k hk
    simp only [phi, h1, h2]
    ring
  have hone : F0 m 0 e (1 : GR n) = 1 := by
    have h1 : toBlocks₂₁ (1 : M2 n) = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have h2 : toBlocks₂₂ (1 : M2 n) = 1 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
    simp [F0, mR, f0, u1, u2, h1, h2]
  have hF : F0 m 0 e k * F0 m 0 e k⁻¹ = 1 := by
    rw [← ((mult n m 0 e).1 k k⁻¹ (inv_mem hk)).1, mul_inv_cancel, hone]
  have htw : ∀ u : GR n, tw m e μK β (mR (k⁻¹ * u)) = F0 m 0 e k * tw m e μK β (mR u) := by
    intro u
    rw [mR_mul]
    have h := tw_left m e μK β (⟨k⁻¹, inv_mem hk⟩ : KR n) (mR u)
    simp only at h
    rw [h, inv_eq_of_mul_eq_one_left hF]
  calc ∫ u : GR n, phi m e w (p * k * u) * tw m e μK β (mR u) ∂ν
      = ∫ u : GR n, phi m e w (p * k * (k⁻¹ * u)) * tw m e μK β (mR (k⁻¹ * u)) ∂ν :=
        (integral_mul_left_eq_self (fun u => phi m e w (p * k * u) * tw m e μK β (mR u)) k⁻¹).symm
    _ = ∫ u : GR n, (F0 m 0 e k * phi m e w p) * (phi m e w u * tw m e μK β (mR u)) ∂ν := by
        congr 1
        funext u
        rw [show p * k * (k⁻¹ * u) = p * u by group, hphi, htw]
        ring
    _ = cw m e ν μK β w * phi m e w (p * k) := by
        rw [integral_const_mul, hK]
        unfold cw
        ring

end PositivityTheory.Rg.Sw.HSt.Conv
