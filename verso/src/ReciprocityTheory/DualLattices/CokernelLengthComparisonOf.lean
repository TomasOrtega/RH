import ReciprocityTheory.DualLattices.CokernelLengthComparisonStatement
import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def btP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g) (Ix g) R :=
  ∑ i, H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R) +
    H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)

def phiP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g ⊕ Fin g) (Ix g) R :=
  fromRows H.Ht (btP H e)

def qW (H : HodgeTateDatum p g v R O σ cp) (a b : O) : Submodule R (Fin g ⊕ Fin g → R) :=
  (lieDPart H b).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (H.ρL a))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xMod (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (w : Fin m) :=
  qW H (e w) (e (π w)) ⧸
    ((tPart H (e w)).map (Matrix.mulVecLin (phiP H e))).comap (qW H (e w) (e (π w))).subtype

end Defs

def WdetLenStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb →
      ∃ (d : ℕ) (X : NNReal),
        Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) ∧
        HasLen v R (xMod H e π w) X ∧ X * cw = v (algebraMap R C cp) ^ d * cwb

def WdetDegStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ) (X : NNReal),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) →
      HasLen v R (xMod H e π w) X → X ≤ v (algebraMap R C cp) ^ d

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb`. Take `⟨d, X, hd, hX, hXe⟩` from `hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb`. Establish `hle` using `hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX`. Establish `hcp : v (algebraMap R C cp) ≠ 0`. Introduce `h0`.

Establish `h5` using `hS.cp_val`. Rewrite `h5` using `[h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne']`. Conclude with `hS.p_ne h5.symm`. Establish `hpos : 0 < v (algebraMap R C cp) ^ d` using `pow_pos (pos_iff_ne_zero.mpr hcp) d`. Establish `h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw`.

Rewrite using `[← hXe]`. Conclude with `mul_le_mul_of_nonneg_right hle zero_le`. Conclude with `le_of_mul_le_mul_left h6 hpos`.
-/
theorem cokernelLengthComparison_of (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) : CokernelLengthComparisonStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXe⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXe]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
