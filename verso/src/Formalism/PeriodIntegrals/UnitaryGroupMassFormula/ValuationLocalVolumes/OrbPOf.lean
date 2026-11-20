import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

/- English proof (translation)
Introduce `hG X hX hXY`. Establish `h : a ≤ n` using `hG.2.2.2.2.1`. Take `⟨G, hGe⟩` from `hE h hG`. Take `⟨ZX, hbX, heX, hgX, hdX⟩` from `hGe X hX hXY`. Take `⟨ZY, hbY, heY, hgY, hdY⟩` from `hGe Y hG.2.2.2.2.2 rfl`.

Use `set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX`. Use `set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY`. Use `set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk`. Establish `hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX`. Establish `: k * uY = uX` using `by rw [hk, inv_mul_cancel_right]`.

Conclude with `congrArg Units.val this`. Establish `hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1`. Establish `: uY * uY⁻¹ = 1` using `mul_inv_cancel uY`. Conclude with `congrArg Units.val this`. Establish `hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))` using `rfl`.

Establish `hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX = cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY`. Rewrite using `[← gram_eq_colM, ← gram_eq_colM, hgX, hgY]`. Establish `hkU : k ∈ HR (Fv F v) σ J` using `by show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = JR (Fv F v) J`. Rewrite using `[hkval]`. Use `set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by`. Rewrite using `[hgXY]`.

Use `_ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by`. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]`. Set `g : HA (Fv F v) σ J` to `(⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))`.

Establish `hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))` using `rfl`. Establish `hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1` using `congrArg Units.val (inv_mul_cancel k)`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ x, x ∈ latLoc (E := E) v Λ ↔ Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ`. Introduce `x`.

Rewrite using `[hgm]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨c, hc, rfl⟩` from `(hbY x).1 hx`. Use `(hbX _).2 ⟨c, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]`. Introduce `hx`. Take `⟨c, hc, hxc⟩` from `(hbX _).1 hx`. Use `(hbY x).2 ⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite `hxc`, the goal using `[sum_eq_colM]`.

Rewrite `hxc` using `[← hkY, ← mulVec_mulVec]`. Use `congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc` as an intermediate fact. Simplify `this` using `only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul]`. Use function extensionality and compare the values at `i show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i`. Rewrite using `[hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]`.
-/
theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  obtain ⟨ZX, hbX, heX, hgX, hdX⟩ := hGe X hX hXY
  obtain ⟨ZY, hbY, heY, hgY, hdY⟩ := hGe Y hG.2.2.2.2.2 rfl
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end PI.OmVd
