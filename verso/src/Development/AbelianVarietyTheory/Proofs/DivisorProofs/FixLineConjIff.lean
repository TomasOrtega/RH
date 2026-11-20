import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

/- English proof (translation)
Establish `key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) = (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩`.

Introduce and unpack `⟨c, hc⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[key, ← Matrix.mulVec_smul]`. Establish `h` using `congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc`. Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h`.

Rewrite `h` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis.
-/
theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

/- English proof (translation)
Introduce `p _ G v β y g z`. Unfold `FixL`. Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `fixLine_conj_iff _ _ z`.
-/
theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
