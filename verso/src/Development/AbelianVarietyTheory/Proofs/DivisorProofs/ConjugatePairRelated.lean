import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.PairConj

section Generic

variable {S : Type*} [Ring S]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem unop_mul_inv (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem unop_inv_mul (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ ((y⁻¹ : Sˣ) : S)).unop * (σ (y : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem triv_conj (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) :
    ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop =
      (x : S) * b * (σ (x : S)).unop := by
  have h := unop_mul_inv σ y
  calc ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop
      = (x : S) * (((y⁻¹ : Sˣ) : S) * y) * b * ((σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop) *
          (σ (x : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h, mul_one, mul_one]

end Generic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

def shU (y : G.Cˣ) : G.Cˣ :=
  ⟨sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C), unop_mul_inv G.star y, unop_inv_mul G.star y⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shU_val (y : G.Cˣ) : ((shU G y : G.Cˣ) : G.C) = sh G y := rfl

def conjAlg (y : G.Cˣ) : G.C →ₐ[G.F] G.C where
  toFun a := y * a * ((y⁻¹ : G.Cˣ) : G.C)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    show (y : G.C) * algebraMap G.F G.C r * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C r
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem conjAlg_injective (y : G.Cˣ) : Function.Injective (conjAlg G y) := by
  intro a b h
  have h' : (y : G.C) * a * ((y⁻¹ : G.Cˣ) : G.C) = y * b * ((y⁻¹ : G.Cˣ) : G.C) := h
  have := congrArg (fun z => ((y⁻¹ : G.Cˣ) : G.C) * z * (y : G.C)) h'
  simpa [mul_assoc] using this

variable {G} in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

variable {G} in

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem triv_conj_unit (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ)
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]
    rfl
  rw [e, triv_conj, hx]

variable {G}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem conj_val (β y : G.Cˣ) : ((y * β * shU G y : G.Cˣ) : G.C) = (y : G.C) * β * sh G y := by
  rw [Units.val_mul, Units.val_mul, shU_val]

def conjPair (P : Pair G) (y : G.Cˣ) : Pair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  trivR := by
    obtain ⟨z, hz⟩ := P.trivR
    have h := triv_conj_unit ℝ (P.β : G.C) y z 1 hz
    rw [← conj_val] at h
    exact ⟨_, h⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conjPair_β (P : Pair G) (y : G.Cˣ) :
    (((conjPair P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

end GlobalTheory.LKMid.PairConj

open GlobalTheory.LKMid.PairConj in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem GlobalTheory.LKMid.Pair.exists_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (y : G.Cˣ),
    ∃ P' : Pair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  intro p _ G P y
  refine ⟨conjPair P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjPair_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjPair_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl
