import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.DualLat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L

/- English proof (translation)
Introduce `i` and use `by simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)`.
-/
theorem IntT.add {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x + y) := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)

/- English proof (translation)
Introduce `i` and use `by simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)`.
-/
theorem IntT.neg {t : L} {x : Fin N → L} (hx : IntT t x) : IntT t (-x) := fun i => by
  simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `hx.add hy.neg`.
-/
theorem IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/- English proof (translation)
Introduce `i` and use `by simp only [Matrix.mulVec, dotProduct, Finset.mul_sum] exact Subring.sum_mem _ fun k _ => by rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)`.
-/
theorem IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)

/- English proof (translation)
Introduce `j` and use `by simp only [Matrix.vecMul, dotProduct, Finset.mul_sum] exact Subring.sum_mem _ fun k _ => by rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)`.
-/
theorem IntT.vecMul {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hx : IntT t x) (hM : IsInt M) :
    IntT t (x ᵥ* M) := fun j => by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)

/- English proof (translation)
Introduce `j` and use `by show Valued.v (t * σ (x j.rev)) ≤ 1 rw [map_mul, hσ, ← map_mul]; exact hx j.rev`.
-/
theorem IntT.twist {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev

/- English proof (translation)
Use extensionality with `j`. Simplify using `[tw, hσσ]`.
-/
theorem tw_tw {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x : Fin N → L) : tw σ (tw σ x) = x := by
  ext j; simp [tw, hσσ]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[tw]`.
-/
theorem tw_add (σ : L →+* L) (x y : Fin N → L) : tw σ (x + y) = tw σ x + tw σ y := by
  ext j; simp [tw]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[tw]`.
-/
theorem tw_neg (σ : L →+* L) (x : Fin N → L) : tw σ (-x) = -tw σ x := by
  ext j; simp [tw]

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]`. Use `(Equiv.sum_comp Fin.revPerm _).symm.trans ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem tw_vecMul {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j
  simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]

end GlobalTheory.InertZeta.DualLat

namespace GlobalTheory.InertZeta

open DualLat

/- English proof (translation)
Introduce `L _ _ ϖ σ q N hU g U V C hF r b t hr`. Take `⟨hσσ, hσ, -⟩` from `hU`. Take `⟨hUi, hVi, hCi, hgC, e⟩` from `hF`. Establish `e' : C * (U + V * mat g) = 1` using `mul_eq_one_comm.1 e`. Establish `hr' : r = -tw σ b` using `by ext j; simp [tw, hr]`.

Establish `m1 : C * V * mat g = 1 - C * U`. Rewrite using `[Matrix.mul_assoc, ← e', Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Establish `m2 : C * V * mat g * mat g⁻¹ = C * V` using `by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]`. Establish `hCU : C * U = 1 - C * V * mat g` using `by rw [m1]; abel`.

Establish `m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V`. Rewrite using `[Matrix.mul_assoc (mat g) C U, hCU]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]`. Express the relevant statement in the definitionally equal form `IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)`. Prove the components needed by the constructor for the conclusion.

Introduce `hρ`. Establish `h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g`. Rewrite using `[Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]`. Establish `hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U))` using `((hρ.vecMul hUi).twist hσ).neg`. Establish `hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V))` using `((hρ.vecMul hVi).twist hσ).neg`.

Establish `htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r`. Rewrite using `[tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]`. Use `conv_rhs => rw [h1]`. Normalize the expressions using the abelian group laws. Establish `hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[htw, hr', neg_neg]`. Use `_ = _ := tw_tw hσσ _`. Rewrite using `[hb]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `(hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `(IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b`. Rewrite using `[← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]`. Establish `key : ∀ b₁ b₂ : Fin N → L, -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C)`. Introduce `b₁ b₂`. Rewrite using `[← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add, Matrix.neg_vecMul, Matrix.add_vecMul]`.

Normalize the expressions using the abelian group laws. Establish `h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b))`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc]`. Conclude with `h2`. Rewrite using `[hr', hb, key]`.

Conclude with `((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)`.
-/
theorem dual_inter_eq_sum : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)

end GlobalTheory.InertZeta

end
