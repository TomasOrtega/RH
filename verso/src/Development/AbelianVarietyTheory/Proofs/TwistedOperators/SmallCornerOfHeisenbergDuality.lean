import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Herm

variable {L : Type} [Field L] {N : ℕ}

def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev

/- English proof (translation)
Simplify using `only [hermJ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hermJ_add_left (σ : L →+* L) (x x' y : Fin N → L) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hermJ_add_right (σ : L →+* L) (x y y' : Fin N → L) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermJ, map_sum, map_mul, hσσ]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]`.
-/
theorem map_hermJ {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) :
    σ (hermJ σ x y) = hermJ σ y x := by
  simp only [hermJ, map_sum, map_mul, hσσ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

/- English proof (translation)
Rewrite using `[hermJ, ← Finset.sum_neg_distrib]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]`.
-/
theorem dotProduct_eq_neg_hermJ {σ : L →+* L} (r b w : Fin N → L) (h : ∀ j, r j = -σ (b j.rev)) :
    r ⬝ᵥ w = -hermJ σ b w := by
  rw [hermJ, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]

end Herm

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

/- English proof (translation)
Establish `hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev` using `fun i k => by`. Rewrite using `[mat_inv_apply, Fin.rev_rev, Fin.rev_rev]`. Establish `hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l`. Introduce `k l`. Rewrite using `[← mat_inv_mul g, Matrix.mul_apply]`.

Conclude with `Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `_ = ∑ k : Fin N, σ (x k) * y k.rev := by`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by
  have hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev := fun i k => by
    rw [mat_inv_apply, Fin.rev_rev, Fin.rev_rev]
  have hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l := by
    intro k l
    rw [← mat_inv_mul g, Matrix.mul_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  calc hermJ σ (mat g *ᵥ x) (mat g *ᵥ y)
      = ∑ k : Fin N, ∑ l : Fin N, σ (x k) * y l * ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l := by
        simp only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin N, σ (x k) * y k.rev := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Valued.v (σ x) ≤ 1`. Rewrite using `[hσ]`. Conclude with `h`.
-/
theorem sigma_mem_intL {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h

/- English proof (translation)
Establish `hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev)`. Simplify using `only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[hsum]`. Conclude with `Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)`.
-/
theorem hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by
  have hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev) := by
    simp only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)

end Unitary

/- English proof (translation)
Introduce `hH hD`. Unfold `SmallCorner`. Introduce `L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr`. Establish `hU'` using `hU`. Unfold `IsUnramInv at hU'`.

Take `⟨hσσ, hσv, hϖσ, hϖv, -⟩` from `hU'`. Take `⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev)` from `⟨_, rfl⟩`. Establish `hrb : ∀ j, r j = -σ (b j.rev)` using `fun j => by`. Rewrite using `[hb]`. Simplify using `only [Fin.rev_rev, map_neg, hσσ, neg_neg]`.

Take `⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b` from `⟨_, rfl⟩`. Take `⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b` from `⟨_, rfl⟩`. Establish `hsplit : b₁ + b₂ = b`. Establish `hCinv : C * (U + V * mat g₀) = 1` using `mul_eq_one_comm.mp hF.2.2.2.2`. Rewrite using `[hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv, Matrix.one_mulVec]`.

Take `⟨τ, hτint, hτ⟩` from `exists_trace_one hU`. Take `⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂` from `⟨_, rfl⟩`. Establish `hσs : σ s = s` using `by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]`. Establish `hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁` using `dotProduct_eq_neg_hermJ r b b₁ hrb`. Establish `hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b`.

Rewrite using `[← dotProduct_eq_neg_hermJ r b b hrb, hb]`. Simplify using `only [dotProduct, mul_neg, Finset.sum_neg_distrib]`. Establish `hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev)`. Rewrite using `[hnorm, hrb₁, map_add, map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]`. Simplify using `only [hermJ_add_left, hermJ_add_right]`.

Take the linear combination `s * hτ + hs`. Take `⟨hHrad, -, hHex⟩` from `hH L ϖ σ q N hU`. Take `⟨u, hu, hur, huc⟩` from `hHex r (r ⬝ᵥ b₁ + τ * s) hc`. Establish `hcol : colOf u = b`. Use function extensionality and compare the values at `i`.

Establish `hi` using `(hHrad u hu).1 i.rev`. Rewrite `hi` using `[hur, Fin.rev_rev]`. Rewrite using `[hb]`. Simplify using `only [hi, map_neg, hσσ, neg_neg]`. Take `⟨h₁, h₂⟩` from `(hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr`.

Use `⟨u, hu, hur, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hur]`. Conclude with `hr`. Rewrite using `[hur, hcol, huc, ← hb₁, add_sub_cancel_left]`. Establish `hϖint : ϖ ∈ intL L`.

Express the relevant statement in the definitionally equal form `Valued.v ϖ ≤ 1`. Rewrite using `[hϖv]`. Conclude with `WithZero.coe_le_one.mpr (by decide)`. Establish `i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L` using `hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)`. Establish `hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b`.

Rewrite using `[hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L`. Rewrite using `[← hermJ_mulVec g₀ b₂ b₂, hg]`. Conclude with `hermJ_int hσv hϖσ e _ h₂`. Establish `hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e)` using `by rw [← pow_add, Nat.sub_add_cancel hef]`.

Establish `hsplit' : ϖ ^ f * (τ * s) = τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂)`. Rewrite using `[hf, hs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit']`. Conclude with `Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)`.
-/
theorem smallCorner_of_heis_dual : Heis → Dual → SmallCorner := by
  intro hH hD
  unfold SmallCorner
  intro L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  have hU' := hU
  unfold IsUnramInv at hU'
  obtain ⟨hσσ, hσv, hϖσ, hϖv, -⟩ := hU'

  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  have hrb : ∀ j, r j = -σ (b j.rev) := fun j => by
    rw [hb]
    simp only [Fin.rev_rev, map_neg, hσσ, neg_neg]
  obtain ⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b := ⟨_, rfl⟩
  have hsplit : b₁ + b₂ = b := by
    have hCinv : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hF.2.2.2.2
    rw [hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv,
      Matrix.one_mulVec]
  obtain ⟨τ, hτint, hτ⟩ := exists_trace_one hU
  obtain ⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂ := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]
  have hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁ := dotProduct_eq_neg_hermJ r b b₁ hrb
  have hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b := by
    rw [← dotProduct_eq_neg_hermJ r b b hrb, hb]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev) := by
    rw [hnorm, hrb₁, map_add, map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]
    simp only [hermJ_add_left, hermJ_add_right]
    linear_combination s * hτ + hs
  obtain ⟨hHrad, -, hHex⟩ := hH L ϖ σ q N hU
  obtain ⟨u, hu, hur, huc⟩ := hHex r (r ⬝ᵥ b₁ + τ * s) hc
  have hcol : colOf u = b := by
    funext i
    have hi := (hHrad u hu).1 i.rev
    rw [hur, Fin.rev_rev] at hi
    rw [hb]
    simp only [hi, map_neg, hσσ, neg_neg]
  obtain ⟨h₁, h₂⟩ := (hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr
  refine ⟨u, hu, hur, ?_, ?_⟩
  · rw [hur]
    exact hr
  · rw [hur, hcol, huc, ← hb₁, add_sub_cancel_left]
    have hϖint : ϖ ∈ intL L := by
      change Valued.v ϖ ≤ 1
      rw [hϖv]
      exact WithZero.coe_le_one.mpr (by decide)
    have i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L :=
      hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)
    have hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b := by
      rw [hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L := by
      rw [← hermJ_mulVec g₀ b₂ b₂, hg]
      exact hermJ_int hσv hϖσ e _ h₂
    have hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e) := by rw [← pow_add, Nat.sub_add_cancel hef]
    have hsplit' : ϖ ^ f * (τ * s) =
        τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂) := by
      rw [hf, hs]
      ring
    rw [hsplit']
    exact Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)

end GlobalTheory.InertZeta
