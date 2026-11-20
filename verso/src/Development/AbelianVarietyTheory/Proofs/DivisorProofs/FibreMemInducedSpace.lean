import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local notation:70 M:70 " ⬝ₘ " N:71 => HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) M N

/- English proof (translation)
Use extensionality with `x`. Simplify using `[stdSum]`.
-/
theorem stdSum_rfl' (a b : ℕ) : stdSum (rfl : a + b = a + b) = finSumFinEquiv := by
  ext x; simp [stdSum]

/- English proof (translation)
Establish `hA : (invT (leviProj k (blocks a b) p false)).val = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ`. Rewrite using `[invT_val, map_inv]`. Both sides reduce to the same expression. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]`.

Take `⟨s, rfl⟩` from `finSumFinEquiv.surjective j`. Break down `s with j | j` into its components or cases. Use `leviProj_apply k (blocks a b) p⁻¹ false j i` as an intermediate fact. Simplify using `[stdSum_rfl'] at this`. Simplify using `[Matrix.mul_apply, X0, this]`.

Establish `hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j` using `fun i h => by`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Use `(mem_parab_two k).1 (p⁻¹).2 j i` as an intermediate fact.

Simplify using `[stdSum_rfl'] at this`. Simplify using `[Matrix.mul_apply, X0, this, hne]`.
-/
theorem X0_mul_invT_parab (a b : ℕ) (p : parab k (blocks a b)) :
    X0 k finSumFinEquiv ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val =
      (invT (leviProj k (blocks a b) p false)).val ⬝ₘ X0 k finSumFinEquiv := by
  have hA : (invT (leviProj k (blocks a b) p false)).val
      = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ := by
    rw [invT_val, map_inv]; rfl
  refine Matrix.ext fun i j => ?_
  rw [frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with j | j
  · have := leviProj_apply k (blocks a b) p⁻¹ false j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this]
  · have hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j := fun i h => by
      have := congrArg Fin.val h; simp at this; omega
    have := (mem_parab_two k).1 (p⁻¹).2 j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this, hne]

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Introduce `p x`. Rewrite using `[ofChar_apply]`. Use `set A := leviProj k (blocks a b) p false with hAdef`. Use `set D := leviProj k (blocks a b) p true with hDdef`. Use `set Ψ := omA ν β 1 x Φ with hΨ`.

Use `set z : ℂ := ((a + b : ℕ) : ℂ) / 2 with hz`. Use `set F : GL (Fin a) k → ℂ := fun g => Ψ (g.val ⬝ₘ X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) * apow (gdet g) z with hF`. Use `set c : ℂ := (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) * ν (gdet A) * apow (gdet A) z with hc`. Establish `h1 : omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ = omA ν β 1 ↑p Ψ` using `by rw [hΨ, ← omA_mul, one_mul]`. Establish `h2 : ∀ Y, omA ν β 1 (↑p : GL (Fin (a + b)) k) Ψ Y = (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) * Ψ (Y ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val)`.

Introduce `Y`. Simplify using `[omA]`. Establish `hm : ∀ g : GL (Fin a) k, (g.val ⬝ₘ X0 k finSumFinEquiv) ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val = (g * invT A).val ⬝ₘ X0 k finSumFinEquiv`. Introduce `g`. Rewrite using `[Matrix.mul_assoc, X0_mul_invT_parab, ← Matrix.mul_assoc, ← Units.val_mul]`.

Establish `key : ∀ g : GL (Fin a) k, omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ (g.val ⬝ₘ X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) * apow (gdet g) z = c * F (g * invT A)`. Introduce `g`. Rewrite using `[h1, h2, hm g]`. Simplify using `only [hF, hc, gdet_mul, gdet_invT, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, apow_mul, apow_inv, apow_neg]`. Establish `n1 : (ν (gdet A) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `n2 : apow (gdet A) z ≠ 0` using `apow_ne_zero _ _`. Clear the denominators using the available nonvanishing facts. Establish `hdet : gdet (p : GL (Fin (a + b)) k) = gdet A * gdet D`. Use `det_parab k (blocks a b) p` as an intermediate fact. Rewrite `this` using `[Fintype.prod_bool]`.

Conclude with `this.trans (mul_comm _ _)`. Establish `hL : leviProj k (blocks a b) p = leviTwo k (Fin a) (Fin b) (A, D)`. Apply the tactic sequence `funext t; cases t <;> rfl`. Establish `hab : ∀ (s : ℂ) (y : kˣ), ((absPow k s y : ℂˣ) : ℂ) = apow y s` using `fun _ _ => rfl`. Establish `hchar : ((parChar ν β a b p : ℂˣ) : ℂ) = c`.

Simplify using `only [parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hL, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, deltaHalf_two, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, hab, Fintype.card_fin]`. Establish `e : apow (gdet A) z * apow (gdet A) (-(a : ℂ) / 2) = apow (gdet A) ((b : ℂ) / 2)`. Rewrite using `[← apow_add, hz]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hdet, map_mul, Units.val_mul, apow_mul]`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hchar]`.

Establish `I1 : fibre ν β a b Φ ((p : GL (Fin (a + b)) k) * x) = ∫ g, c * F (g * invT A) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))` using `integral_congr_ae (Filter.Eventually.of_forall key)`. Establish `I2 : fibre ν β a b Φ x = ∫ g, F g ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))` using `rfl`. Rewrite using `[I1, I2, integral_const_mul, integral_mul_right_eq_self F (invT A)]`.
-/
theorem fibre_mem_indSpace (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) :
    fibre ν β a b Φ ∈ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b)) := by
  intro p x
  rw [ofChar_apply]
  set A := leviProj k (blocks a b) p false with hAdef
  set D := leviProj k (blocks a b) p true with hDdef
  set Ψ := omA ν β 1 x Φ with hΨ
  set z : ℂ := ((a + b : ℕ) : ℂ) / 2 with hz
  set F : GL (Fin a) k → ℂ := fun g => Ψ (g.val ⬝ₘ X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
    apow (gdet g) z with hF
  set c : ℂ := (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
    ν (gdet A) * apow (gdet A) z with hc
  have h1 : omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ = omA ν β 1 ↑p Ψ := by rw [hΨ, ← omA_mul, one_mul]
  have h2 : ∀ Y, omA ν β 1 (↑p : GL (Fin (a + b)) k) Ψ Y =
      (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
        Ψ (Y ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val) := by
    intro Y
    simp [omA]
  have hm : ∀ g : GL (Fin a) k, (g.val ⬝ₘ X0 k finSumFinEquiv) ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val =
      (g * invT A).val ⬝ₘ X0 k finSumFinEquiv := by
    intro g
    rw [Matrix.mul_assoc, X0_mul_invT_parab, ← Matrix.mul_assoc, ← Units.val_mul]
  have key : ∀ g : GL (Fin a) k, omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ (g.val ⬝ₘ X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
      apow (gdet g) z = c * F (g * invT A) := by
    intro g
    rw [h1, h2, hm g]
    simp only [hF, hc, gdet_mul, gdet_invT, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, apow_mul,
      apow_inv, apow_neg]
    have n1 : (ν (gdet A) : ℂ) ≠ 0 := Units.ne_zero _
    have n2 : apow (gdet A) z ≠ 0 := apow_ne_zero _ _
    field_simp
  have hdet : gdet (p : GL (Fin (a + b)) k) = gdet A * gdet D := by
    have := det_parab k (blocks a b) p
    rw [Fintype.prod_bool] at this
    exact this.trans (mul_comm _ _)
  have hL : leviProj k (blocks a b) p = leviTwo k (Fin a) (Fin b) (A, D) := by
    funext t; cases t <;> rfl
  have hab : ∀ (s : ℂ) (y : kˣ), ((absPow k s y : ℂˣ) : ℂ) = apow y s := fun _ _ => rfl
  have hchar : ((parChar ν β a b p : ℂˣ) : ℂ) = c := by
    simp only [parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hL,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, deltaHalf_two,
      MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, hab, Fintype.card_fin]
    have e : apow (gdet A) z * apow (gdet A) (-(a : ℂ) / 2) = apow (gdet A) ((b : ℂ) / 2) := by
      rw [← apow_add, hz]; congr 1; push_cast; ring
    rw [hc, hdet, map_mul, Units.val_mul, apow_mul]
    rw [← e]
    ring
  rw [hchar]
  have I1 : fibre ν β a b Φ ((p : GL (Fin (a + b)) k) * x) =
      ∫ g, c * F (g * invT A) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    integral_congr_ae (Filter.Eventually.of_forall key)
  have I2 : fibre ν β a b Φ x = ∫ g, F g ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := rfl
  rw [I1, I2, integral_const_mul, integral_mul_right_eq_self F (invT A)]

end GlobalTheory.RankFibre
