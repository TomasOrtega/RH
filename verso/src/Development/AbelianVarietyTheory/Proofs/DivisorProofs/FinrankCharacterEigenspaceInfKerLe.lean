import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegularStatement
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

/- English proof (translation)
Rewrite `hx` using `[mem_eig]`. Establish `hc : (Nat.card Hb : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Unfold `Formalism.L2.DIV.lvlIdem`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Simplify using `only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]`.

Establish `e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹` using `fun h => by`. Rewrite using `[mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]`. Simplify using `only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]`.
-/
theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem
  rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

/- English proof (translation)
Introduce `Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff`. Use `set p := Formalism.L2.DIV.lvlIdem Hb lam with hp`. Use `set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW`. Set `f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p))` to `((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)`. Establish `hinj : Function.Injective f`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨x, hxe, hxk⟩ hx0`. Establish `h0 : ρ.asAlgebraHom (b 0 * p) x = 0`. Use `congrArg (fun z => ((z.1 : _) : V)) hx0` as an intermediate fact. Simplify `this` using `[f]`.

Establish `h1 : ρ.asAlgebraHom (b 1 * p) x = 0`. Use `congrArg (fun z => ((z.2 : _) : V)) hx0` as an intermediate fact. Simplify `this` using `[f]`. Establish `hpx : ρ.asAlgebraHom p x = x` using `lvlIdem_apply_of_mem_eig ρ Hb lam x hxe`. Establish `hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x` using `fun k => by`.

Rewrite using `[map_mul, Module.End.mul_apply, hpx]`. Establish `hb0 : ρ.asAlgebraHom (b 0) x = 0` using `(hb 0).trans h0`. Establish `hb1 : ρ.asAlgebraHom (b 1) x = 0` using `(hb 1).trans h1`. Establish `hek : ρ.asAlgebraHom e x = 0` using `hxk`. Establish `hx1 : x = ρ.asAlgebraHom (1 - e) x`.

Rewrite using `[map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]`. Both sides reduce to the same expression. Establish `: x = 0`. Rewrite using `[hx1, he, map_sub, map_add, map_mul]`. Simplify using `[LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]`.

Conclude with `Subtype.ext this`. Establish `hdim` using `LinearMap.finrank_le_finrank_of_injective hinj`. Rewrite `hdim` using `[Module.finrank_prod]`. Establish `hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ c * s k * finrank ℂ (eig ρ Hb lam)`. Introduce `k`.

Establish `hid : b k * p * (b k * p) = b k * p`. Combine the equalities or inequalities in the displayed calculation. Take `⟨r, hr, hle⟩` from `GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid`. Rewrite `hr` using `[hcoeff k]`. Establish `hHb : (0 : ℝ) < Nat.card Hb` using `by exact_mod_cast Nat.card_pos`.

Establish `hH : (0 : ℝ) < Nat.card (H k)` using `by exact_mod_cast Nat.card_pos`. Establish `hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k`. Establish `hHbC : (Nat.card Hb : ℂ) ≠ 0` using `by exact_mod_cast hHb.ne'`. Establish `: ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ)` using `by push_cast; rw [hr]; field_simp`. Conclude with `this` after adjusting the coercions.

Establish `hs : 0 ≤ s k`. Establish `: 0 ≤ (Nat.card (H k) : ℝ) * s k` using `by rw [← hrR]; positivity`. Conclude with `le_of_mul_le_mul_left (by simpa using this) hH`. Establish `hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam)` using `by positivity`. Establish `hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r` using `by exact_mod_cast hle`.

Establish `key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hleR.trans (le_of_mul_le_mul_right key hHb)`. Establish `hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) + finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p)))` using `by exact_mod_cast hdim`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add, map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
