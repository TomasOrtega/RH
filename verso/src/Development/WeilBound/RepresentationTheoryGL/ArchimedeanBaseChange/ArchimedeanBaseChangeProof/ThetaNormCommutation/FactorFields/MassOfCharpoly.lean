import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace PositivityTheory.Rg.BcB.G3.MassP

open GlobalTheory.MassNorm

section

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hθE : ∀ g, thE E m (thE E m g) = g` using `GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)`. Take `⟨x, hx⟩` from `GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h`. Establish `hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁)` using `Units.ext hx`. Establish `hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁`. Simplify using `only [map_mul, map_inv, hθE]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y` using `fun y => GlobalTheory.ThetaPull.cFin_cFin y`. Establish `hN : ratF E m δ₁ * thF E m (ratF E m δ₁) = ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x))`. Rewrite using `[thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]`. Take `⟨v, hv⟩` from `GlobalTheory.ClassParam.exists_cyclic_field _ hs`.

Establish `hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det`. Establish `h1` using `(IsUnit.mk0 _ hv).map (algebraMap E (Af E))`. Rewrite `h1` using `[RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map]`. Rewrite using `[thF_ratF, ← map_mul]`. Conclude with `h1`.

Establish `heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x))` using `le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))`. Use `set y := ratF E m x with hy`. Establish `hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y`. Rewrite using `[hy, thF_ratF, map_mul, map_mul, map_inv]`. Establish `hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom`.

Rewrite using `[heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]`. Establish `hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁)`. Introduce `t`. Rewrite using `[hT]`. Conclude with `⟨t, t.2, by simp [MulAut.conj_apply]⟩`.

Establish `hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂)`. Introduce `s`. Establish `hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom` using `hT ▸ s.2`. Take `⟨t, ht, he⟩` from `hs'`. Establish `: (s : GL (Fin m) (Af E)) = y⁻¹ * t * y` using `by rw [← he]; simp [MulAut.conj_apply]`.

Rewrite using `[this]`. Simplify `ht` using `[mul_assoc]`. Set `e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁)` to `{ toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩ invFun := fun s => ⟨y * s * y⁻¹, hg s⟩ left_inv := fun t => Subtype.ext (by simp [mul_assoc]) right_inv := fun s => Subtype.ext (by simp [mul_assoc]) map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) continuous_toFun := Continuous.su …`. Establish `hyΓ : y ∈ (ratF E m).range` using `⟨x, rfl⟩`. Use `GlobalTheory.MassTor.mass_eq_of_equiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _) (isClosed_twCent_thF E m _) e fun t => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range`. Rewrite using `[Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]`.
-/
theorem mass_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.MassTor.mass_eq_of_equiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end

/- English proof (translation)
Introduce `E _ _ _ _ n δ hP`. Establish `hd : (δ * thE E n δ).val.charpoly.natDegree = n` using `hP.2.1`. Establish `hs : (δ * thE E n δ).val.charpoly.Separable` using `hP.2.2.1`. Generalize the expression as in `hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢`. Establish `hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧ ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P → mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ)`.

Introduce `k hk`. Substitute `hk` using the available equality. Conclude with `⟨⟨δ, hPdef⟩, fun δ' h' => mass_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩`. Take `⟨hex, hm⟩` from `hcast _ hd`. Unfold `GlobalTheory.BCT.kap GlobalTheory.BCT.nfac`.

Rewrite using `[dif_pos hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]`.
-/
theorem mass_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => mass_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dif_pos hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]

end PositivityTheory.Rg.BcB.G3.MassP

end
