import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Lift

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun b ha ↦ h _ ha b⟩`.
-/
theorem rel_isTwoSided (h : ∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) : (rel R δ).IsTwoSided :=
  ⟨fun b ha ↦ h _ ha b⟩

variable [(rel R δ).IsTwoSided]

def kq : K1 R δ →ₗ[B] DR R B ⧸ rel R δ :=
  (N1 R δ).liftQ ((Ideal.Quotient.mkₐ B (rel R δ)).toLinearMap ∘ₗ ι1) fun x hx ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kq_mk (ω : Ω[B⁄R]) : kq δ (Submodule.Quotient.mk ω) = Ideal.Quotient.mk (rel R δ) (ι1 ω) := rfl

end Lift

/- English proof (translation)
Use `haveI : (rel R δ).IsTwoSided := rel_isTwoSided δ ((GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R B J δ).1)`. Use `letI algC : Algebra C (DR R B ⧸ rel R δ) := ((algebraMap B (DR R B ⧸ rel R δ)).comp (π : C →+* B)).toAlgebra' fun c x ↦ Algebra.commutes (π c) x`. Use `haveI : IsScalarTower R C (DR R B ⧸ rel R δ) := IsScalarTower.of_algebraMap_eq fun r ↦ by`. Express the relevant statement in the definitionally equal form `_ = algebraMap B _ (π (algebraMap R C r))`. Rewrite using `[AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`.

Establish `smulC : ∀ (c : C) (q : DR R B ⧸ rel R δ), c • q = π c • q` using `fun c q ↦ by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression. Set `v : Derivation R C (DR R B ⧸ rel R δ)` to `Derivation.mk' { toFun := fun c ↦ kq δ (w c) map_add' := fun a b ↦ by simp map_smul' := fun r c ↦ by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def r c, hw, hw0, smul_zero, add_zero, map_smul, AlgHom.commutes, algebraMap_smul] }`.

Use `fun a b ↦ by`. Express the relevant statement in the definitionally equal form `kq δ (w (a * b)) = a • kq δ (w b) + b • kq δ (w a)`. Rewrite using `[hw, map_add, map_smul, map_smul, smulC, smulC]`. Establish `hv : ∀ c, v c = kq δ (w c)` using `fun _ ↦ rfl`. Establish `key : ∀ ω : Ω[C⁄R], ∃ η : Ω[B⁄R], v.liftKaehlerDifferential ω = Ideal.Quotient.mk (rel R δ) (ι1 η)`.

Introduce `ω`. Proceed by induction on `ω using ind1 with`. Consider the case `h b c`. Take `⟨η, hη⟩` from `Submodule.Quotient.mk_surjective _ (w c)`. Use `⟨π b • η, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, Derivation.liftKaehlerDifferential_comp_D, hv, ← hη, kq_mk, smulC, map_smul, Algebra.smul_def (π b) (ι1 η), map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]`. Consider the case `h0 => exact ⟨0, by simp⟩`. Consider the case `ha x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Conclude with `⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩`. Set `Φ : DR R C →ₐ[C] DR R B ⧸ rel R δ` to `ExteriorAlgebra.lift C ⟨v.liftKaehlerDifferential, fun m ↦ by`. Take `⟨η, h⟩` from `key m`. Rewrite using `[h, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩`. Establish `hΦι : ∀ ω : Ω[C⁄R], Φ (ι1 ω) = v.liftKaehlerDifferential ω` using `fun ω ↦ ExteriorAlgebra.lift_ι_apply _ _ _ _`.

Establish `hΦD : ∀ c, Φ (ι1 (D R C c)) = kq δ (w c)` using `fun c ↦ by`. Rewrite using `[hΦι, Derivation.liftKaehlerDifferential_comp_D, hv]`. Take `⟨ρ, hρ⟩ : ∃ ρ : DR R C → DR R B, ∀ x, Ideal.Quotient.mk (rel R δ) (ρ x) = Φ x` from `⟨_, fun x ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (Φ x)⟩`. Establish `cv : ∀ x a, ρ x - a ∈ rel R δ ↔ Φ x = Ideal.Quotient.mk (rel R δ) a` using `fun x a ↦ by`. Rewrite using `[← Ideal.Quotient.eq, hρ]`.

Use `⟨ρ, fun x y ↦ ?_, fun x y ↦ ?_, fun c ↦ ?_, fun c ω h ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun j x hx ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[sub_sub]`. Conclude with `(cv _ _).2 (by rw [map_add, map_add, hρ, hρ])`. Conclude with `(cv _ _).2 (by rw [map_mul, map_mul, hρ, hρ])`. Conclude with `(cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)`.

Conclude with `(cv _ _).2 (by rw [hΦD, ← h, kq_mk])`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hρ]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨n, a, ha, rfl⟩` from `hx`.

Rewrite using `[map_sub, map_smul, map_sub, map_smul, hΦD, hΦD, hwd n a ha, map_smul, smulC, sub_self]`. Consider the case `zero => exact map_zero _`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul r x _ ih => rw [smul_eq_mul, map_mul, ih, mul_zero]`. Take `⟨η, h⟩` from `key x`.

Conclude with `⟨η, (cv _ _).2 (by rw [hΦι, h])⟩`. Proceed by induction on `hx using Submodule.pow_induction_on_left' with`. Consider the case `algebraMap c`. Use `⟨algebraMap B _ (π c), ?_, (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ LinearMap.range _ ^ 0`.

Rewrite using `[pow_zero]`. Conclude with `Submodule.algebraMap_mem _`. Consider the case `add x y i _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`. Take `⟨b, hb, hb'⟩` from `hy`.

Conclude with `⟨a + b, add_mem ha hb, (cv _ _).2 (by rw [map_add, (cv _ _).1 ha', (cv _ _).1 hb', map_add])⟩`. Consider the case `mem_mul m hm i x hx ih`. Take `⟨ω, rfl⟩` from `hm`. Take `⟨η, hη⟩` from `key ω`. Take `⟨y, hy, hy'⟩` from `ih`.

Use `⟨ι1 η * y, ?_, (cv _ _).2 ?_⟩` and prove the remaining obligations. Use `GlobalTheory.CechDR.mul_mem (ι_mem η) hy` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Rewrite using `[map_mul, (cv _ _).1 hy', map_mul, ← hη, ← hΦι]`.
-/
theorem exists_lift_of_pdDerivation (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC)
    (π : C →ₐ[R] B) (w : C →+ K1 R δ) (hw : ∀ x y, w (x * y) = π x • w y + π y • w x)
    (hw0 : ∀ r, w (algebraMap R C r) = 0)
    (hwd : ∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) :
    ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧
      (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧
      (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧
      (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧
      ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  haveI : (rel R δ).IsTwoSided := rel_isTwoSided δ ((GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R B J δ).1)
  letI algC : Algebra C (DR R B ⧸ rel R δ) :=
    ((algebraMap B (DR R B ⧸ rel R δ)).comp (π : C →+* B)).toAlgebra' fun c x ↦ Algebra.commutes (π c) x
  haveI : IsScalarTower R C (DR R B ⧸ rel R δ) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap B _ (π (algebraMap R C r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have smulC : ∀ (c : C) (q : DR R B ⧸ rel R δ), c • q = π c • q := fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  let v : Derivation R C (DR R B ⧸ rel R δ) := Derivation.mk'
    { toFun := fun c ↦ kq δ (w c)
      map_add' := fun a b ↦ by simp
      map_smul' := fun r c ↦ by
        rw [RingHom.id_apply, Algebra.smul_def r c, hw, hw0, smul_zero, add_zero, map_smul, AlgHom.commutes,
          algebraMap_smul] }
    fun a b ↦ by
      change kq δ (w (a * b)) = a • kq δ (w b) + b • kq δ (w a)
      rw [hw, map_add, map_smul, map_smul, smulC, smulC]
  have hv : ∀ c, v c = kq δ (w c) := fun _ ↦ rfl
  have key : ∀ ω : Ω[C⁄R], ∃ η : Ω[B⁄R], v.liftKaehlerDifferential ω = Ideal.Quotient.mk (rel R δ) (ι1 η) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      obtain ⟨η, hη⟩ := Submodule.Quotient.mk_surjective _ (w c)
      refine ⟨π b • η, ?_⟩
      rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hv, ← hη, kq_mk, smulC, map_smul,
        Algebra.smul_def (π b) (ι1 η), map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
    | h0 => exact ⟨0, by simp⟩
    | ha x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
  let Φ : DR R C →ₐ[C] DR R B ⧸ rel R δ := ExteriorAlgebra.lift C ⟨v.liftKaehlerDifferential, fun m ↦ by
    obtain ⟨η, h⟩ := key m
    rw [h, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩
  have hΦι : ∀ ω : Ω[C⁄R], Φ (ι1 ω) = v.liftKaehlerDifferential ω := fun ω ↦ ExteriorAlgebra.lift_ι_apply _ _ _ _
  have hΦD : ∀ c, Φ (ι1 (D R C c)) = kq δ (w c) := fun c ↦ by
    rw [hΦι, Derivation.liftKaehlerDifferential_comp_D, hv]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DR R C → DR R B, ∀ x, Ideal.Quotient.mk (rel R δ) (ρ x) = Φ x :=
    ⟨_, fun x ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (Φ x)⟩
  have cv : ∀ x a, ρ x - a ∈ rel R δ ↔ Φ x = Ideal.Quotient.mk (rel R δ) a := fun x a ↦ by
    rw [← Ideal.Quotient.eq, hρ]
  refine ⟨ρ, fun x y ↦ ?_, fun x y ↦ ?_, fun c ↦ ?_, fun c ω h ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun j x hx ↦ ?_⟩
  · rw [sub_sub]
    exact (cv _ _).2 (by rw [map_add, map_add, hρ, hρ])
  · exact (cv _ _).2 (by rw [map_mul, map_mul, hρ, hρ])
  · exact (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)
  · exact (cv _ _).2 (by rw [hΦD, ← h, kq_mk])
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hρ]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, a, ha, rfl⟩ := hx
      rw [map_sub, map_smul, map_sub, map_smul, hΦD, hΦD, hwd n a ha, map_smul, smulC, sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ ih => rw [smul_eq_mul, map_mul, ih, mul_zero]
  · obtain ⟨η, h⟩ := key x
    exact ⟨η, (cv _ _).2 (by rw [hΦι, h])⟩
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap c =>
      refine ⟨algebraMap B _ (π c), ?_, (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)⟩
      change _ ∈ LinearMap.range _ ^ 0
      rw [pow_zero]; exact Submodule.algebraMap_mem _
    | add x y i _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, (cv _ _).2 (by rw [map_add, (cv _ _).1 ha', (cv _ _).1 hb', map_add])⟩
    | mem_mul m hm i x hx ih =>
      obtain ⟨ω, rfl⟩ := hm
      obtain ⟨η, hη⟩ := key ω
      obtain ⟨y, hy, hy'⟩ := ih
      refine ⟨ι1 η * y, ?_, (cv _ _).2 ?_⟩
      · have := GlobalTheory.CechDR.mul_mem (ι_mem η) hy
        rwa [add_comm] at this
      · rw [map_mul, (cv _ _).1 hy', map_mul, ← hη, ← hΦι]

end GlobalTheory.PDForm
