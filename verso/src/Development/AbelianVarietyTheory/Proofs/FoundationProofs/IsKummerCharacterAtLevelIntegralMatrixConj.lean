import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Rewrite using `[Filter.Germ.coe_eq]`. Conclude with `Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h z hz)`.
-/
theorem germ_eq_of_eqOn_Hs {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  rw [Filter.Germ.coe_eq]
  exact Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h z hz)

/- English proof (translation)
Introduce `Ω _ _ ε X l _ n m x χ hm hK`. Take `⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩` from `hK`. Take `⟨mobHs, mobMul, mobOne, mobDiff, -, -⟩` from `GlobalTheory.T.glTwoPosRatMobius_basic_laws`. Take `⟨cj1, -, cj3⟩` from `GlobalTheory.T.integralConjugateSL2Int_laws`. Take `⟨-, -, gcomp, -, -⟩` from `GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties`.

Establish `hcls` using `(GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.2.1 (X.sl (toGQ m)).toRingEquiv x f hx`. Use `⟨Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f, fun z => a (mob (toGQ m) z), fun z => b (mob (toGQ m) z), M * m.det.natAbs, ?_, hcls, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Nat.mul_pos hM (Int.natAbs_pos.2 hm.ne')`. Conclude with `ha.comp (mobDiff _) (fun z hz => mobHs _ z hz)`. Conclude with `hb.comp (mobDiff _) (fun z hz => mobHs _ z hz)`.

Introduce `h0`. Apply `hb0` to reduce the goal to its premises. Establish `h0' : ((fun z => b (mob (toGQ m) z) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero)` using `h0`. Establish `h1` using `gcomp (toGQ m)⁻¹ _ _ h0'`. Combine the equalities or inequalities in the displayed calculation.

Use `germ_eq_of_eqOn_Hs fun z hz => ?_` and prove the remaining obligations. Rewrite using `[← mobMul _ _ z hz, mul_inv_cancel, mobOne]`. Use `_ = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h1`. Use `_ = 0 := rfl`. Take `⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero)` from `(Quotient.exists_rep (X.an (f : X.K))).imp fun _ h => h.symm`.

Establish `h1 : X.an ((Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K) = ((fun z => φ (mob (toGQ m) z) : ℂ → ℂ) : Mero)` using `X.an_sl (toGQ m) f φ hφ`. Rewrite using `[h1]`. Rewrite `hab` using `[hφ]`. Establish `e` using `gcomp (toGQ m) (φ * b ^ (l ^ n)) (a ^ (l ^ n)) (by rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab)`. Rewrite using `[← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]`.

Conclude with `e`. Introduce `δ hδ z hz`. Take `⟨hmδ, hcj⟩` from `cj1 m M hm δ hδ`. Establish `e` using `cj3 m δ (cj m δ) hm hmδ z hz`. Use `show a (mob (toGQ m) (mob (ofSL δ) z)) * b (mob (toGQ m) z) = _ * (a (mob (toGQ m) z) * b (mob (toGQ m) (mob (ofSL δ) z)))`.

Rewrite using `[e]`. Conclude with `hrel (cj m δ) hcj (mob (toGQ m) z) (mobHs _ z hz)`.
-/
theorem kum_kmap_sl : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det →
      Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  intro Ω _ _ ε X l _ n m x χ hm hK
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩ := hK
  obtain ⟨mobHs, mobMul, mobOne, mobDiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨cj1, -, cj3⟩ := GlobalTheory.T.integralConjugateSL2Int_laws
  obtain ⟨-, -, gcomp, -, -⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  have hcls := (GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.2.1 (X.sl (toGQ m)).toRingEquiv x f hx
  refine ⟨Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f, fun z => a (mob (toGQ m) z),
    fun z => b (mob (toGQ m) z), M * m.det.natAbs, ?_, hcls, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Nat.mul_pos hM (Int.natAbs_pos.2 hm.ne')
  · exact ha.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · exact hb.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · intro h0
    apply hb0
    have h0' : ((fun z => b (mob (toGQ m) z) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h0
    have h1 := gcomp (toGQ m)⁻¹ _ _ h0'
    calc (b : Mero) = ((fun z => b (mob (toGQ m) (mob (toGQ m)⁻¹ z)) : ℂ → ℂ) : Mero) := by
          refine germ_eq_of_eqOn_Hs fun z hz => ?_
          rw [← mobMul _ _ z hz, mul_inv_cancel, mobOne]
      _ = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h1
      _ = 0 := rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
      (Quotient.exists_rep (X.an (f : X.K))).imp fun _ h => h.symm
    have h1 : X.an ((Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K) =
        ((fun z => φ (mob (toGQ m) z) : ℂ → ℂ) : Mero) := X.an_sl (toGQ m) f φ hφ
    rw [h1]
    rw [hφ] at hab
    have e := gcomp (toGQ m) (φ * b ^ (l ^ n)) (a ^ (l ^ n))
      (by rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab)
    rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]
    exact e
  · intro δ hδ z hz
    obtain ⟨hmδ, hcj⟩ := cj1 m M hm δ hδ
    have e := cj3 m δ (cj m δ) hm hmδ z hz
    show a (mob (toGQ m) (mob (ofSL δ) z)) * b (mob (toGQ m) z) = _ * (a (mob (toGQ m) z) * b (mob (toGQ m) (mob (ofSL δ) z)))
    rw [e]
    exact hrel (cj m δ) hcj (mob (toGQ m) z) (mobHs _ z hz)

end GlobalTheory.KZ.H3
