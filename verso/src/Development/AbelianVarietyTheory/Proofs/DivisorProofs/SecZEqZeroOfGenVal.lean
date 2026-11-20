import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagTan GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨hL, -, hG, hA⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c`. Take `⟨C, ψ, z0, t', hψ, hb⟩` from `hA hG L z`. Rewrite using `[evR_frBor hg hb]`. Establish `hnat` using `(mem_secZ.mp hg).1`. Take `⟨p, φ0, u, hu⟩` from `hL.test C.R C.y`.

Establish `e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u)` using `evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))`. Establish `e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u)` using `evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))`. Establish `e3` using `evR_frBor hg C.bor`. Establish `e4 : evR Xo c g (genFr hG C.Z) = 0`. Establish `h1` using `h0 C.Z`.

Rewrite `h1` using `[genVal_apply hG]`. Conclude with `h1`. Rewrite `e3` using `[e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val]`. Establish `e5 : φ0 (g p u) = 0` using `Subtype.ext e3`. Rewrite using `[e1, AlgHom.comp_apply, e5, map_zero, mul_zero]`.
-/
private theorem evR_eq_zero_of_genVal_eq_zero {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) {L : Type} [Field L] [Algebra c.F L] (z : FrPt Xo c L) :
    evR Xo c g z = 0 := by
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z0, t', hψ, hb⟩ := hA hG L z
  rw [evR_frBor hg hb]
  have hnat := (mem_secZ.mp hg).1
  obtain ⟨p, φ0, u, hu⟩ := hL.test C.R C.y
  have e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u) :=
    evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))
  have e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u) :=
    evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))
  have e3 := evR_frBor hg C.bor
  have e4 : evR Xo c g (genFr hG C.Z) = 0 := by
    have h1 := h0 C.Z
    rw [genVal_apply hG] at h1
    exact h1
  rw [e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val] at e3
  have e5 : φ0 (g p u) = 0 := Subtype.ext e3
  rw [e1, AlgHom.comp_apply, e5, map_zero, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p u`. Take `⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u` from `Ideal.Quotient.mk_surjective _`. Use `show g p u = 0`. Rewrite using `[← ha, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hJ : p.I.jacobson = p.I` using `by first`.

Consider the case `exact IsJacobsonRing.out' _ p.rad`. Consider the case `exact IsJacobsonRing.out inferInstance p.rad`. Consider the case `exact Ideal.IsJacobson.out' _ p.rad`. Rewrite using `[← hJ, Ideal.jacobson, Submodule.mem_sInf]`. Introduce and unpack `m ⟨hIm, hm⟩`.

Use `letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m`. Set `φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m` to `Ideal.Quotient.factorₐ c.F hIm`. Take `⟨z, hz⟩` from `exists_frMap φ u`. Establish `h1` using `evR_eq (mem_secZ.mp hg).1 hz`. Rewrite `h1` using `[evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha]`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h1.symm`.
-/
theorem secZ_eq_zero_of_genVal {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) : g = 0 :=by
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u := Ideal.Quotient.mk_surjective _
  show g p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := by
    first
    | exact IsJacobsonRing.out' _ p.rad
    | exact IsJacobsonRing.out inferInstance p.rad
    | exact Ideal.IsJacobson.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m := Ideal.Quotient.factorₐ c.F hIm
  obtain ⟨z, hz⟩ := exists_frMap φ u
  have h1 := evR_eq (mem_secZ.mp hg).1 hz
  rw [evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha] at h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h1.symm

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Z e f hf`. Take `⟨-, -, hG, -⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c`. Prove the components needed by the constructor for the conclusion. Introduce `h0 S _ _ y hy`. Distinguish the cases in `ht : Tested y`.

Establish `hz : idem Z * f = 0`. Use `secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)` and prove the remaining obligations. Distinguish the cases in `hZ : Z' = Z`. Substitute `hZ` using the available equality. Rewrite using `[map_mul, h0, mul_zero]`.

Rewrite using `[genVal_apply hG]`. Conclude with `evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))`. Establish `h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y` using `evalAt_mul _ _ _ _ y`. Rewrite `h1` using `[hz, evR_idem hy ht, one_mul]`. Rewrite using `[← h1]`.

Conclude with `evalAt_zero _ _ y`. Unfold `evR evalAt`. Rewrite using `[dif_neg ht]`. Introduce `hall`. Rewrite using `[genVal_apply hG]`.

Conclude with `hall _ _ (liesOn_genFr hG Z)`.
-/
theorem genVal_eq_zero_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Z : Comp Xo c) (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, genVal Z f = 0 ↔ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c f y = 0 :=by
  intro E _ _ _ H Dw l Xo c Z e f hf
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  constructor
  · intro h0 S _ _ y hy
    by_cases ht : Tested y
    · have hz : idem Z * f = 0 := by
        refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)
        by_cases hZ : Z' = Z
        · subst hZ
          rw [map_mul, h0, mul_zero]
        · rw [genVal_apply hG]
          exact evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))
      have h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y := evalAt_mul _ _ _ _ y
      rw [hz, evR_idem hy ht, one_mul] at h1
      rw [← h1]
      exact evalAt_zero _ _ y
    · unfold evR evalAt
      rw [dif_neg ht]
  · intro hall
    rw [genVal_apply hG]
    exact hall _ _ (liesOn_genFr hG Z)

end GlobalTheory.CompHt
