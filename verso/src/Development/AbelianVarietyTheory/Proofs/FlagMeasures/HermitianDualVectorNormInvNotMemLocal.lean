import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.LocNot

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `ι : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F` to `Algebra.TensorProduct.includeRight`. Use `letI : Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) := (ι.toRingHom.comp (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra`. Set `ιO : v.adicCompletion F →ₐ[v.adicCompletionIntegers F] E ⊗[F] v.adicCompletion F` to `{ ι.toRingHom with commutes' := fun _ => rfl }`. Establish `hinj : Function.Injective ιO` using `Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective`. Establish `hle : intV E v ≤ (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring`.

Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)`. Take `⟨a, rfl⟩` from `he`. Take `⟨p, hp, hpe⟩` from `RingOfIntegers.isIntegral_coe a`. Use `⟨p.map (Int.castRingHom _), hp.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Set `g : E →+* E ⊗[F] v.adicCompletion F` to `Algebra.TensorProduct.includeLeftRingHom`. Establish `hc : (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).comp (Int.castRingHom _) = g.comp (algebraMap ℤ E)` using `RingHom.ext_int _ _`. Establish `h3` using `congrArg g hpe`. Rewrite `h3` using `[Polynomial.hom_eval₂, map_zero]`.

Rewrite using `[hc]`. Conclude with `h3`. Conclude with `isIntegral_algebraMap (x := (⟨c, hc⟩ : v.adicCompletionIntegers F))`. Establish `hi : IsIntegral (v.adicCompletionIntegers F) t` using `(isIntegral_algHom_iff ιO hinj).1 (hle ht)`. Take `⟨b, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`.

Conclude with `b.2`.
-/
theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F)
    (ht : (1 : E) ⊗ₜ[F] t ∈ intV E v) : t ∈ v.adicCompletionIntegers F := by
  classical
  let ι : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeRight
  letI : Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
    (ι.toRingHom.comp (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  let ιO : v.adicCompletion F →ₐ[v.adicCompletionIntegers F] E ⊗[F] v.adicCompletion F :=
    { ι.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ιO :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  have hle : intV E v ≤
      (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      obtain ⟨p, hp, hpe⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      let g : E →+* E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeLeftRingHom
      have hc : (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).comp
          (Int.castRingHom _) = g.comp (algebraMap ℤ E) := RingHom.ext_int _ _
      have h3 := congrArg g hpe
      rw [Polynomial.hom_eval₂, map_zero] at h3
      rw [hc]
      exact h3
    · exact isIntegral_algebraMap (x := (⟨c, hc⟩ : v.adicCompletionIntegers F))
  have hi : IsIntegral (v.adicCompletionIntegers F) t := (isIntegral_algHom_iff ιO hinj).1 (hle ht)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

end GlobalTheory.St.G.LocNot

namespace GlobalTheory.St.G

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm n J L hL d T hT hd hdd v hv`. Set `x : Fin n → E ⊗[F] v.adicCompletion F` to `fun i => inclE (F := F) (v.adicCompletion F) (d i)`. Use `⟨x, Submodule.subset_span ⟨d, hd, rfl⟩, fun hx => ?_⟩` and prove the remaining obligations. Establish `hLd : L ≤ dualL cm.sig J L` using `fun y hy => Submodule.subset_span (hL y hy)`. Establish `hx' : x ∈ loc v (dualL cm.sig J L)` using `Submodule.span_mono (Set.image_mono hLd) hx`.

Establish `hxx` using `Dual.fwd cm.sig J (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring L x hx' x hx`. Rewrite `hxx` using `[Dual.hR_incl]`. Take `⟨a, ha⟩` from `hdd`. Establish `h1 : inclE (F` using `F) (v.adicCompletion F) ((T : E)⁻¹) ∈ intV E v := by`. Establish `he : Formalism.UG.hform (cm.sig : E →+* E) J d d = algebraMap (𝓞 E) E a + (T : E)⁻¹`.

Rewrite using `[ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxx` using `[he, map_add]`. Establish `ha' : inclE (F` using `F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) ∈ intV E v := Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)`. Use `sub_mem hxx ha'` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `h2 : inclE (F` using `F) (v.adicCompletion F) ((T : E)⁻¹) = (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) := by`. Establish `e1 : ((T : E))⁻¹ = ((T : F))⁻¹ • (1 : E)`. Rewrite using `[Algebra.smul_def, mul_one, map_inv₀, map_natCast]`. Establish `e2 : ((T : v.adicCompletion F))⁻¹ = ((T : F))⁻¹ • (1 : v.adicCompletion F)`.

Rewrite using `[Algebra.smul_def, mul_one, map_inv₀, map_natCast]`. Rewrite using `[e1, e2]`. Use `show ((T : F)⁻¹ • (1 : E)) ⊗ₜ[F] (1 : v.adicCompletion F) = _`. Rewrite using `[TensorProduct.smul_tmul]`. Rewrite `h1` using `[h2]`.

Establish `h3` using `LocNot.mem_of_tmul_mem v _ h1`. Rewrite `h3` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hval : Valued.v (T : v.adicCompletion F) < 1`. Establish `hv1` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (T : 𝓞 F)`. Establish `hv2` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (T : 𝓞 F)).2 hv`.

Rewrite `hv2` using `[← hv1]`. Use `hv2 using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `hne : (T : v.adicCompletion F) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F (v.adicCompletion F))]`.

Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 hT.ne')`. Rewrite `h3` using `[map_inv₀]`. Establish `hpos : 0 < Valued.v (T : v.adicCompletion F)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)`. Establish `h4 : 1 ≤ Valued.v (T : v.adicCompletion F)` using `(inv_le_one₀ hpos).1 h3`. Conclude with `absurd hval (not_lt.2 h4)`.
-/
theorem dual_not_loc_of_norm_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  intro F E _ _ _ _ _ _ cm n J L hL d T hT hd hdd v hv
  let x : Fin n → E ⊗[F] v.adicCompletion F := fun i => inclE (F := F) (v.adicCompletion F) (d i)
  refine ⟨x, Submodule.subset_span ⟨d, hd, rfl⟩, fun hx => ?_⟩
  have hLd : L ≤ dualL cm.sig J L := fun y hy => Submodule.subset_span (hL y hy)
  have hx' : x ∈ loc v (dualL cm.sig J L) := Submodule.span_mono (Set.image_mono hLd) hx
  have hxx := Dual.fwd cm.sig J (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring L x hx' x hx
  rw [Dual.hR_incl] at hxx
  obtain ⟨a, ha⟩ := hdd
  have h1 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) ∈ intV E v := by
    have he : Formalism.UG.hform (cm.sig : E →+* E) J d d = algebraMap (𝓞 E) E a + (T : E)⁻¹ := by
      rw [ha]; ring
    rw [he, map_add] at hxx
    have ha' : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) ∈ intV E v :=
      Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
    have := sub_mem hxx ha'
    rwa [add_sub_cancel_left] at this
  have h2 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) =
      (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) := by
    have e1 : ((T : E))⁻¹ = ((T : F))⁻¹ • (1 : E) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    have e2 : ((T : v.adicCompletion F))⁻¹ = ((T : F))⁻¹ • (1 : v.adicCompletion F) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    rw [e1, e2]
    show ((T : F)⁻¹ • (1 : E)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [TensorProduct.smul_tmul]
  rw [h2] at h1
  have h3 := LocNot.mem_of_tmul_mem v _ h1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
  have hval : Valued.v (T : v.adicCompletion F) < 1 := by
    have hv1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (T : 𝓞 F)
    have hv2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (T : 𝓞 F)).2 hv
    rw [← hv1] at hv2
    convert hv2 using 2
    simp
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT.ne')
  rw [map_inv₀] at h3
  have hpos : 0 < Valued.v (T : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have h4 : 1 ≤ Valued.v (T : v.adicCompletion F) := (inv_le_one₀ hpos).1 h3
  exact absurd hval (not_lt.2 h4)

end GlobalTheory.St.G
