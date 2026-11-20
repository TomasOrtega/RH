import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.Places

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

namespace UpperTheory.TraceSumEquivalence

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O C)` using `hv.hom_inj`. Establish `hmem : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), σ (y : E) ∈ (algebraMap O C).range`. Introduce `σ y`. Establish `hi : IsIntegral ℤ (σ (y : E))` using `(RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom`. Establish `hi' : IsIntegral O (σ (y : E))` using `hi.tower_top`.

Take `⟨z, hz⟩` from `hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hi')`. Conclude with `⟨z, hz⟩`. Set `e : O ≃+* (algebraMap O C).range` to `RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)`. Establish `he : ∀ z, algebraMap O C (e.symm z) = z`. Introduce `z`.

Take `⟨a, ha⟩` from `z.2`. Use `show algebraMap O C (Function.invFun (algebraMap O C) z) = z`. Conclude with `Function.invFun_eq ⟨a, ha⟩`. Set `F : (E →ₐ[ℚ] C) → (𝓞 E →+* O)` to `fun σ => e.symm.toRingHom.comp ((σ.toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _ (hmem σ))`. Establish `hF : ∀ σ (y : 𝓞 E), algebraMap O C (F σ y) = σ (y : E)` using `fun σ y => he _`.

Establish `hFi : Function.Injective F`. Introduce `σ τ h`. Establish `h1 : σ.toRingHom.comp (algebraMap (𝓞 E) E) = τ.toRingHom.comp (algebraMap (𝓞 E) E)`. Use extensionality with `y`. Use `congrArg (fun φ : 𝓞 E →+* O => algebraMap O C (φ y)) h` as an intermediate fact.

Simplify using `only [hF] at this`. Conclude with `this`. Establish `h2 : σ.toRingHom = τ.toRingHom` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h1`. Conclude with `AlgHom.coe_ringHom_injective h2`. Establish `hFs : Function.Surjective F`.

Introduce `τ`. Set `g : 𝓞 E →+* C` to `(algebraMap O C).comp τ`. Establish `hg : Function.Injective g`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises.

Rewrite using `[RingHom.comap_ker]`. Establish `: g.comp (algebraMap ℤ (𝓞 E)) = Int.castRingHom C` using `RingHom.ext_int _ _`. Rewrite using `[this]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mp Int.cast_injective`. Use `⟨(IsFractionRing.lift hg : E →+* C).toRatAlgHom, ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hF]`. Conclude with `IsFractionRing.lift_algebraMap hg y`. Conclude with `⟨Equiv.ofBijective F ⟨hFi, hFs⟩, hF⟩`.
-/
private theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  classical
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hmem : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), σ (y : E) ∈ (algebraMap O C).range := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) :=
      (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    obtain ⟨z, hz⟩ := hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hi')
    exact ⟨z, hz⟩
  let e : O ≃+* (algebraMap O C).range :=
    RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)
  have he : ∀ z, algebraMap O C (e.symm z) = z := by
    intro z
    obtain ⟨a, ha⟩ := z.2
    show algebraMap O C (Function.invFun (algebraMap O C) z) = z
    exact Function.invFun_eq ⟨a, ha⟩
  let F : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    e.symm.toRingHom.comp ((σ.toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _ (hmem σ))
  have hF : ∀ σ (y : 𝓞 E), algebraMap O C (F σ y) = σ (y : E) := fun σ y => he _
  have hFi : Function.Injective F := by
    intro σ τ h
    have h1 : σ.toRingHom.comp (algebraMap (𝓞 E) E) = τ.toRingHom.comp (algebraMap (𝓞 E) E) := by
      ext y
      have := congrArg (fun φ : 𝓞 E →+* O => algebraMap O C (φ y)) h
      simp only [hF] at this
      exact this
    have h2 : σ.toRingHom = τ.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h1
    exact AlgHom.coe_ringHom_injective h2
  have hFs : Function.Surjective F := by
    intro τ
    let g : 𝓞 E →+* C := (algebraMap O C).comp τ
    have hg : Function.Injective g := by
      rw [RingHom.injective_iff_ker_eq_bot]
      apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
      rw [RingHom.comap_ker]
      have : g.comp (algebraMap ℤ (𝓞 E)) = Int.castRingHom C := RingHom.ext_int _ _
      rw [this]
      exact (RingHom.injective_iff_ker_eq_bot _).mp Int.cast_injective
    refine ⟨(IsFractionRing.lift hg : E →+* C).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hF]
    exact IsFractionRing.lift_algebraMap hg y
  exact ⟨Equiv.ofBijective F ⟨hFi, hFs⟩, hF⟩

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb`. Establish `hadd : LinearMap.mulLeft ℤ_[p] (a + b) = LinearMap.mulLeft ℤ_[p] a + LinearMap.mulLeft ℤ_[p] b`. Use extensionality with `z`.

Simplify using `[add_mul]`. Rewrite using `[hadd, map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]`. Simplify using `[map_add]`. Consider the case `tmul c y`. Establish `h0 : (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) = c • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `h1 : LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) = c • (Algebra.lmul ℤ (𝓞 E) y).baseChange ℤ_[p]`. Rewrite using `[Algebra.baseChange_lmul, h0]`. Use extensionality with `z`. Simplify using `[smul_mul_assoc]`.

Establish `h2 : LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E)) = c * ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℤ_[p])`. Rewrite using `[h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]`. Simplify using the standard rewrite rules. Establish `h3 : ∑ σ : E →ₐ[ℚ] C, σ (y : E) = (((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) : C)`. Rewrite using `[Algebra.coe_trace_int, ← eq_ratCast (algebraMap ℚ C), trace_eq_sum_embeddings]`.

Rewrite using `[h2]`. Simplify using `only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul]`. Establish `h4 : ∀ σ : E →ₐ[ℚ] C, algebraMap O C ((Φ σ).toIntAlgHom y) = σ (y : E)` using `fun σ => hΦ σ y`. Simplify using `only [h4, Algebra.ofId_apply, ← Finset.mul_sum, h3, map_intCast, Rat.cast_intCast]`.
-/
private theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    have hadd : LinearMap.mulLeft ℤ_[p] (a + b) = LinearMap.mulLeft ℤ_[p] a + LinearMap.mulLeft ℤ_[p] b := by
      ext z
      simp [add_mul]
    rw [hadd, map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    simp [map_add]
  | tmul c y =>
    have h0 : (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) = c • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h1 : LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) =
        c • (Algebra.lmul ℤ (𝓞 E) y).baseChange ℤ_[p] := by
      rw [Algebra.baseChange_lmul, h0]
      ext z
      simp [smul_mul_assoc]
    have h2 : LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        c * ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℤ_[p]) := by
      rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]
      simp
    have h3 : ∑ σ : E →ₐ[ℚ] C, σ (y : E) = (((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) : C) := by
      rw [Algebra.coe_trace_int, ← eq_ratCast (algebraMap ℚ C), trace_eq_sum_embeddings]
    rw [h2]
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul]
    have h4 : ∀ σ : E →ₐ[ℚ] C, algebraMap O C ((Φ σ).toIntAlgHom y) = σ (y : E) := fun σ => hΦ σ y
    simp only [h4, Algebra.ofId_apply, ← Finset.mul_sum, h3, map_intCast, Rat.cast_intCast]

end UpperTheory.TraceSumEquivalence

open UpperTheory.TraceSumEquivalence in

/- English proof (translation)
Introduce `E _ _ p _ C _ _ _ v O _ _ hv _ e he`. Take `⟨Φ, hΦ⟩` from `exists_equiv E C v O hv`. Establish `hcard : Nat.card (𝓞 E →+* O) = Module.finrank ℚ E`. Rewrite using `[← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]`. Use `⟨?_, hcard⟩` and prove the remaining obligations.

Use `haveI : IsDomain O := hv.hom_inj.isDomain _`. Set `f` to `LinearMap.mulLeft ℤ_[p] e`. Establish `hf : IsIdempotentElem f` using `by show f * f = f`. Use extensionality with `z`. Simplify using `[f, ← mul_assoc, he]`.

Establish `htr : LinearMap.trace ℤ_[p] _ f = (Module.finrank ℤ_[p] (LinearMap.range f) : ℤ_[p])` using `((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf).trace`. Establish `hsum` using `trace_eq_sum E p C O Φ hΦ e`. Establish `hval : ∀ σ, algebraMap O C (tauExt (Φ σ) e) = if Φ σ ∈ Emb (O` using `O) e then 1 else 0 := by`. Introduce `σ`. Establish `hid : IsIdempotentElem (tauExt (Φ σ) e)` using `by show _ * _ = _`.

Rewrite using `[← map_mul, he]`. Break down `IsIdempotentElem.iff_eq_zero_or_one.mp hid with h | h` into its components or cases. Establish `hn : Φ σ ∉ Emb (O` using `O) e := by show ¬ (tauExt (Φ σ) e = 1)`. Rewrite using `[h]`. Conclude with `zero_ne_one`.

Rewrite using `[if_neg hn, h, map_zero]`. Establish `hm : Φ σ ∈ Emb (O` using `O) e := h`. Rewrite using `[if_pos hm, h, map_one]`. Establish `hsum' : ((Module.finrank ℤ_[p] (LinearMap.range f) : ℕ) : C) = ((Finset.univ.filter (fun σ => Φ σ ∈ Emb (O` using `O) e)).card : C) := by`. Establish `h` using `hsum`.

Express the relevant statement in the definitionally equal form `algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ f)) = _ at h`. Rewrite `h` using `[htr, map_natCast, map_natCast]`. Rewrite using `[h]`. Simplify using `only [hval]`. Rewrite using `[Finset.sum_boole]`.

Establish `hn` using `Nat.cast_injective hsum'`. Use `haveI : Finite (𝓞 E →+* O) := Finite.of_equiv _ Φ`. Establish `hEmb : Nat.card (Emb (O` using `O) e) = (Finset.univ.filter (fun σ => Φ σ ∈ Emb (O := O) e)).card := by`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨(finCongr (hn.trans hEmb.symm)).trans (Finite.equivFin _).symm⟩`.
-/
theorem UpperTheory.trace_form_decomposition_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e →
      Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  intro E _ _ p _ C _ _ _ v O _ _ hv _ e he
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv E C v O hv
  have hcard : Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
    rw [← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]
  refine ⟨?_, hcard⟩
  haveI : IsDomain O := hv.hom_inj.isDomain _
  let f := LinearMap.mulLeft ℤ_[p] e
  have hf : IsIdempotentElem f := by
    show f * f = f
    ext z
    simp [f, ← mul_assoc, he]
  have htr : LinearMap.trace ℤ_[p] _ f = (Module.finrank ℤ_[p] (LinearMap.range f) : ℤ_[p]) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf).trace
  have hsum := trace_eq_sum E p C O Φ hΦ e
  have hval : ∀ σ, algebraMap O C (tauExt (Φ σ) e) = if Φ σ ∈ Emb (O := O) e then 1 else 0 := by
    intro σ
    have hid : IsIdempotentElem (tauExt (Φ σ) e) := by
      show _ * _ = _
      rw [← map_mul, he]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h | h
    · have hn : Φ σ ∉ Emb (O := O) e := by
        show ¬ (tauExt (Φ σ) e = 1)
        rw [h]
        exact zero_ne_one
      rw [if_neg hn, h, map_zero]
    · have hm : Φ σ ∈ Emb (O := O) e := h
      rw [if_pos hm, h, map_one]
  have hsum' : ((Module.finrank ℤ_[p] (LinearMap.range f) : ℕ) : C) =
      ((Finset.univ.filter (fun σ => Φ σ ∈ Emb (O := O) e)).card : C) := by
    have h := hsum
    change algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ f)) = _ at h
    rw [htr, map_natCast, map_natCast] at h
    rw [h]
    simp only [hval]
    rw [Finset.sum_boole]
  have hn := Nat.cast_injective hsum'
  haveI : Finite (𝓞 E →+* O) := Finite.of_equiv _ Φ
  have hEmb : Nat.card (Emb (O := O) e) =
      (Finset.univ.filter (fun σ => Φ σ ∈ Emb (O := O) e)).card := by
    calc Nat.card (Emb (O := O) e) = Nat.card {σ // Φ σ ∈ Emb (O := O) e} :=
          (Nat.card_congr (Φ.subtypeEquiv (fun σ => Iff.rfl))).symm
      _ = Fintype.card {σ // Φ σ ∈ Emb (O := O) e} := Nat.card_eq_fintype_card
      _ = _ := Fintype.card_subtype _
  exact ⟨(finCongr (hn.trans hEmb.symm)).trans (Finite.equivFin _).symm⟩
