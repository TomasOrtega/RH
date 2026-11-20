import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariantStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g`. Take `⟨-, -, -, h4, -, -, -, -, ha⟩` from `GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v`. Take `⟨-, hact⟩` from `ha a`. Use `haveI := h4`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`.

Establish `hc : ∀ k : HA (Fv F v) σ J, Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X)` using `fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)`. Set `T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E)` to `{ toFun := fun X => g • X invFun := fun X => g⁻¹ • X left_inv := fun X => inv_smul_smul g X right_inv := fun X => smul_inv_smul g X continuous_toFun := hc g continuous_invFun := hc g⁻¹ }`. Set `Tm` to `T.toMeasurableEquiv`. Establish `hTm : ∀ X, Tm X = g • X` using `fun X => rfl`. Establish `hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X`.

Introduce `X`. Use function extensionality and compare the values at `i j`. Conclude with `hR_lin g (X i) (X j)`. Establish `hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X)`. Introduce `k X hX`.

Establish `hinj : Function.Injective (lin (Fv F v) σ J k)` using `Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))`. Conclude with `hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)`. Establish `hpre : ∀ b : HermR (Fv F v) σ a, Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) = gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}`. Introduce `b`. Use extensionality with `X`.

Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]`. Use `and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩` and prove the remaining obligations. Use `hli g⁻¹ _ h` as an intermediate fact. Rewrite `this` using `[inv_smul_smul]`. Then use the resulting hypothesis. Establish `hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} = {X | LinearIndependent (Fv F v ⊗[F] E) X}`.

Use extensionality with `X`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, hTm]`. Use `⟨fun h => ?_, hli g X⟩` and prove the remaining obligations. Use `hli g⁻¹ _ h` as an intermediate fact. Rewrite `this` using `[inv_smul_smul]`. Then use the resulting hypothesis.

Establish `hμT : μ.map Tm = μ` using `GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g`. Set `fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E)` to `fun b => (fib b).map Tm`. Establish `hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib'`. Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩` and prove the remaining obligations. Use `show (fib b).map Tm _ = 0`.

Rewrite using `[Tm.map_apply, Set.preimage_compl, hpre]`. Conclude with `hfib.1 b`. Establish `e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b)` using `fun b => lintegral_map_equiv φ Tm (μ := fib b)`. Simplify using `only [e1]`. Rewrite using `[← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]`.

Use `conv_lhs => rw [← hμT]`. Rewrite using `[Tm.restrict_map, lintegral_map_equiv, hU]`. Establish `h3` using `hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by show tsupport (φ ∘ T) ⊆ _`. Rewrite using `[tsupport_comp_eq_preimage φ T]`. Introduce `X hX`.

Establish `: Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X}` using `hφU hX`. Rewrite `this` using `[← Set.mem_preimage, hU]`. Conclude with `this)`. Use `⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩` and prove the remaining obligations. Use `h3.2.congr fun b _ => ?_` and prove the remaining obligations.

Conclude with `MeasureTheory.integral_map_equiv Tm φ`. Establish `hu` using `GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'`. Use `show (fib S).map Tm = fib S`. Conclude with `(congrFun hu S).symm`.
-/
theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
