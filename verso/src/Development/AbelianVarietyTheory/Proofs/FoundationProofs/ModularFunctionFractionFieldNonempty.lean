import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMapsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHomStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomainStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFunStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ _ _ ε`. Use `haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range`. Take `⟨hmem, hconst⟩` from `GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range`. Take `⟨-, huniq, hC, -, -⟩` from `GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε`. Take `⟨e, he_inj, he_exp⟩` from `GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε`.

Take `⟨hexp_mem, -, -, -, -, -⟩` from `GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε`. Take `⟨⟨G, hG⟩, hmd, -, -, hHs⟩` from `GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict`. Take `⟨-, hid, hunit⟩` from `GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units`. Set `cst : Ω →+* ring ε.range` to `{ toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩ map_one' := Subtype.ext (funext fun _ => by simp) map_mul' := fun x y => Subtype.ext (funext fun _ => by simp) map_zero' := Subtype.ext (funext fun _ => by simp) map_add' := fun x y => Subtype.ext (funext fun _ => …`. Establish `hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x` using `fun _ => rfl`.

Establish `hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x`. Introduce `x`. Use `huniq _ _ _ (he_exp (cst x)) ?_` and prove the remaining obligations. Use `hC x using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.

Simplify using `[HahnSeries.algebraMap_apply']`. Establish `hsl` using `fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem`. Use `choose σ hσ using hsl`. Establish `hslc : ∀ g x, σ g (cst x) = cst x`. Introduce `g x`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hσ]`. Both sides reduce to the same expression. Establish `hga` using `fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv`. Use `choose τ hτ using hga`.

Set `A : ring ε.range →+* Mero` to `G.comp (ring ε.range).subtype`. Establish `hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero)` using `fun a => hG a`. Establish `hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs` using `fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))`. Establish `hAunit : ∀ a, a ≠ 0 → IsUnit (A a)`. Introduce `a ha`.

Rewrite using `[hA]`. Use `(hunit _ (hdiff a) ?_).2` and prove the remaining obligations. Introduce `h0`. Apply `ha` to reduce the goal to its premises. Establish `h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero)`.

Rewrite using `[h0, ← hA, map_zero]`. Establish `heq` using `hid _ _ (hdiff a) (hdiff 0) h0'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `t`. Use `heq t (hHs t)` as an intermediate fact.

Simplify `this` using `[up, UpperHalfPlane.ofComplex_apply]`. Take `⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩` from `GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit`. Use `⟨{ K := K fld := fK alg := aK io := io io_inj := hinj io_surj := hsurj io_c := fun x a ha => ?_ exp := e' exp_io := fun a => ?_ sl := sl' sl_io := fun g a a' ha => ?_ gal := ga' gal_exp := fun s f r => ?_ an := A' an_io := fun a => ?_ }⟩` and prove the remaining obligations. Establish `: a = cst x` using `Subtype.ext ha`. Rewrite using `[this, hioc]`.

Rewrite using `[he']`. Conclude with `he_exp a`. Rewrite using `[hsl']`. Use `congr 1`. Conclude with `Subtype.ext ((hσ g a).trans ha.symm)`.

Take `⟨Φ, hΦ⟩` from `GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)`. Establish `hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r)`. Introduce `h r`. Use `hΦ h r` as an intermediate fact. Simplify using `using this`.

Establish `key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a))`. Introduce `a`. Rewrite using `[hga', he', he']`. Use extensionality with `r`. Rewrite using `[hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']`.

Both sides reduce to the same expression. Take `⟨a, b, hb, hf⟩` from `hsurj f`. Establish `hib : io b ≠ 0` using `fun h => hb (hinj (by rw [h, map_zero]))`. Establish `hf' : f = io a * (io b)⁻¹` using `by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]`. Establish `hfe : e' (ga' s f) = Φ (e' f)`.

Rewrite using `[hf']`. Simplify using `only [map_mul, map_inv₀, key]`. Rewrite using `[hfe, hΦ']`. Rewrite using `[hA', hA]`. Both sides reduce to the same expression.
-/
theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    convert hC x using 1
    · rfl
    · simp [HahnSeries.algebraMap_apply']

  have hsl := fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
