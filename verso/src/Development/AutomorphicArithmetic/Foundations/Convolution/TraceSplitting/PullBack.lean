import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep

namespace UpperTheory.ConvolutionTheory.T

section Rep
variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def pull (e : G ≃ₜ* H) (τ : SmIrr H) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (e : G →* H)
  smooth := fun x => (τ.smooth x).preimage e.continuous
  irred := by
    refine (OrderIso.isSimpleOrder_iff (β := Subrepresentation τ.ρ)
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => ?_⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (e g) hv⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl
        map_rel_iff' := Iff.rfl }).2 τ.irred
    have := S.apply_mem_toSubmodule (e.symm g) hv
    simpa using this

end Rep

section Trace
variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨hf, rfl⟩` from `h`. Establish `hR : LinearMap.range (c • A) = LinearMap.range A` using `LinearMap.range_smul A c hc`. Establish `key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R) (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A), LinearMap.trace ℂ R ((c • A).restrict h1) = c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2)`. Introduce and unpack `_ rfl h1 h2`. Establish `: (c • A).restrict h1 = c • A.restrict h2`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, map_smul, smul_eq_mul]`. Conclude with `⟨hR ▸ hf, key _ hR _ _⟩`.
-/
private theorem hasFinTrace_smul {A : V →ₗ[ℂ] V} {c s : ℂ} (hc : c ≠ 0) (h : HasFinTrace A s) :
    HasFinTrace (c • A) (c * s) := by
  obtain ⟨hf, rfl⟩ := h
  have hR : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul A c hc
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((c • A).restrict h1) =
        c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    rintro _ rfl h1 h2
    have : (c • A).restrict h1 = c • A.restrict h2 := by
      ext x
      simp
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hR ▸ hf, key _ hR _ _⟩

/- English proof (translation)
Take `⟨A, hA, hf⟩` from `hs`. Establish `hme : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`. Use `⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩` and prove the remaining obligations. Take `⟨hi, hl⟩` from `hA x l`.

Establish `hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e)` using `hme.integrable_map_iff.2 hi`. Substitute `h` using the available equality. Use `⟨hi'.smul_measure_nnreal, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]`. Simplify using `[NNReal.smul_def]`.
-/
private theorem hasTrace_map (e : G ≃ₜ* H) (mF : Measure G) (mE : Measure H) (c : NNReal) (hc : c ≠ 0)
    (h : mE = c • mF.map e) (π : Representation ℂ H V) (ψ : H → ℂ) (s : ℂ)
    (hs : HasTrace mF (π.comp (e : G →* H)) (fun g => ψ (e g)) s) : HasTrace mE π ψ ((c : ℂ) * s) := by
  obtain ⟨A, hA, hf⟩ := hs
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩
  obtain ⟨hi, hl⟩ := hA x l
  have hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e) := hme.integrable_map_iff.2 hi
  subst h
  refine ⟨hi'.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]
  simp [NNReal.smul_def]

end Trace

end UpperTheory.ConvolutionTheory.T

/- English proof (translation)
Introduce `F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'`. Take `⟨⟨e, he⟩, -⟩` from `UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n`. Establish `hmap : (mF.map e).IsHaarMeasure` using `ContinuousMulEquiv.isHaarMeasure_map mF e`. Establish `hscal` using `Measure.isMulLeftInvariant_eq_smul mE (mF.map e)`. Establish `hpos` using `Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)`.

Establish `hc0 : mE.haarScalarFactor (mF.map e) ≠ 0` using `hpos.ne'`. Use `⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `τ₁ ⟨E₁⟩`. Use `⟨E₁.toLinearEquiv, fun g x => ?_⟩` and prove the remaining obligations. Rewrite using `[← he g]`.

Conclude with `LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x`. Introduce `ψ s h`. Use `hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_` and prove the remaining obligations. Establish `hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g)`. Use function extensionality and compare the values at `fun g => by rw [he g]`.

Rewrite using `[hfun]`. Conclude with `h`. Introduce `J U hJ hU`. Establish `hU' : ∀ g, g ∈ U ↔ e g ∈ J` using `fun g => by rw [he g]; exact hU g`. Establish `hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1))` using `Set.ext hU'`.

Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hset]`. Conclude with `e.toHomeomorph.isCompact_preimage.2 hJ.1`. Rewrite using `[hset]`. Conclude with `hJ.2.preimage e.continuous`.

Introduce `h h0`. Use `h (eq_bot_iff.2 fun x hx => ?_)` and prove the remaining obligations. Establish `hx' : x ∈ fixedVectors (pull e τ').ρ U` using `fun u hu => hx _ ((hU' u).1 hu)`. Rewrite `hx'` using `[h0]`. Conclude with `hx'`.

Introduce `φ hφ hinv`. Use `⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous, hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩` and prove the remaining obligations. Establish `hu' : e.symm u ∈ U` using `(hU' _).2 (by simpa using hu)`. Simplify `hinv _ hu' (e.symm g)` using `[map_mul]`. Use function extensionality and compare the values at `g`.

Rewrite using `[← he g]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.T.pullBack :
    UpperTheory.ConvolutionTheory.T.PullBack := by
  intro F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'
  obtain ⟨⟨e, he⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
  have hmap : (mF.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map mF e
  have hscal := Measure.isMulLeftInvariant_eq_smul mE (mF.map e)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)
  have hc0 : mE.haarScalarFactor (mF.map e) ≠ 0 := hpos.ne'
  refine ⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · rintro τ₁ ⟨E₁⟩
    refine ⟨E₁.toLinearEquiv, fun g x => ?_⟩
    rw [← he g]
    exact LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x
  · intro ψ s h
    refine hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_
    have hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g) :=
      funext fun g => by rw [he g]
    rw [hfun]
    exact h
  · intro J U hJ hU
    have hU' : ∀ g, g ∈ U ↔ e g ∈ J := fun g => by rw [he g]; exact hU g
    have hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1)) := Set.ext hU'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hset]
      exact e.toHomeomorph.isCompact_preimage.2 hJ.1
    · rw [hset]
      exact hJ.2.preimage e.continuous
    · intro h h0
      refine h (eq_bot_iff.2 fun x hx => ?_)
      have hx' : x ∈ fixedVectors (pull e τ').ρ U := fun u hu => hx _ ((hU' u).1 hu)
      rw [h0] at hx'
      exact hx'
    · intro φ hφ hinv
      refine ⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous,
        hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩
      · have hu' : e.symm u ∈ U := (hU' _).2 (by simpa using hu)
        simpa [map_mul] using hinv _ hu' (e.symm g)
      · funext g
        rw [← he g]
        simp
