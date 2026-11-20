import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.PairEx
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEigAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SatPair
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfPair
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Establish `h1` using `UpperTheory.V.Af.Gk.satAE ℚ 2 π`. Rewrite `h1`, the goal using `[Filter.eventually_cofinite]`. Use `(h1.biUnion (t := fun v => {w : P E | Below v w}) fun v _ => ?_).subset fun w hw => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Use `Set.Finite.of_finite_image (f := fun w => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) fun _ _ _ _ e => HeightOneSpectrum.ext e` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `⟨w.isPrime, ⟨hw⟩⟩`. Simplify using `only [Set.mem_setOf_eq, not_forall] at hw`. Take `⟨v, hv, hn⟩` from `hw`. Conclude with `Set.mem_biUnion (show v ∈ {v | ¬ ∃ B, π.HasSat v B} from hn) hv`.
-/
private theorem sat_below (π : TR.CuspSub ℚ 2) {E : Type} [Field E] [NumberField E] :
    ∀ᶠ w : P E in cofinite, ∀ v : P ℚ, Below v w → ∃ B, π.HasSat v B := by
  have h1 := UpperTheory.V.Af.Gk.satAE ℚ 2 π
  rw [Filter.eventually_cofinite] at h1 ⊢
  refine (h1.biUnion (t := fun v => {w : P E | Below v w}) fun v _ => ?_).subset fun w hw => ?_
  · have := v.isMaximal
    refine Set.Finite.of_finite_image (f := fun w => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_)
      fun _ _ _ _ e => HeightOneSpectrum.ext e
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨hw⟩⟩
  · simp only [Set.mem_setOf_eq, not_forall] at hw
    obtain ⟨v, hv, hn⟩ := hw
    exact Set.mem_biUnion (show v ∈ {v | ¬ ∃ B, π.HasSat v B} from hn) hv

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ h`. Take `⟨f, hf, φ, hφ, e⟩` from `h`. Establish `hO` using `UpperTheory.ConvolutionTheory.R2.Ff.level ℚ E D W M π f hf φ hφ Ψ e`. Establish `hc : Continuous (locGL E 2 w)` using `GlobalTheory.CuspRep.CuspSub.continuous_locGL w`.

Establish `hm : {k | GlobalTheory.CuspRep.finRep E 2 k Ψ = Ψ} ∈ 𝓝 (locGL E 2 w 1)` using `hO.mem_nhds (by simp)`. Use `filter_upwards [hc.continuousAt.eventually hm] with y hy g`. Conclude with `congrFun (congrArg Subtype.val hy) g`. Consider the case `zero => exact Filter.Eventually.of_forall fun _ _ => rfl`. Consider the case `add x y _ _ ix iy => filter_upwards [ix, iy] with z h1 h2 g`.

Conclude with `congrArg₂ (· + ·) (h1 g) (h2 g)`. Consider the case `smul c x _ ix => filter_upwards [ix] with z h1 g`. Conclude with `congrArg (c • ·) (h1 g)`.
-/
private theorem span_level {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (M : Meas ℚ)
    (π : TR.CuspSub ℚ 2) (w : P E) (Φ : Sm E 2) (hΦ : Φ ∈ span W M π) :
    ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, Φ.1 (g * lc w y) = Φ.1 g := by
  induction hΦ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    have hO := UpperTheory.ConvolutionTheory.R2.Ff.level ℚ E D W M π f hf φ hφ Ψ e
    have hc : Continuous (locGL E 2 w) := GlobalTheory.CuspRep.CuspSub.continuous_locGL w
    have hm : {k | GlobalTheory.CuspRep.finRep E 2 k Ψ = Ψ} ∈ 𝓝 (locGL E 2 w 1) := hO.mem_nhds (by simp)
    filter_upwards [hc.continuousAt.eventually hm] with y hy g
    exact congrFun (congrArg Subtype.val hy) g
  | zero => exact Filter.Eventually.of_forall fun _ _ => rfl
  | add x y _ _ ix iy =>
    filter_upwards [ix, iy] with z h1 h2 g
    exact congrArg₂ (· + ·) (h1 g) (h2 g)
  | smul c x _ ix =>
    filter_upwards [ix] with z h1 g
    exact congrArg (c • ·) (h1 g)

/- English proof (translation)
Introduce `E _ _ _ D W M N Q hn π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩`. Take `⟨B, hI, hB, hK⟩` from `pairEx E D W M N Q hn π hπ`. Take `⟨Φ, hΦ⟩` from `UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph`. Establish `hmem : Φ ∈ span W M π` using `Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩`. Establish `hB0 : B ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `h1` using `hB ⟨Φ, hmem⟩ ⟨φ, hφ⟩`. Rewrite `h1` using `[h0]`. Rewrite using `[← hΦ]`.

Conclude with `h1.symm`. Establish `hc : ∀ x : span W M π, Continuous x.1.1` using `fun x => (UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2).1`. Set `T : span W M π →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)` to `{ toFun := fun x => WE D x.1.1 map_add' := fun x y => by`. Use function extensionality and compare the values at `h`. Establish `e` using `(UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D x.1.1 (hc x)).2.2 y.1.1 1 (hc y) h`.

Simplify using `using e`. Use the proof step `map_smul' := fun c x => by`. Use function extensionality and compare the values at `h`. Establish `e` using `(UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D 0 continuous_const).2.2 x.1.1 c (hc x) h`. Simplify `e }` using `[WE]`.

Establish `hsat : ∀ (w : P E) (v : P ℚ), SplitAt v w → ∀ C C', π.HasSat v C → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹)`. Introduce `w v hsp C C' hC hC'`. Use `satPair E (span W M π) Q B hI hB0 w T (fun x => span_level W M π w x.1 x.2) (fun x x' y h g => ?_) (fun x hx => hK x fun h => congrFun hx h) C C' (fun x hx => splitEig E D W M N Q π x.1 x.2 v w hsp C hC hx) hC'` and prove the remaining obligations. Use `show WE D x'.1.1 g = WE D x.1.1 (g * lc w y)`. Simplify using `only [WE, h, mul_assoc]`.

Use `⟨π.dual, ?_, fun τ m hm => ?_⟩` and prove the remaining obligations. Use `filter_upwards [sat_below π, placeAe ℚ E D, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat Q] with w h1 h2 ⟨C', hC'⟩ hnorm`. Establish `hb : Below (w.under (𝓞 ℚ)) w` using `rfl`. Take `⟨C, hC⟩` from `h1 _ hb`. Establish `h4 : 1 < normV (w.under (𝓞 ℚ))`.

Use `GlobalTheory.LFun.one_lt_absNorm (w.under (𝓞 ℚ))` as an intermediate fact. Simplify `this` using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Break down `h2 _ hb with hsp | hi` into its components or cases. Conclude with `⟨C.map (·⁻¹), hC.dual, hsat w _ hsp C C' hC hC' ▸ hC'⟩`. It suffices to derive a contradiction.

Establish `h5` using `hi.norm`. Rewrite `h5` using `[hnorm]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨m₀, hm₀⟩` from `UpperTheory.V.TR.Cen.exists_hasInfChar π (InfinitePlace.mk (τ.comp (algebraMap ℚ E)))`. Establish `e` using `infPair E (span W M π) Q B hI hB0 τ m₀ m hm₀.1 (UpperTheory.ConvolutionTheory.R2.cap ℚ E D W M π τ m₀ hm₀) hm`.

Rewrite using `[e]`. Conclude with `hm₀.dual`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.finS :
    FinS := by
  intro E _ _ _ D W M N Q hn π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩
  obtain ⟨B, hI, hB, hK⟩ := pairEx E D W M N Q hn π hπ
  obtain ⟨Φ, hΦ⟩ := UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph
  have hmem : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩
  have hB0 : B ≠ 0 := by
    intro h0
    apply hne
    have h1 := hB ⟨Φ, hmem⟩ ⟨φ, hφ⟩
    rw [h0] at h1
    rw [← hΦ]
    exact h1.symm
  have hc : ∀ x : span W M π, Continuous x.1.1 := fun x => (UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2).1
  let T : span W M π →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun x => WE D x.1.1
      map_add' := fun x y => by
        funext h
        have e := (UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D x.1.1 (hc x)).2.2 y.1.1 1 (hc y) h
        simpa using e
      map_smul' := fun c x => by
        funext h
        have e := (UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D 0 continuous_const).2.2 x.1.1 c (hc x) h
        simpa [WE] using e }
  have hsat : ∀ (w : P E) (v : P ℚ), SplitAt v w → ∀ C C', π.HasSat v C → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹) := by
    intro w v hsp C C' hC hC'
    refine satPair E (span W M π) Q B hI hB0 w T (fun x => span_level W M π w x.1 x.2) (fun x x' y h g => ?_)
      (fun x hx => hK x fun h => congrFun hx h) C C' (fun x hx => splitEig E D W M N Q π x.1 x.2 v w hsp C hC hx) hC'
    show WE D x'.1.1 g = WE D x.1.1 (g * lc w y)
    simp only [WE, h, mul_assoc]
  refine ⟨π.dual, ?_, fun τ m hm => ?_⟩
  · filter_upwards [sat_below π, placeAe ℚ E D, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat Q] with w h1 h2 ⟨C', hC'⟩ hnorm
    have hb : Below (w.under (𝓞 ℚ)) w := rfl
    obtain ⟨C, hC⟩ := h1 _ hb
    have h4 : 1 < normV (w.under (𝓞 ℚ)) := by
      have := GlobalTheory.LFun.one_lt_absNorm (w.under (𝓞 ℚ))
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
    rcases h2 _ hb with hsp | hi
    · exact ⟨C.map (·⁻¹), hC.dual, hsat w _ hsp C C' hC hC' ▸ hC'⟩
    · exfalso
      have h5 := hi.norm
      rw [hnorm] at h5
      nlinarith
  · obtain ⟨m₀, hm₀⟩ := UpperTheory.V.TR.Cen.exists_hasInfChar π (InfinitePlace.mk (τ.comp (algebraMap ℚ E)))
    have e := infPair E (span W M π) Q B hI hB0 τ m₀ m hm₀.1 (UpperTheory.ConvolutionTheory.R2.cap ℚ E D W M π τ m₀ hm₀) hm
    rw [e]
    exact hm₀.dual
