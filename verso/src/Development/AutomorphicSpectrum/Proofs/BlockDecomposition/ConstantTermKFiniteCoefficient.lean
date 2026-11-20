import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.KType

/- English proof (translation)
Set `f : Finset K → Submodule ℂ S` to `fun T => ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)`. Take `⟨T, -, hT⟩` from `(measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩`. Use `⟨T, fun s hs h0 => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨t, ht⟩` from `Function.ne_iff.1 hne`.

Establish `hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0` using `fun T' u => by`. Simplify using `[f, Submodule.mem_iInf]`. Establish `hle : f (insert t T) ≤ f T` using `fun u hu => (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')`. Establish `hlt : f (insert t T) < f T`. Use `lt_of_le_of_ne hle fun heq => ?_` and prove the remaining obligations.

Establish `h1 : (⟨s, hs⟩ : S) ∈ f T` using `(hmem T _).2 h0`. Rewrite `h1` using `[← heq]`. Conclude with `ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))`. Conclude with `hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)`.
-/
theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_finset_sep S`. Set `R : S →ₗ[ℂ] (T → ℂ)` to `LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype`. Establish `hker : LinearMap.ker R = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_` and prove the remaining obligations. Use `hT u u.2 fun t ht => ?_` and prove the remaining obligations.

Use `congrFun hu ⟨t, ht⟩` as an intermediate fact. Simplify `this` using `[R]`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective R hker`. Set `b` to `Pi.basisFun ℂ T`. Establish `hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ)`.

Introduce `s hs`. Establish `h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩)` using `by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]`. Establish `h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t` using `by conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]`. Simplify using `[R, b]`. Rewrite `h1` using `[h2, map_sum]`.

Establish `h3` using `congrArg (fun u : S => (u : K → ℂ)) h1`. Simplify `h3` using `[Submodule.coe_sum, map_smul]`. Establish `: (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ)`. Use function extensionality and compare the values at `k`. Establish `hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k` using `fun k' => by conv_lhs => rw [hexp (F k') (hF k')]`.

Simplify using `[Finset.sum_apply]`. Repeatedly rewrite using `[hk]`. Rewrite using `[integral_finset_sum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ fun t _ => (hi t).mul_const _]`. Simplify using `[Finset.sum_apply, integral_mul_const]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2`.
-/
theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finset_sum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

/- English proof (translation)
Set `T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ)` to `LinearMap.pi fun k => LinearMap.applyₗ (ρ k)`. Establish `: GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f ⟨ℓ, w, rfl⟩`. Conclude with `⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩`.

Conclude with `Submodule.finiteDimensional_of_le this`.
-/
theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

/- English proof (translation)
Establish `hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x)` using `continuous_const.mul (JointCont.continuous_finPart g)`. Establish `h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ` using `by rw [inv_mul_cancel]; simp`. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx`. Establish `hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ` using `hx`. Rewrite using `[chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x), map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]`.

Conclude with `congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'`.
-/
theorem eventually_eq_chart (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a)
    (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, φ.1 (unip x * g) =
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx
  have hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ := hx
  rw [chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x),
    map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]
  exact congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Establish `hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a)` using `φ.2 _`. Establish `hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀` using `ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀))) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _))) (JointCont.continuous_infPart g).continuousAt`. Establish `hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀] fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)` using `eventually_eq_chart φ hlev g x₀`. Conclude with `hA.congr hE.symm`.
-/
theorem continuous_unip_mul (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E =>
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀)))
      (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  have hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀]
      fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) :=
    eventually_eq_chart φ hlev g x₀
  exact hA.congr hE.symm

/- English proof (translation)
Take `⟨K, hK, hcov⟩` from `Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)`. Establish `hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K)` using `isCompact_univ_pi fun _ => hK`. Take `⟨C, hC⟩` from `hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Use `choose q hq using fun p => hcov (x p)`.

Take `⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K, x = (fun p => algebraMap E (Ad E) (q p)) + x'` from `⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hleft]`. Conclude with `hC x' hx'm`.
-/
theorem exists_bound_unip_mul (φ : Sm E a) (hleft : ∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K,
      x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  rw [unip_add, unip_algebraMap, mul_assoc, hleft]
  exact hC x' hx'm

/- English proof (translation)
Introduce `E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g`. Use `haveI := hμ`. Use `haveI := finiteDimensional_coeffSpan ρ`. Establish `hfin` using `covol_lt_top μ 𝓕 hF`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩`.

Use `integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ) (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)` and prove the remaining obligations. Establish `e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))` using `fun k => by rw [← mul_assoc]; rfl`. Use `hρ (unip x * g)` as an intermediate fact. Simplify using `only [e] at this`. Conclude with `this`.

Take `⟨C, hC⟩` from `exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))`. Conclude with `Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C (Filter.Eventually.of_forall hC)`.
-/
theorem ct_mem_coeffSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g
  haveI := hμ
  haveI := finiteDimensional_coeffSpan ρ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)
  · have e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) :=
      fun k => by rw [← mul_assoc]; rfl
    have := hρ (unip x * g)
    simp only [e] at this
    exact this
  · obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))
    exact Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

end GlobalTheory.CompanionTheory.CTFin.KType

end
