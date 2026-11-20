import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing

/- English proof (translation)
Establish `hd : IsDomain O₂` using `IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `: IsNoetherianRing O₂` using `IsLocalization.isNoetherianRing P.primeCompl _ inferInstance`. Establish `hinj` using `IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors`. Take `⟨g, hg⟩` from `IsPrincipalIdealRing.principal (maximalIdeal O₁)`.

Establish `hg' : maximalIdeal O₁ = Ideal.span {g}` using `hg`. Establish `hmax : maximalIdeal O₂ = Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]`. Use `conv_lhs => rw [hP]`. Rewrite using `[hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]`.

Establish `hnf : ¬ IsField O₂`. Rewrite using `[isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]`. Introduce `h`. Establish `h1` using `hinj (h.trans (map_zero _).symm)`. Establish `h2 : g = 0` using `by simpa using h1`.

Apply `IsDiscreteValuationRing.not_a_field O₁` to reduce the goal to its premises. Rewrite using `[hg', h2]`. Simplify using the standard rewrite rules. Use `((IsDiscreteValuationRing.TFAE O₂ hnf).out 0 4).mpr ?_` and prove the remaining obligations. Rewrite using `[hmax]`.

Conclude with `⟨⟨_, rfl⟩⟩`.
-/
theorem gaussRing_isDVR {σ : Type} [Finite σ] (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime]
    (hP : P = Ideal.map MvPolynomial.C (maximalIdeal O₁))
    (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial σ O₁) O₂]
    [IsLocalization.AtPrime O₂ P] : ∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂ := by
  have hd : IsDomain O₂ :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors
  refine ⟨hd, ?_⟩
  have : IsNoetherianRing O₂ :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (maximalIdeal O₁)
  have hg' : maximalIdeal O₁ = Ideal.span {g} := hg
  have hmax : maximalIdeal O₂ =
      Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
    conv_lhs => rw [hP]
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField O₂ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    intro h
    have h1 := hinj (h.trans (map_zero _).symm)
    have h2 : g = 0 := by simpa using h1
    apply IsDiscreteValuationRing.not_a_field O₁
    rw [hg', h2]; simp
  refine ((IsDiscreteValuationRing.TFAE O₂ hnf).out 0 4).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C x`. Take `⟨a, ha⟩` from `h x`. Use `⟨MvPolynomial.C a, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.map_C, ← map_sub]`.

Conclude with `Ideal.mem_map_of_mem _ ha`. Consider the case `add p q hp hq`. Take `⟨a, ha⟩` from `hp`. Take `⟨b, hb⟩` from `hq`. Use `⟨a + b, ?_⟩` and prove the remaining obligations.

Use `Ideal.add_mem _ ha hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p n hp`.

Take `⟨a, ha⟩` from `hp`. Use `⟨a * MvPolynomial.X n, ?_⟩` and prove the remaining obligations. Use `Ideal.mul_mem_right (MvPolynomial.X n) _ ha` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, MvPolynomial.map_X]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mvPolynomial_sub_map_mem {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal S) (h : ∀ x : S, ∃ a : R, x - φ a ∈ I) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R,
      p - MvPolynomial.map φ q ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) I := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha⟩ := h x
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := Ideal.add_mem _ ha hb
    convert this using 1
    rw [map_add]; ring
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨a * MvPolynomial.X n, ?_⟩
    have := Ideal.mul_mem_right (MvPolynomial.X n) _ ha
    convert this using 1
    rw [map_mul, MvPolynomial.map_X]; ring

/- English proof (translation)
Introduce `K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _`. Take `⟨hd, hdvr⟩` from `gaussRing_isDVR O₁ P hP O₂`. Use `⟨⟨hd, hdvr⟩, ?_⟩` and prove the remaining obligations. Establish `hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal`. Use `symm`.

Apply `la.isMaximal.eq_of_le` to reduce the goal to its premises. Conclude with `Ideal.IsPrime.ne_top inferInstance`. Rewrite using `[← hmap]`. Conclude with `Ideal.le_comap_map`. Establish `hmem : ∀ p : OT K D N, MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la`.

Introduce `p`. Rewrite using `[hP, MvPolynomial.mem_map_C_iff]`. Use `Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm` and prove the remaining obligations. Use `forall_congr' fun m => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]`.

Set `g : OT K D N →+* O₂` to `(algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))`. Establish `hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y)` using `fun y => IsLocalization.map_units (M := P.primeCompl) O₂ ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩`. Set `f : Op D N la →+* O₂` to `IsLocalization.lift (M := (laT D N la).primeCompl) hu`. Establish `hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g` using `IsLocalization.lift_comp hu`. Establish `hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)` using `fun p => IsLocalization.lift_eq hu p`.

Establish `hinj₂` using `IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors`. Establish `hginj : Function.Injective g` using `hinj₂.comp (MvPolynomial.map_injective _ hinj)`. Establish `hfinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨⟨p, s⟩, h⟩` from `IsLocalization.surj (laT D N la).primeCompl x`. Establish `h1` using `congrArg f h`. Rewrite `h1` using `[map_mul, hx, zero_mul, hf']`. Establish `h2 : p = 0` using `hginj (h1.symm.trans (map_zero g).symm)`. Simplify using `only [h2, map_zero] at h`.

Conclude with `(IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h`. Establish `hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf, ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]`. Use `congr 1`. Rewrite using `[hP, ← hmap, Ideal.map_map]`.

Express the relevant statement in the definitionally equal form `Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _`. Rewrite using `[Ideal.map_map]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Use `⟨f, hf', ?_, ?_, hmax, ?_⟩` and prove the remaining obligations. Use `haveI := Op_isDVR D N la algebraize [f]`. Establish `: Module.IsTorsionFree (Op D N la) O₂`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`. Conclude with `hfinj`.

Unfold `RingHom.Flat`. Use `infer_instance`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `h1 : f a ∈ maximalIdeal O₂` using `hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)`.

Conclude with `(mem_maximalIdeal _).1 h1 ha`. Introduce `x`. Take `⟨⟨p, s⟩, h⟩` from `IsLocalization.surj P.primeCompl x`. Take `⟨p₀, hp⟩` from `exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p`. Take `⟨s₀, hs⟩` from `exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres (s : MvPolynomial (TVar D N) O₁)`.

Rewrite `hp`, `hs` using `[← hP]`. Establish `hs₀ : s₀ ∈ (laT D N la).primeCompl`. Introduce `h0`. Apply `s.2` to reduce the goal to its premises. Use `P.add_mem hs ((hmem _).2 h0)` as an intermediate fact.

Simplify using `using this`. Take `⟨u, hu'⟩` from `IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩`. Use `⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂`. Introduce `q hq`.

Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]`. Conclude with `Ideal.mem_map_of_mem _ hq`. Establish `h1` using `hm _ hp`. Establish `h2` using `hm _ hs`. Rewrite `h1`, `h2` using `[map_sub, ← hf']`.

Simplify using `only at h hu'`. Rewrite `h2` using `[← hu']`. Establish `h3 : f u * f ↑u⁻¹ = 1` using `by rw [← map_mul]; simp`. Establish `h4` using `Ideal.mul_mem_right (f ↑u⁻¹) _ (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_mul, ← h]`. Take the linear combination `(-x) * h3`.
-/
theorem gaussRing_completion :
    ∀ (K : Type) [Field K] [NumberField K] (D N : ℕ) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra (𝓞 K) O₁], Function.Injective (algebraMap (𝓞 K) O₁) → Ideal.map (algebraMap (𝓞 K) O₁) la.asIdeal = IsLocalRing.maximalIdeal O₁ → (∀ x : O₁, ∃ a : 𝓞 K, x - algebraMap (𝓞 K) O₁ a ∈ IsLocalRing.maximalIdeal O₁) → ∀ (P : Ideal (MvPolynomial (TVar D N) O₁)) [P.IsPrime], P = Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O₁) → ∀ (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial (TVar D N) O₁) O₂] [IsLocalization.AtPrime O₂ P], (∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂) ∧ ∃ f : Op D N la →+* O₂, (∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)) ∧ f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (Op D N la)) = IsLocalRing.maximalIdeal O₂ ∧ ∀ x : O₂, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal O₂ := by
  intro K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _
  obtain ⟨hd, hdvr⟩ := gaussRing_isDVR O₁ P hP O₂
  refine ⟨⟨hd, hdvr⟩, ?_⟩
  have hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal := by
    symm
    apply la.isMaximal.eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← hmap]; exact Ideal.le_comap_map
  have hmem : ∀ p : OT K D N,
      MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la := by
    intro p
    rw [hP, MvPolynomial.mem_map_C_iff]
    refine Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm
    refine forall_congr' fun m => ?_
    rw [MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]
  let g : OT K D N →+* O₂ :=
    (algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))
  have hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := P.primeCompl) O₂
      ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩
  let f : Op D N la →+* O₂ := IsLocalization.lift (M := (laT D N la).primeCompl) hu
  have hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g := IsLocalization.lift_comp hu
  have hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) =
      algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p) :=
    fun p => IsLocalization.lift_eq hu p
  have hinj₂ := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective g := hinj₂.comp (MvPolynomial.map_injective _ hinj)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (laT D N la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf'] at h1
    have h2 : p = 0 := hginj (h1.symm.trans (map_zero g).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h
  have hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]
    congr 1
    rw [hP, ← hmap, Ideal.map_map]
    change Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  refine ⟨f, hf', ?_, ?_, hmax, ?_⟩
  · haveI := Op_isDVR D N la
    algebraize [f]
    have : Module.IsTorsionFree (Op D N la) O₂ := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact hfinj
    unfold RingHom.Flat
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : f a ∈ maximalIdeal O₂ := hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  · intro x
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    obtain ⟨p₀, hp⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p
    obtain ⟨s₀, hs⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres
      (s : MvPolynomial (TVar D N) O₁)
    rw [← hP] at hp hs
    have hs₀ : s₀ ∈ (laT D N la).primeCompl := by
      intro h0
      apply s.2
      have := P.add_mem hs ((hmem _).2 h0)
      simpa using this
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩
    refine ⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩
    have hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂ := by
      intro q hq
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
      exact Ideal.mem_map_of_mem _ hq
    have h1 := hm _ hp
    have h2 := hm _ hs
    rw [map_sub, ← hf'] at h1 h2
    simp only at h hu'
    rw [← hu'] at h2
    have h3 : f u * f ↑u⁻¹ = 1 := by rw [← map_mul]; simp
    have h4 := Ideal.mul_mem_right (f ↑u⁻¹) _
      (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))
    convert h4 using 1
    rw [map_mul, ← h]
    linear_combination (-x) * h3

end GlobalTheory
