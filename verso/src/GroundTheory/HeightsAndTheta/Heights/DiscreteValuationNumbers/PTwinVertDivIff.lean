import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section General

variable {A : Type*} [CommRing A]

/- English proof (translation)
Set `q : (A ⧸ I) →ₗ[A] A ⧸ J` to `Submodule.mapQ _ _ LinearMap.id (fun a ha => hIJ ha)`. Establish `hq : Function.Surjective q`. Introduce `y`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩`.

Set `f₁` to `LocalizedModule.mkLinearMap W.primeCompl (A ⧸ I)`. Set `f₂` to `LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)`. Set `φ` to `IsLocalizedModule.map W.primeCompl f₁ f₂ q`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_localizedMap_eq_localized₀_ker, eq_bot_iff]`.

Introduce `z hz`. Rewrite `hz` using `[Submodule.mem_localized₀]`. Take `⟨m, hm, t, ht, rfl⟩` from `hz`. Rewrite using `[Submodule.mem_bot, IsLocalizedModule.mk'_eq_zero']`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Rewrite `hm` using `[LinearMap.mem_ker]`. Establish `hxJ : x ∈ J` using `(Submodule.Quotient.mk_eq_zero _).mp hm`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (s • x) = 0`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (hsJ x hxJ)`.

Set `e : LocalizedModule W.primeCompl (A ⧸ I) ≃ₗ[A] LocalizedModule W.primeCompl (A ⧸ J)` to `LinearEquiv.ofBijective φ ⟨hinj, IsLocalizedModule.map_surjective _ _ _ q hq⟩`. Conclude with `(e.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq`.
-/
theorem length_localizedQuot_eq_of_mul_le {I J W : Ideal A} [W.IsPrime] (hIJ : I ≤ J) {s : A}
    (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ I)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) := by
  let q : (A ⧸ I) →ₗ[A] A ⧸ J := Submodule.mapQ _ _ LinearMap.id (fun a ha => hIJ ha)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  let f₁ := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ I)
  let f₂ := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let φ := IsLocalizedModule.map W.primeCompl f₁ f₂ q
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_localizedMap_eq_localized₀_ker, eq_bot_iff]
    intro z hz
    rw [Submodule.mem_localized₀] at hz
    obtain ⟨m, hm, t, ht, rfl⟩ := hz
    rw [Submodule.mem_bot, IsLocalizedModule.mk'_eq_zero']
    refine ⟨⟨s, hs⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    have hxJ : x ∈ J := (Submodule.Quotient.mk_eq_zero _).mp hm
    change Submodule.Quotient.mk (s • x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hsJ x hxJ)
  let e : LocalizedModule W.primeCompl (A ⧸ I) ≃ₗ[A] LocalizedModule W.primeCompl (A ⧸ J) :=
    LinearEquiv.ofBijective φ ⟨hinj, IsLocalizedModule.map_surjective _ _ _ q hq⟩
  exact (e.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq

/- English proof (translation)
Take `⟨p, hp, r, hr, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h)) (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)`.
-/
theorem mul_mem_sup_span_of_sub_mem {P : Ideal A} {f g u v : A} (h : u * f - v * g ∈ P) {x : A}
    (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
  rw [e]
  exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
    (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)

end General

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

/- English proof (translation)
Use `letI := weightedGradedAlgebra R (blockWeight ι)`. Establish `hmem : f ∈ weightedHomogeneousSubmodule R (blockWeight ι) α` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf`. Establish `h` using `DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule R (blockWeight ι)) (a := u) (i := γ) hmem`. Establish `key : ∀ (x : MRing ι R) (m : K → ℕ), (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) x m : MRing ι R) = weightedHomogeneousComponent (blockWeight ι) m x` using `fun x m => weightedDecomposition.decompose'_apply R (blockWeight ι) x m`. Rewrite `h` using `[key, key]`.

Conclude with `h`.
-/
theorem component_mul_form_add {u f : MRing ι R} {α : K → ℕ} (hf : IsMultiHomog f α) (γ : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (γ + α) (u * f) =
      weightedHomogeneousComponent (blockWeight ι) γ u * f := by
  letI := weightedGradedAlgebra R (blockWeight ι)
  have hmem : f ∈ weightedHomogeneousSubmodule R (blockWeight ι) α :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule R (blockWeight ι)) (a := u) (i := γ) hmem
  have key : ∀ (x : MRing ι R) (m : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) x m : MRing ι R) =
        weightedHomogeneousComponent (blockWeight ι) m x :=
    fun x m => weightedDecomposition.decompose'_apply R (blockWeight ι) x m
  rw [key, key] at h
  exact h

/- English proof (translation)
Take `⟨γ, rfl⟩` from `exists_add_of_le hn`. Rewrite using `[add_comm β γ, add_tsub_cancel_right]`. Conclude with `component_mul_form_add hg γ`.
-/
theorem component_mul_form_of_le {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β) {n : K → ℕ}
    (hn : β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) =
      weightedHomogeneousComponent (blockWeight ι) (n - β) v * g := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le hn
  rw [add_comm β γ, add_tsub_cancel_right]
  exact component_mul_form_add hg γ

/- English proof (translation)
Use `letI := weightedGradedAlgebra R (blockWeight ι)`. Establish `hmem : g ∈ weightedHomogeneousSubmodule R (blockWeight ι) β` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg`. Establish `h` using `DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule R (blockWeight ι)) (a := v) hmem hn`. Rewrite using `[← h]`. Conclude with `(weightedDecomposition.decompose'_apply R (blockWeight ι) (v * g) n).symm`.
-/
theorem component_mul_form_of_not_le {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β)
    {n : K → ℕ} (hn : ¬ β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) = 0 := by
  letI := weightedGradedAlgebra R (blockWeight ι)
  have hmem : g ∈ weightedHomogeneousSubmodule R (blockWeight ι) β :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg
  have h := DirectSum.coe_decompose_mul_of_right_mem_of_not_le
    (weightedHomogeneousSubmodule R (blockWeight ι)) (a := v) hmem hn
  rw [← h]
  exact (weightedDecomposition.decompose'_apply R (blockWeight ι) (v * g) n).symm

/- English proof (translation)
Set `e : K ≃ Fin (Fintype.card K)` to `Fintype.equivFin K`. Use `letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq`. Use `letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))`. Use `⟨(W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal, hW.homogeneousCore, isMultiHomogIdeal_of_isHomogeneous_lex e (Ideal.homogeneousCore _ W).isHomogeneous, Ideal.toIdeal_homogeneousCore_le _ W, ?_, ?_⟩` and prove the remaining obligations. Introduce `J hJ hJW`.

Establish `hJh` using `isHomogeneous_lex_of_isMultiHomogIdeal e hJ`. Rewrite using `[← hJh.toIdeal_homogeneousCore_eq_self]`. Conclude with `Ideal.homogeneousCore_mono _ hJW`. Introduce `x γ hx hxW`. Use `Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨lexRelabel e γ, ?_⟩ hxW` and prove the remaining obligations.

Rewrite using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Rewrite using `[weight_comp_addMonoidHom, hx hd]`.
-/
theorem exists_multiHomog_core {W : Ideal (MRing ι R)} (hW : W.IsPrime) :
    ∃ W' : Ideal (MRing ι R), W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ W' ≤ W ∧
      (∀ J : Ideal (MRing ι R), IsMultiHomogIdeal J → J ≤ W → J ≤ W') ∧
      (∀ (x : MRing ι R) (γ : K → ℕ), IsMultiHomog x γ → x ∈ W → x ∈ W') := by
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  refine ⟨(W.homogeneousCore
      (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal,
    hW.homogeneousCore, isMultiHomogIdeal_of_isHomogeneous_lex e (Ideal.homogeneousCore _ W).isHomogeneous,
    Ideal.toIdeal_homogeneousCore_le _ W, ?_, ?_⟩
  · intro J hJ hJW
    have hJh := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJW
  · intro x γ hx hxW
    refine Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨lexRelabel e γ, ?_⟩ hxW
    rw [mem_weightedHomogeneousSubmodule]
    intro d hd
    rw [weight_comp_addMonoidHom, hx hd]

end Forms

section Divisor

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Establish `h' : v * g - u * f ∈ P`. Use `P.neg_mem h` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Establish `claim : ∀ W' : Ideal (MRing ι R), W'.IsPrime → W' ≤ W → (P ⊔ Ideal.span {f} ≤ W' ↔ P ⊔ Ideal.span {g} ≤ W')`. Introduce `W' hW' hle`.

Simplify using `only [sup_le_iff, Ideal.span_singleton_le_iff_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hf⟩`. Use `⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hv (hle h'')⟩` and prove the remaining obligations. Establish `e : v * g = u * f - (u * f - v * g)` using `by ring`.

Rewrite using `[e]`. Conclude with `W'.sub_mem (W'.mul_mem_left u hf) (hP h)`. Introduce and unpack `⟨hP, hg⟩`. Use `⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hu (hle h'')⟩` and prove the remaining obligations. Establish `e : u * f = (u * f - v * g) + v * g` using `by ring`.

Rewrite using `[e]`. Conclude with `W'.add_mem (hP h) (W'.mul_mem_left v hg)`. Establish `hmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hp, h1⟩, hm⟩`.

Conclude with `⟨⟨hp, (claim W hW le_rfl).1 h1⟩, fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).2 hy.2⟩ hyx⟩`. Introduce and unpack `⟨⟨hp, h1⟩, hm⟩`. Conclude with `⟨⟨hp, (claim W hW le_rfl).2 h1⟩, fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).1 hy.2⟩ hyx⟩`. Use `haveI := hW`. Establish `hmult : multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W`.

Unfold `multAt`. Rewrite using `[← length_localizedQuot_eq_of_mul_le (I := (P ⊔ Ideal.span {f}) ⊓ (P ⊔ Ideal.span {g})) inf_le_left hu (fun x hx => Ideal.mem_inf.mpr ⟨Ideal.mul_mem_left _ _ hx, mul_mem_sup_span_of_sub_mem h hx⟩), length_localizedQuot_eq_of_mul_le inf_le_right hv (fun x hx => Ideal.mem_inf.mpr ⟨ …`. Unfold `divCycle`. Distinguish the cases in `hc : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W`. Establish `hc' : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W` using `⟨hmin.1 hc.1, hc.2⟩`.

Rewrite using `[dif_pos hc, dif_pos hc']`. Conclude with `congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) hmult`. Establish `hc' : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W)` using `fun h'' => hc ⟨hmin.2 h''.1, h''.2⟩`. Rewrite using `[dif_neg hc, dif_neg hc']`.
-/
theorem divCycle_eq_of_unit_mul_sub_mem {P W : Ideal (MRing ι R)} (hW : W.IsPrime) {f g u v : MRing ι R}
    (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) : divCycle P f W = divCycle P g W := by
  have h' : v * g - u * f ∈ P := by
    have := P.neg_mem h
    rwa [neg_sub] at this
  have claim : ∀ W' : Ideal (MRing ι R), W'.IsPrime → W' ≤ W →
      (P ⊔ Ideal.span {f} ≤ W' ↔ P ⊔ Ideal.span {g} ≤ W') := by
    intro W' hW' hle
    simp only [sup_le_iff, Ideal.span_singleton_le_iff_mem]
    constructor
    · rintro ⟨hP, hf⟩
      refine ⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hv (hle h'')⟩
      have e : v * g = u * f - (u * f - v * g) := by ring
      rw [e]
      exact W'.sub_mem (W'.mul_mem_left u hf) (hP h)
    · rintro ⟨hP, hg⟩
      refine ⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hu (hle h'')⟩
      have e : u * f = (u * f - v * g) + v * g := by ring
      rw [e]
      exact W'.add_mem (hP h) (W'.mul_mem_left v hg)
  have hmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes := by
    constructor
    · rintro ⟨⟨hp, h1⟩, hm⟩
      exact ⟨⟨hp, (claim W hW le_rfl).1 h1⟩,
        fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).2 hy.2⟩ hyx⟩
    · rintro ⟨⟨hp, h1⟩, hm⟩
      exact ⟨⟨hp, (claim W hW le_rfl).2 h1⟩,
        fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).1 hy.2⟩ hyx⟩
  haveI := hW
  have hmult : multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    unfold multAt
    rw [← length_localizedQuot_eq_of_mul_le
        (I := (P ⊔ Ideal.span {f}) ⊓ (P ⊔ Ideal.span {g})) inf_le_left hu
        (fun x hx => Ideal.mem_inf.mpr ⟨Ideal.mul_mem_left _ _ hx, mul_mem_sup_span_of_sub_mem h hx⟩),
      length_localizedQuot_eq_of_mul_le inf_le_right hv
        (fun x hx => Ideal.mem_inf.mpr ⟨mul_mem_sup_span_of_sub_mem h' hx, Ideal.mul_mem_left _ _ hx⟩)]
  unfold divCycle
  by_cases hc : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hc' : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W := ⟨hmin.1 hc.1, hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) hmult
  · have hc' : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) :=
      fun h'' => hc ⟨hmin.2 h''.1, h''.2⟩
    rw [dif_neg hc, dif_neg hc']

end Divisor

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ P ϖ b f g hϖ hP`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, hQ⟩`. Rewrite `hα`, `hβ` using `[← FlagTypings.isMultiHomog_iff]`.

Use `⟨⟨α, β, hα, hβ, funext hb⟩, hfP, hgP, ?_, ?_⟩` and prove the remaining obligations. Introduce `W hW`. Assume the negation of the conclusion as `hϖW`. Establish `key : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W → divCycle P f W = divCycle P g W`. Introduce `x c hc hWm hWr`.

Establish `hWp : W.IsPrime` using `hWm.1.1`. Establish `hWh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.proof O K ι _ W (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hc) hWm`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWm.1.2`. Take `⟨u, v, -, -, hu, hv, huv⟩` from `hQ W ((BundleExamples.isMultiProjPrime_iff O W).mpr ⟨hWp, hWh, hWr⟩) hPW (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW)`. Conclude with `divCycle_eq_of_unit_mul_sub_mem hWp hu hv huv`.

Apply `hW` to reduce the goal to its premises. Unfold `ratDiv`. Rewrite using `[sub_eq_zero]`. Distinguish the cases in `h1 : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W`. Conclude with `key f α hα h1.1 h1.2`.

Distinguish the cases in `h2 : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W`. Conclude with `key g β hβ h2.1 h2.2`. Unfold `divCycle`. Rewrite using `[dif_neg h1, dif_neg h2]`. Introduce `W hWp hPW hWr hϖW`.

Take `⟨W', hW'p, hW'h, hW'W, hW'max, hW'form⟩` from `exists_multiHomog_core hWp`. Establish `hPW'` using `hW'max P hP.multiHomog hPW`. Establish `hW'r : IsRelevant W'` using `fun k =>`. Set `⟨i, hi⟩` to `hWr k`. Use the proof step `⟨i, fun h => hi (hW'W h)⟩`.

Establish `hcomap : W'.comap (C : O →+* MRing ι O) = ⊥` using `eq_bot_iff.mpr ((Ideal.comap_mono hW'W).trans (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW).le)`. Take `⟨u, v, ⟨γ, hγ⟩, ⟨δ, hδ⟩, hu, hv, huv⟩` from `hQ W' ((BundleExamples.isMultiProjPrime_iff O W').mpr ⟨hW'p, hW'h, hW'r⟩) hPW' hcomap`. Rewrite `hγ`, `hδ` using `[← FlagTypings.isMultiHomog_iff]`. Conclude with `⟨u, v, fun h => hu (hW'form u γ hγ h), fun h => hv (hW'form v δ hδ h), huv⟩`. Introduce and unpack `⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, -, hunit⟩`.

Use `⟨⟨α, β, (FlagTypings.isMultiHomog_iff f α).mp hα, (FlagTypings.isMultiHomog_iff g β).mp hβ, fun k => congrFun hb k⟩, hfP, hgP, ?_⟩` and prove the remaining obligations. Introduce `Q hQ hPQ hQO`. Establish `hQ' : IsMultiProjPrime Q` using `(BundleExamples.isMultiProjPrime_iff O Q).mp hQ`. Establish `hϖQ : (C ϖ : MRing ι O) ∉ Q`. Introduce `h`.

Establish `h' : ϖ ∈ Q.comap (C : O →+* MRing ι O)` using `h`. Rewrite `h'` using `[hQO, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero h'`. Take `⟨u, v, hu, hv, huv⟩` from `hunit Q hQ'.isPrime hPQ hQ'.relevant hϖQ`. Take `⟨γ, hγ⟩` from `exists_component_not_mem hu`.

Establish `hcomp` using `hP.multiHomog _ huv (γ + α)`. Rewrite `hcomp` using `[map_sub, component_mul_form_add hα]`. Distinguish the cases in `hβle : β ≤ γ + α`. Rewrite using `[component_mul_form_of_le hβ hβle] at hcomp set uγ := weightedHomogeneousComponent (blockWeight ι) γ u with huγ set vδ := weightedHomogeneousComponent (blockWeight ι) (γ + α - β) v with hvδ`. Establish `hvδQ : vδ ∉ Q`.

Introduce `hvQ`. Establish `h1 : f * (uγ * v - vδ * u) ∈ P`. Establish `e : f * (uγ * v - vδ * u) = v * (uγ * f - vδ * g) - vδ * (u * f - v * g)` using `by ring`. Rewrite using `[e]`. Conclude with `P.sub_mem (P.mul_mem_left _ hcomp) (P.mul_mem_left _ huv)`.

Establish `h2 : uγ * v - vδ * u ∈ Q` using `hPQ ((hP.isPrime.mem_or_mem h1).resolve_left hfP)`. Establish `h3 : uγ * v ∈ Q`. Establish `e : uγ * v = (uγ * v - vδ * u) + vδ * u` using `by ring`. Rewrite using `[e]`. Conclude with `Q.add_mem h2 (Q.mul_mem_right _ hvQ)`.

Break down `hQ'.isPrime.mem_or_mem h3 with h | h` into its components or cases. Use `exacts [hγ h, hv h]`. Conclude with `⟨uγ, vδ, ⟨γ, (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩, ⟨γ + α - β, (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩, hγ, hvδQ, hcomp⟩`. Rewrite `hcomp` using `[component_mul_form_of_not_le hβ hβle, sub_zero]`. Break down `hP.isPrime.mem_or_mem hcomp with h | h` into its components or cases.

Use `exacts [absurd (hPQ h) hγ, absurd h hfP]`.
-/
theorem VerticalDivisorCharacterisation.proof : VerticalDivisorCharacterisation.Statement := by
  intro O _ _ _ K _ _ ι _ P ϖ b f g hϖ hP
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv
  constructor
  · rintro ⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, hQ⟩
    rw [← FlagTypings.isMultiHomog_iff] at hα hβ
    refine ⟨⟨α, β, hα, hβ, funext hb⟩, hfP, hgP, ?_, ?_⟩
    · intro W hW
      by_contra hϖW
      have key : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
          W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
          divCycle P f W = divCycle P g W := by
        intro x c hc hWm hWr
        have hWp : W.IsPrime := hWm.1.1
        have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
          (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hc) hWm
        have hPW : P ≤ W := le_sup_left.trans hWm.1.2
        obtain ⟨u, v, -, -, hu, hv, huv⟩ := hQ W
          ((BundleExamples.isMultiProjPrime_iff O W).mpr ⟨hWp, hWh, hWr⟩) hPW
          (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW)
        exact divCycle_eq_of_unit_mul_sub_mem hWp hu hv huv
      apply hW
      unfold ratDiv
      rw [sub_eq_zero]
      by_cases h1 : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
      · exact key f α hα h1.1 h1.2
      by_cases h2 : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W
      · exact key g β hβ h2.1 h2.2
      unfold divCycle
      rw [dif_neg h1, dif_neg h2]
    · intro W hWp hPW hWr hϖW
      obtain ⟨W', hW'p, hW'h, hW'W, hW'max, hW'form⟩ := exists_multiHomog_core hWp
      have hPW' := hW'max P hP.multiHomog hPW
      have hW'r : IsRelevant W' := fun k =>
        let ⟨i, hi⟩ := hWr k
        ⟨i, fun h => hi (hW'W h)⟩
      have hcomap : W'.comap (C : O →+* MRing ι O) = ⊥ :=
        eq_bot_iff.mpr ((Ideal.comap_mono hW'W).trans (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW).le)
      obtain ⟨u, v, ⟨γ, hγ⟩, ⟨δ, hδ⟩, hu, hv, huv⟩ := hQ W'
        ((BundleExamples.isMultiProjPrime_iff O W').mpr ⟨hW'p, hW'h, hW'r⟩) hPW' hcomap
      rw [← FlagTypings.isMultiHomog_iff] at hγ hδ
      exact ⟨u, v, fun h => hu (hW'form u γ hγ h), fun h => hv (hW'form v δ hδ h), huv⟩
  · rintro ⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, -, hunit⟩
    refine ⟨⟨α, β, (FlagTypings.isMultiHomog_iff f α).mp hα, (FlagTypings.isMultiHomog_iff g β).mp hβ,
      fun k => congrFun hb k⟩, hfP, hgP, ?_⟩
    intro Q hQ hPQ hQO
    have hQ' : IsMultiProjPrime Q := (BundleExamples.isMultiProjPrime_iff O Q).mp hQ
    have hϖQ : (C ϖ : MRing ι O) ∉ Q := by
      intro h
      have h' : ϖ ∈ Q.comap (C : O →+* MRing ι O) := h
      rw [hQO, Ideal.mem_bot] at h'
      exact hϖ.ne_zero h'
    obtain ⟨u, v, hu, hv, huv⟩ := hunit Q hQ'.isPrime hPQ hQ'.relevant hϖQ
    obtain ⟨γ, hγ⟩ := exists_component_not_mem hu
    have hcomp := hP.multiHomog _ huv (γ + α)
    rw [map_sub, component_mul_form_add hα] at hcomp
    by_cases hβle : β ≤ γ + α
    · rw [component_mul_form_of_le hβ hβle] at hcomp
      set uγ := weightedHomogeneousComponent (blockWeight ι) γ u with huγ
      set vδ := weightedHomogeneousComponent (blockWeight ι) (γ + α - β) v with hvδ
      have hvδQ : vδ ∉ Q := by
        intro hvQ
        have h1 : f * (uγ * v - vδ * u) ∈ P := by
          have e : f * (uγ * v - vδ * u) = v * (uγ * f - vδ * g) - vδ * (u * f - v * g) := by ring
          rw [e]
          exact P.sub_mem (P.mul_mem_left _ hcomp) (P.mul_mem_left _ huv)
        have h2 : uγ * v - vδ * u ∈ Q := hPQ ((hP.isPrime.mem_or_mem h1).resolve_left hfP)
        have h3 : uγ * v ∈ Q := by
          have e : uγ * v = (uγ * v - vδ * u) + vδ * u := by ring
          rw [e]
          exact Q.add_mem h2 (Q.mul_mem_right _ hvQ)
        rcases hQ'.isPrime.mem_or_mem h3 with h | h
        exacts [hγ h, hv h]
      exact ⟨uγ, vδ,
        ⟨γ, (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩,
        ⟨γ + α - β,
          (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩,
        hγ, hvδQ, hcomp⟩
    · rw [component_mul_form_of_not_le hβ hβle, sub_zero] at hcomp
      rcases hP.isPrime.mem_or_mem hcomp with h | h
      exacts [absurd (hPQ h) hγ, absurd h hfP]

end GroundTheory.Heights₂.Heights.NumbersDVR
