import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_relabel_bundle

variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}

/- English proof (translation)
Take `⟨a, i⟩` from `p`. Simplify using `only at h`. Substitute `h` using the available equality. Conclude with `⟨i, rfl⟩`.
-/
theorem exists_snd {K : Type} {ι : K → Type} (p : Σ k, ι k) (k : K) (h : p.1 = k) :
    ∃ i : ι k, p = ⟨k, i⟩ := by
  obtain ⟨a, i⟩ := p
  simp only at h
  subst h
  exact ⟨i, rfl⟩

/- English proof (translation)
Establish `h : ∀ k, ∃ i : ι₁ k, σ.symm ⟨e k, s₂ (e k)⟩ = ⟨k, i⟩` using `fun k => by`. Apply `exists_snd` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hσ, Equiv.apply_symm_apply]`. Use `choose s₁ hs using h`.

Conclude with `⟨s₁, fun k => by rw [← hs k, Equiv.apply_symm_apply]⟩`.
-/
theorem exists_down (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₂ : ∀ k, ι₂ k) : ∃ s₁ : ∀ k, ι₁ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₁ k, σ.symm ⟨e k, s₂ (e k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    apply e.injective
    rw [← hσ, Equiv.apply_symm_apply]
  choose s₁ hs using h
  exact ⟨s₁, fun k => by rw [← hs k, Equiv.apply_symm_apply]⟩

/- English proof (translation)
Establish `h : ∀ k, ∃ i : ι₂ k, σ ⟨e.symm k, s₁ (e.symm k)⟩ = ⟨k, i⟩` using `fun k => by`. Apply `exists_snd` to reduce the goal to its premises. Rewrite using `[hσ, Equiv.apply_symm_apply]`. Use `choose s₂ hs using h`. Use `⟨s₂, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hs (e k)]`. Conclude with `congrArg (fun k => σ ⟨k, s₁ k⟩) (e.symm_apply_apply k).symm`.
-/
theorem exists_up (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₁ : ∀ k, ι₁ k) : ∃ s₂ : ∀ k, ι₂ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₂ k, σ ⟨e.symm k, s₁ (e.symm k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    rw [hσ, Equiv.apply_symm_apply]
  choose s₂ hs using h
  refine ⟨s₂, fun k => ?_⟩
  rw [← hs (e k)]
  exact congrArg (fun k => σ ⟨k, s₁ k⟩) (e.symm_apply_apply k).symm

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `h` using `σ.injective ((hs k).trans (ht k).symm)`. Conclude with `eq_of_heq (Sigma.mk.inj_iff.1 h).2`.
-/
theorem down_unique (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) {s₂ : ∀ k, ι₂ k}
    {s₁ t₁ : ∀ k, ι₁ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩)
    (ht : ∀ k, σ ⟨k, t₁ k⟩ = ⟨e k, s₂ (e k)⟩) : s₁ = t₁ := by
  funext k
  have h := σ.injective ((hs k).trans (ht k).symm)
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `key : (pointConeMap O y).comp (rename σ) = ((rename e : MvPolynomial K₁ Ω →ₐ[Ω] MvPolynomial K₂ Ω).restrictScalars O).comp (pointConeMap O (y ∘ σ))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[pointConeMap, hσ]`. Conclude with `congrArg (fun φ => φ f) key`.
-/
theorem cone_rename (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    (f : MvPolynomial (Σ k, ι₁ k) O) :
    pointConeMap O y (rename σ f) = rename e (pointConeMap O (y ∘ σ) f) := by
  have key : (pointConeMap O y).comp (rename σ) =
      ((rename e : MvPolynomial K₁ Ω →ₐ[Ω] MvPolynomial K₂ Ω).restrictScalars O).comp
        (pointConeMap O (y ∘ σ)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hσ]
  exact congrArg (fun φ => φ f) key

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `g hg`. Take `⟨f, rfl⟩` from `rename_surjective (R := O) σ σ.surjective g`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Establish `h0 : pointConeMap O y (rename σ f) = 0` using `hg`.

Rewrite `h0` using `[cone_rename O e σ hσ]`. Use `show pointConeMap O (y ∘ σ) f = 0`. Apply `rename_injective e e.injective` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `f hf`. Establish `h0 : pointConeMap O (y ∘ σ) f = 0` using `hf`. Use `show pointConeMap O y (rename σ f) = 0`. Rewrite using `[cone_rename O e σ hσ, h0, map_zero]`.
-/
theorem pointIdeal_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨f, rfl⟩ := rename_surjective (R := O) σ σ.surjective g
    apply Ideal.mem_map_of_mem
    have h0 : pointConeMap O y (rename σ f) = 0 := hg
    rw [cone_rename O e σ hσ] at h0
    show pointConeMap O (y ∘ σ) f = 0
    apply rename_injective e e.injective
    rw [h0, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    have h0 : pointConeMap O (y ∘ σ) f = 0 := hf
    show pointConeMap O y (rename σ f) = 0
    rw [cone_rename O e σ hσ, h0, map_zero]

/- English proof (translation)
Unfold `fnField`. Use `congr 2`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨k, i, j⟩, rfl⟩`.

Establish `h : ∀ i : ι₂ k, ∃ i' : ι₁ (e.symm k), σ.symm ⟨k, i⟩ = ⟨e.symm k, i'⟩` using `fun i => by`. Apply `exists_snd` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Take `⟨i', hi⟩` from `h i`.

Take `⟨j', hj⟩` from `h j`. Use `⟨⟨e.symm k, i', j'⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Introduce and unpack `⟨⟨k, i, j⟩, rfl⟩`.

Take `⟨i', hi⟩` from `exists_snd (σ ⟨k, i⟩) (e k) (hσ _)`. Take `⟨j', hj⟩` from `exists_snd (σ ⟨k, j⟩) (e k) (hσ _)`. Use `⟨⟨e k, i', j'⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[hi, hj]`.
-/
theorem fnField_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    fnField O y = fnField O (y ∘ σ) := by
  unfold fnField
  congr 2
  ext a
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    have h : ∀ i : ι₂ k, ∃ i' : ι₁ (e.symm k), σ.symm ⟨k, i⟩ = ⟨e.symm k, i'⟩ := fun i => by
      apply exists_snd
      apply e.injective
      rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨i', hi⟩ := h i
    obtain ⟨j', hj⟩ := h j
    refine ⟨⟨e.symm k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    obtain ⟨i', hi⟩ := exists_snd (σ ⟨k, i⟩) (e k) (hσ _)
    obtain ⟨j', hj⟩ := exists_snd (σ ⟨k, j⟩) (e k) (hσ _)
    refine ⟨⟨e k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [hi, hj]

variable [Fintype K₁] [Fintype K₂] [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

/- English proof (translation)
Simplify using `only [mseg, Function.comp, hs]`. Conclude with `(Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩)).symm`.
-/
theorem mseg_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    mseg y s₂ = mseg (y ∘ σ) s₁ := by
  simp only [mseg, Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩)).symm

/- English proof (translation)
Simplify using `only [Function.comp, hs]`. Conclude with `(Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩ ^ a k)).symm`.
-/
theorem mon_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) (a : K₂ → ℤ) :
    ∏ k, y ⟨k, s₂ k⟩ ^ a k = ∏ k, (y ∘ σ) ⟨k, s₁ k⟩ ^ (a ∘ e) k := by
  simp only [Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩ ^ a k)).symm

/- English proof (translation)
Unfold `chartRing`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, rfl⟩`. Take `⟨t₁, ht⟩` from `exists_down e σ hσ t`. Conclude with `⟨t₁, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩`. Introduce and unpack `⟨t, rfl⟩`. Take `⟨t₂, ht⟩` from `exists_up e σ hσ t`.

Conclude with `⟨t₂, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩`.
-/
theorem chartRing_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    chartRing O (mseg y) s₂ = chartRing O (mseg (y ∘ σ)) s₁ := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨t₁, ht⟩ := exists_down e σ hσ t
    exact ⟨t₁, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t₂, ht⟩ := exists_up e σ hσ t
    exact ⟨t₂, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩

end PositivityTheory.Xgn.A_relabel_bundle

open PositivityTheory.Xgn.A_relabel_bundle in
/- English proof (translation)
Introduce `O _ Ω _ _ K₁ _ _ ι₁ _ K₂ _ _ ι₂ _ e σ hσ y`. Use `⟨pointIdeal_eq O e σ hσ y, fnField_eq O e σ hσ y, fun N V _ _ E₁ => ?_⟩` and prove the remaining obligations. Use `choose d hd using exists_down e σ hσ`. Establish `hm : ∀ s, mseg y s = mseg (y ∘ σ) (d s)` using `fun s => mseg_eq e σ y (hd s)`. Establish `hc : ∀ s, chartRing O (mseg y) s = chartRing O (mseg (y ∘ σ)) (d s)` using `fun s => chartRing_eq O e σ hσ y (hd s)`.

Use `⟨{ lat := fun s => E₁.lat (d s) stable := fun s a ha v hv => E₁.stable (d s) a (by rw [← hc]; exact ha) v hv frame := fun s hs => by` and prove the remaining obligations. Simplify using `only [hc]`. Conclude with `E₁.frame (d s) (by rw [← hm]; exact hs)`. Use `overlap := fun s t hs ht v hv => by`. Simplify using `only [hm]`.

Conclude with `E₁.overlap (d s) (d t) (by rw [← hm]; exact hs) (by rw [← hm]; exact ht) v hv },`. Use `fun s₁ s₂ h => ?_, fun w b h => ⟨fun s hs i => ?_⟩⟩`. Use `show E₁.lat (d s₂) = E₁.lat s₁`. Rewrite using `[down_unique e σ (hd s₂) h]`. Establish `hs' : segreVec (y ∘ σ) (d s) ≠ 0` using `by show mseg (y ∘ σ) (d s) ≠ 0`.

Rewrite using `[← hm]`. Conclude with `hs`. Use `(h.graded (d s) hs' i).trans ?_` and prove the remaining obligations. Establish `hc' : chartRing O (segreVec y) s = chartRing O (segreVec (y ∘ σ)) (d s)` using `hc s`. Unfold `degLat`.

Rewrite using `[hc', mon_eq e σ y (hd s) (b i)]`.
-/
theorem PositivityTheory.Xgn.t_relabel_bundle : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) → ∀ y : (Σ k, ι₂ k) → Ω, pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) ∧ fnField O y = fnField O (y ∘ σ) ∧ ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E₁ : ChartBundle O (mseg (y ∘ σ)) N V), ∃ E₂ : ChartBundle O (mseg y) N V, (∀ (s₁ : ∀ k, ι₁ k) (s₂ : ∀ k, ι₂ k), (∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) → E₂.lat s₂ = E₁.lat s₁) ∧ ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K₂ → ℤ), IsFlagFrame (y ∘ σ) E₁ w (fun i => b i ∘ e) → IsFlagFrame y E₂ w b := by
  intro O _ Ω _ _ K₁ _ _ ι₁ _ K₂ _ _ ι₂ _ e σ hσ y
  refine ⟨pointIdeal_eq O e σ hσ y, fnField_eq O e σ hσ y, fun N V _ _ E₁ => ?_⟩
  choose d hd using exists_down e σ hσ
  have hm : ∀ s, mseg y s = mseg (y ∘ σ) (d s) := fun s => mseg_eq e σ y (hd s)
  have hc : ∀ s, chartRing O (mseg y) s = chartRing O (mseg (y ∘ σ)) (d s) :=
    fun s => chartRing_eq O e σ hσ y (hd s)
  refine ⟨{ lat := fun s => E₁.lat (d s)
            stable := fun s a ha v hv => E₁.stable (d s) a (by rw [← hc]; exact ha) v hv
            frame := fun s hs => by
              simp only [hc]
              exact E₁.frame (d s) (by rw [← hm]; exact hs)
            overlap := fun s t hs ht v hv => by
              simp only [hm]
              exact E₁.overlap (d s) (d t) (by rw [← hm]; exact hs) (by rw [← hm]; exact ht) v hv },
    fun s₁ s₂ h => ?_, fun w b h => ⟨fun s hs i => ?_⟩⟩
  · show E₁.lat (d s₂) = E₁.lat s₁
    rw [down_unique e σ (hd s₂) h]
  · have hs' : segreVec (y ∘ σ) (d s) ≠ 0 := by
      show mseg (y ∘ σ) (d s) ≠ 0
      rw [← hm]
      exact hs
    refine (h.graded (d s) hs' i).trans ?_
    have hc' : chartRing O (segreVec y) s = chartRing O (segreVec (y ∘ σ)) (d s) := hc s
    unfold degLat
    rw [hc', mon_eq e σ y (hd s) (b i)]
