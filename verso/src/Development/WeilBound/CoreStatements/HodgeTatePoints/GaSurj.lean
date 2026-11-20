import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq

noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

/- English proof (translation)
The claim follows from `Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)`.
-/
theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, hy, rfl⟩`.
-/
theorem proj_mem_omHT (σ : E →+* K) {y : Ω} (hy : y ∈ D.om') : eigProj D.ρΩ σ y ∈ D.omHT σ :=
  ⟨y, hy, rfl⟩

/- English proof (translation)
Unfold `HTChart.q`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `proj_mem_omHT D σ (h_mem_om' D _)`.
-/
theorem q_mem (σ : E →+* K) (x : Fin N → A) : D.q σ x ∈ D.omHT σ := by
  unfold HTChart.q
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact proj_mem_omHT D σ (h_mem_om' D _)

/- English proof (translation)
Unfold `HTChart.q`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`.
-/
theorem q_add (σ : E →+* K) (x y : Fin N → A) : D.q σ (x + y) = D.q σ x + D.q σ y := by
  unfold HTChart.q
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `HTChart.q`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`.
-/
theorem q_smul (σ : E →+* K) (a : A) (x : Fin N → A) : D.q σ (a • x) = a • D.q σ x := by
  unfold HTChart.q
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Use `choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)`. Use `choose b hb using fun i => hσ (z i)`. Establish `hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v`. Introduce `a v`. Establish `h1` using `congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)`. Establish `h2` using `congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2`.

Rewrite using `[h1, h2]`. Use `⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hz]`. Rewrite using `[map_sum, map_sum]`. Simplify using `only [he, map_add, hrho, ← hb, algebraMap_smul]`.

Rewrite using `[Finset.sum_add_distrib, map_sum, Finset.smul_sum]`. Unfold `HTChart.q`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, ← Nat.cast_smul_eq_nsmul A]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (z : Fin N → 𝓞 E) :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ (D.h z) = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)
  choose b hb using fun i => hσ (z i)
  have hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v := by
    intro a v
    have h1 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)
    have h2 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
    rw [h1, h2]
  refine ⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩
  conv_lhs => rw [hz]
  rw [map_sum, map_sum]
  simp only [he, map_add, hrho, ← hb, algebraMap_smul]
  rw [Finset.sum_add_distrib, map_sum, Finset.smul_sum]
  unfold HTChart.q
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

/- English proof (translation)
Take `⟨s, hs, t, ht, rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨y0, hy0, rfl⟩` from `Submodule.mem_map.mp ht`. Use `clear hy ht`. Establish `key : ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y'`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨z, rfl⟩` from `hv`. Conclude with `toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z`. Consider the case `zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩`. Consider the case `add u v _ _ hu hv`.

Take `⟨x1, y1, hy1, e1⟩` from `hu`. Take `⟨x2, y2, hy2, e2⟩` from `hv`. Use `⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, e1, e2, q_add, map_add, smul_add]`. Normalize the expressions using the abelian group laws.

Consider the case `smul a v _ hv`. Take `⟨x1, y1, hy1, e1⟩` from `hv`. Use `⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]`. Take `⟨x, y', hy', e⟩` from `key`.

Establish `ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0) = ((p : A) ^ R) • eigProj D.ρΩ σ y0`. Simplify using `[LinearMap.map_smul_of_tower]`. Use `⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, e, ht0, map_add, smul_add, add_assoc]`.
-/
theorem exists_q_add (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    {y : Ω} (hy : y ∈ D.om') :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ y = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp ht
  clear hy ht
  have key : ∃ x : Fin N → A, ∃ y' ∈ D.om,
      eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
    induction hs using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z
    | zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩
    | add u v _ _ hu hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hu
      obtain ⟨x2, y2, hy2, e2⟩ := hv
      refine ⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩
      rw [map_add, e1, e2, q_add, map_add, smul_add]
      abel
    | smul a v _ hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hv
      refine ⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩
      rw [LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]
  obtain ⟨x, y', hy', e⟩ := key
  have ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0)
      = ((p : A) ^ R) • eigProj D.ρΩ σ y0 := by
    simp [LinearMap.map_smul_of_tower]
  refine ⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩
  rw [map_add, e, ht0, map_add, smul_add, add_assoc]

end

/- English proof (translation)
Introduce `A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ`. Use `⟨fun x => q_mem D σ x, ?_, ?_⟩` and prove the remaining obligations. Unfold `HTChart.omHT eigQuot`. Apply `Submodule.FG.map` to reduce the goal to its premises. Unfold `HTChart.om'`.

Use `Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)` and prove the remaining obligations. Take `⟨T, hT⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)`. Use `⟨T.image D.h, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce `v hv`.

Simplify using `only [Finset.coe_image, Set.mem_image] at hv`. Take `⟨z, _, rfl⟩` from `hv`. Conclude with `⟨z, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`.

Establish `hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E))` using `hT ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`. Conclude with `Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)`. Consider the case `zero => simp`.

Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hu hv`. Consider the case `smul n u _ hu`. Rewrite using `[map_zsmul]`.

Conclude with `zsmul_mem hu n`. Introduce `y hy`. Simplify using `only [HTChart.omHT, eigQuot] at hy`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.mp hy`. Take `⟨x, y'', hy'', e⟩` from `exists_q_add D σ hσ hw`.

Take `⟨d, hd⟩` from `hdiv`. Use `⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))`. Rewrite using `[LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]`. Use `congr 1`.

Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_surj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ
  classical
  refine ⟨fun x => q_mem D σ x, ?_, ?_⟩
  · unfold HTChart.omHT eigQuot
    apply Submodule.FG.map
    unfold HTChart.om'
    refine Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)
    refine ⟨T.image D.h, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨z, _, rfl⟩ := hv
      exact ⟨z, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E)) := hT ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem w hw =>
        exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      | smul n u _ hu =>
        rw [map_zsmul]
        exact zsmul_mem hu n
  · intro y hy
    simp only [HTChart.omHT, eigQuot] at hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, y'', hy'', e⟩ := exists_q_add D σ hσ hw
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩
    · exact Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))
    · rw [LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]
      congr 1
      simp only [smul_smul]
      congr 1
      ring

end PositivityTheory.HtPt.Ga
