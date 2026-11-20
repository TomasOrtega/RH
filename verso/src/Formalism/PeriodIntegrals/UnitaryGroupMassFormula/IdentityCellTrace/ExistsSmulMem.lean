import Mathlib
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Lemmata.GeneralBFactThirdTail.Imports

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.IdCellInSW

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_third''''''.goal1 .. | (apply Bl.general_b_fact_third''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third''''''.goal1 <;> assumption)`.
-/
theorem exists_smul_mem (Λ : Submodule (𝓞 E) V) (hsp : Submodule.span E (Λ : Set V) = ⊤) (x : V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ Λ := by
  first | exact Bl.general_b_fact_third''''''.goal1 .. | (apply Bl.general_b_fact_third''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third''''''.goal1 <;> assumption)

variable [StarRing E]

/- English proof (translation)
Take `⟨s, _, b, hb, hsL⟩` from `Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 E) Λ hsp`. Take `⟨d, hd, hdL⟩` from `Formalism.HermitianLatticesTheory.dualLattice_denom b Λ hΛ`. Take `⟨bs, hbs⟩` from `Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b`. Establish `hbL : ∀ i, b i ∈ Λ` using `fun i => by rw [hb i]; exact hsL i.2`. Use `⟨∑ k, star (f ⟨b k, hbL k⟩) • bs k, ?_⟩` and prove the remaining obligations.

Use `set w := ∑ k, star (f ⟨b k, hbL k⟩) • bs k with hw`. Establish `e : ∀ j k, h (bs k) (b j) = if j = k then 1 else 0`. Introduce `j k`. Rewrite using `[← hs.eq (b j) (bs k), hbs]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hwb : ∀ j, h w (b j) = f ⟨b j, hbL j⟩`. Introduce `j`. Simplify using `[hw, e, starRingEnd_apply, star_star]`. Establish `hspL : Submodule.span (𝓞 E) (Set.range b) ≤ Λ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hbL j`. Establish `hspan : ∀ u (hu : u ∈ Submodule.span (𝓞 E) (Set.range b)) (huL : u ∈ Λ), h w u = f ⟨u, huL⟩`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Introduce `_`. Conclude with `hwb j`. Consider the case `zero`.

Introduce `huL`. Establish `: (⟨0, huL⟩ : Λ) = 0` using `rfl`. Rewrite using `[this, map_zero, map_zero]`. Consider the case `add x y hx hy ihx ihy`. Introduce `huL`.

Establish `e2 : (⟨x + y, huL⟩ : Λ) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩` using `rfl`. Rewrite using `[e2, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]`. Consider the case `smul r x hx ih`. Introduce `huL`. Establish `e2 : (⟨r • x, huL⟩ : Λ) = r • ⟨x, hspL hx⟩` using `rfl`.

Rewrite using `[e2, f.map_smul, ← algebraMap_smul E r x, (h w).map_smul, ih (hspL hx), algebraMap_smul]`. Introduce `y hy`. Establish `h1` using `hspan (d • y) (hdL y hy) (Λ.smul_mem d hy)`. Establish `e2 : (⟨d • y, Λ.smul_mem d hy⟩ : Λ) = d • ⟨y, hy⟩` using `rfl`. Rewrite `h1` using `[e2, f.map_smul, ← algebraMap_smul E d y, (h w).map_smul, ← algebraMap_smul E d (f _), smul_eq_mul, smul_eq_mul]`.

Conclude with `mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1`.
-/
theorem riesz [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (f : Λ →ₗ[𝓞 E] E) : ∃ w : V, ∀ y (hy : y ∈ Λ), h w y = f ⟨y, hy⟩ := by
  classical
  obtain ⟨s, _, b, hb, hsL⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 E) Λ hsp
  obtain ⟨d, hd, hdL⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom b Λ hΛ
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbL : ∀ i, b i ∈ Λ := fun i => by rw [hb i]; exact hsL i.2
  refine ⟨∑ k, star (f ⟨b k, hbL k⟩) • bs k, ?_⟩
  set w := ∑ k, star (f ⟨b k, hbL k⟩) • bs k with hw
  have e : ∀ j k, h (bs k) (b j) = if j = k then 1 else 0 := by
    intro j k
    rw [← hs.eq (b j) (bs k), hbs]
    split_ifs <;> simp
  have hwb : ∀ j, h w (b j) = f ⟨b j, hbL j⟩ := by
    intro j
    simp [hw, e, starRingEnd_apply, star_star]
  have hspL : Submodule.span (𝓞 E) (Set.range b) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbL j
  have hspan : ∀ u (hu : u ∈ Submodule.span (𝓞 E) (Set.range b)) (huL : u ∈ Λ),
      h w u = f ⟨u, huL⟩ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro _
      exact hwb j
    | zero =>
      intro huL
      have : (⟨0, huL⟩ : Λ) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro huL
      have e2 : (⟨x + y, huL⟩ : Λ) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e2, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro huL
      have e2 : (⟨r • x, huL⟩ : Λ) = r • ⟨x, hspL hx⟩ := rfl
      rw [e2, f.map_smul, ← algebraMap_smul E r x, (h w).map_smul, ih (hspL hx), algebraMap_smul]
  intro y hy
  have h1 := hspan (d • y) (hdL y hy) (Λ.smul_mem d hy)
  have e2 : (⟨d • y, Λ.smul_mem d hy⟩ : Λ) = d • ⟨y, hy⟩ := rfl
  rw [e2, f.map_smul, ← algebraMap_smul E d y, (h w).map_smul, ← algebraMap_smul E d (f _),
    smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1

omit [StarRing E] in

/- English proof (translation)
Set `N : Submodule (𝓞 E) Λ` to `(X.restrictScalars (𝓞 E)).comap Λ.subtype`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.mpr hΛ`. Establish `htf : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N)`. Use `⟨fun r hr q₁ q₂ hq => ?_⟩` and prove the remaining obligations. Establish `hr0 : r ≠ 0` using `hr.ne_zero`.

Take `⟨y₁, rfl⟩` from `N.mkQ_surjective q₁`. Take `⟨y₂, rfl⟩` from `N.mkQ_surjective q₂`. Establish `hq' : N.mkQ (r • (y₁ - y₂)) = 0`. Rewrite using `[map_smul, map_sub, smul_sub, sub_eq_zero]`. Conclude with `hq`.

Rewrite `hq'` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `hmem : ((r • (y₁ - y₂) : Λ) : V) ∈ X` using `hq'`. Establish `hrE : algebraMap (𝓞 E) E r ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr0`. Establish `e : ((y₁ - y₂ : Λ) : V) = (algebraMap (𝓞 E) E r)⁻¹ • ((r • (y₁ - y₂) : Λ) : V)`.

Rewrite using `[Submodule.coe_smul, ← algebraMap_smul E r, smul_smul, inv_mul_cancel₀ hrE, one_smul]`. Use `show ((y₁ - y₂ : Λ) : V) ∈ X`. Rewrite using `[e]`. Conclude with `X.smul_mem _ hmem`. Establish `: Module.FinitePresentation (𝓞 E) (Λ ⧸ N)` using `Module.finitePresentation_of_finite _ _`.

Establish `: Module.Projective (𝓞 E) (Λ ⧸ N)` using `Module.Flat.projective_of_finitePresentation`. Take `⟨s, hs⟩` from `Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective`. Set `ρ : Λ →ₗ[𝓞 E] Λ` to `LinearMap.id - s ∘ₗ N.mkQ`. Use `⟨ρ, fun y => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h0 : N.mkQ (ρ y) = 0`.

Use `congrArg (fun φ => φ (N.mkQ y)) hs` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this`. Simplify using `only [ρ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp, Function.comp_apply, map_sub, this, sub_self]`. Rewrite `h0` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `h0`.

Establish `h0 : N.mkQ y = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hy`. Simplify using `[ρ, h0]`.
-/
theorem exists_retract (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ y, ((ρ y : Λ) : V) ∈ X) ∧ ∀ y : Λ, (y : V) ∈ X → ρ y = y := by
  classical
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  have htf : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    refine ⟨fun r hr q₁ q₂ hq => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨y₁, rfl⟩ := N.mkQ_surjective q₁
    obtain ⟨y₂, rfl⟩ := N.mkQ_surjective q₂
    have hq' : N.mkQ (r • (y₁ - y₂)) = 0 := by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero]
      exact hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : ((r • (y₁ - y₂) : Λ) : V) ∈ X := hq'
    have hrE : algebraMap (𝓞 E) E r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr0
    have e : ((y₁ - y₂ : Λ) : V) = (algebraMap (𝓞 E) E r)⁻¹ • ((r • (y₁ - y₂) : Λ) : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul E r, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    show ((y₁ - y₂ : Λ) : V) ∈ X
    rw [e]
    exact X.smul_mem _ hmem
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s ∘ₗ N.mkQ
  refine ⟨ρ, fun y => ?_, fun y hy => ?_⟩
  · have h0 : N.mkQ (ρ y) = 0 := by
      have := congrArg (fun φ => φ (N.mkQ y)) hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
        Function.comp_apply, map_sub, this, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · have h0 : N.mkQ y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    simp [ρ, h0]

end PI.UnitaryGroupMassFormula.IdCellInSW
