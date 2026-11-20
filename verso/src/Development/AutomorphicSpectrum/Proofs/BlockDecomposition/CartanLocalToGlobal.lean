import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.LinRedFactor

open GlobalTheory.LinRed

variable {n : ℕ}

/- English proof (translation)
Establish `hc : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Use `IsCompact.of_isClosed_subset (t := _) hc ?_ ?_` and prove the remaining obligations. Establish `: (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {A | A * Aᴴ = 1}`. Use extensionality with `A`. Conclude with `Matrix.mem_unitaryGroup_iff`.

Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const`. Introduce `A hA i _ j _`. Simplify using `using entry_norm_bound_of_unitary hA i j`.
-/
theorem isCompact_unitary_fin :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := _) hc ?_ ?_
  · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

/- English proof (translation)
The claim follows from `Matrix.mem_unitaryGroup_iff.1 hU`.
-/
theorem unitary_mul_star {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hU

/- English proof (translation)
The claim follows from `Matrix.mem_unitaryGroup_iff'.1 hU`.
-/
theorem star_mul_unitary {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 hU

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Uᴴ * (s * t) * U := by`. Rewrite using `[unitary_mul_star hU]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem conj_mul_conj {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (s t : Matrix (Fin n) (Fin n) ℂ) :
    (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * (s * t) * U := by
  calc (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * s * (U * Uᴴ) * t * U := by
        simp only [Matrix.mul_assoc]
    _ = Uᴴ * (s * t) * U := by
        rw [unitary_mul_star hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← conj_mul_conj hU]`. Conclude with `hs.mul ht`.
-/
theorem tri_mul {U s t : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hs : (Uᴴ * s * U).BlockTriangular id) (ht : (Uᴴ * t * U).BlockTriangular id) :
    (Uᴴ * (s * t) * U).BlockTriangular id := by
  rw [← conj_mul_conj hU]
  exact hs.mul ht

/- English proof (translation)
Simplify using `only [Matrix.BlockTriangular, Set.setOf_forall]`. Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j) continuous_const`.
-/
theorem isClosed_tri (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {s : Matrix (Fin n) (Fin n) ℂ | (Uᴴ * s * U).BlockTriangular id} := by
  simp only [Matrix.BlockTriangular, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
    continuous_const

/- English proof (translation)
Use `isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right` and prove the remaining obligations. Use `isClosed_of_closure_subset fun x hx => ?_` and prove the remaining obligations. Establish `hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))` using `closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx`. Conclude with `⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU)) (closure_mono Set.inter_subset_left hx), hxU⟩`.
-/
theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) :
    IsCompact (maxCpt G) := by
  refine isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx
  exact ⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU))
    (closure_mono Set.inter_subset_left hx), hxU⟩

def Good (G : Set (Matrix (Fin n) (Fin n) ℂ)) (U g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

/- English proof (translation)
Take `⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩` from `h₀`. Establish `hkk : k₀ * k₀ᴴ = 1` using `unitary_mul_star hk₀.2`. Establish `hkk' : k₀ᴴ * k₀ = 1` using `star_mul_unitary hk₀.2`. Establish `hsu : IsUnit s₀` using `hG.isUnit s₀ hs₀`. Establish `hss : s₀ * s₀⁻¹ = 1` using `Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)`.

Establish `hss' : s₀⁻¹ * s₀ = 1` using `Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)`. Establish `hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Establish `e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1`. Rewrite using `[← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]`. Establish `ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1)`.

Use `hφ.tendsto (k₀ * s₀)` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Use `filter_upwards [ht.eventually h] with g hg hgG`. Take `⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩` from `hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))`. Use `⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀, hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hkk, hss', Matrix.one_mul, Matrix.mul_one]`. Use `_ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]`. Use `_ = k₀ * k₁ * (s₁ * s₀) := by`.

Rewrite using `[e₁]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem good_nhds {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → Good G U g)
    {g₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : Good G U g₀) :
    ∀ᶠ g in 𝓝 g₀, g ∈ G → Good G U g := by
  obtain ⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩ := h₀
  have hkk : k₀ * k₀ᴴ = 1 := unitary_mul_star hk₀.2
  have hkk' : k₀ᴴ * k₀ = 1 := star_mul_unitary hk₀.2
  have hsu : IsUnit s₀ := hG.isUnit s₀ hs₀
  have hss : s₀ * s₀⁻¹ = 1 := Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hss' : s₀⁻¹ * s₀ = 1 := Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1 := by
    rw [← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]
  have ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1) := by
    have := hφ.tendsto (k₀ * s₀)
    rwa [e] at this
  filter_upwards [ht.eventually h] with g hg hgG
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩ :=
    hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))
  refine ⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀,
    hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩
  calc g = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by
        calc g = (k₀ * k₀ᴴ) * g * (s₀⁻¹ * s₀) := by
              rw [hkk, hss', Matrix.one_mul, Matrix.mul_one]
          _ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]
    _ = k₀ * k₁ * (s₁ * s₀) := by
        rw [e₁]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Use `haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)`. Establish `hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ | (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id}` using `(isClosed_tri U).preimage ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)`. Use `isClosedMap_snd_of_compactSpace _ hC` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, t⟩`. Conclude with `⟨(⟨k, hk⟩, g), t, rfl⟩`. Introduce and unpack `⟨⟨k, g'⟩, t, rfl⟩`. Conclude with `⟨k.1, k.2, t⟩`.
-/
theorem isClosed_factor {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ |
      ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  have hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ |
      (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id} :=
    (isClosed_tri U).preimage
      ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)
  have := isClosedMap_snd_of_compactSpace _ hC
  convert this using 1
  ext g
  constructor
  · rintro ⟨k, hk, t⟩
    exact ⟨(⟨k, hk⟩, g), t, rfl⟩
  · rintro ⟨⟨k, g'⟩, t, rfl⟩
    exact ⟨k.1, k.2, t⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, s, _, rfl, t⟩`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]` and apply the resulting hypothesis. Introduce and unpack `⟨k, hk, t⟩`.

Use `⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]`.
-/
theorem good_iff {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    Good G U g ↔ ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id := by
  constructor
  · rintro ⟨k, hk, s, _, rfl, t⟩
    refine ⟨k, hk, ?_⟩
    rwa [← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]
  · rintro ⟨k, hk, t⟩
    refine ⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩
    rw [← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]

/- English proof (translation)
Introduce `n G hG U hU h g hg`. Use `haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected`. Establish `hclosed : IsClosed {x : G | Good G U x.1}`. Establish `e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ | ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id}`. Use extensionality with `x`.

Conclude with `good_iff hG x.2`. Rewrite using `[e]`. Conclude with `(isClosed_factor hG U).preimage continuous_subtype_val`. Establish `hopen : IsOpen {x : G | Good G U x.1}`. Rewrite using `[isOpen_iff_eventually]`.

Introduce `x hx`. Use `(continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)` as an intermediate fact. Use `filter_upwards [this] with y hy using hy y.2`. Establish `hone : Good G U 1`. Use `⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_one, star_mul_unitary hU]`. Conclude with `Matrix.blockTriangular_one`. Establish `huniv` using `IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩`. Establish `hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1}` using `huniv ▸ Set.mem_univ _`. Conclude with `hmem`.
-/
theorem factor_of_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
    (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) →
    ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  intro n G hG U hU h g hg
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected
  have hclosed : IsClosed {x : G | Good G U x.1} := by
    have e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ |
        ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
      ext x
      exact good_iff hG x.2
    rw [e]
    exact (isClosed_factor hG U).preimage continuous_subtype_val
  have hopen : IsOpen {x : G | Good G U x.1} := by
    rw [isOpen_iff_eventually]
    intro x hx
    have := (continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)
    filter_upwards [this] with y hy using hy y.2
  have hone : Good G U 1 := by
    refine ⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩
    rw [Matrix.mul_one, star_mul_unitary hU]
    exact Matrix.blockTriangular_one
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩
  have hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1} := huniv ▸ Set.mem_univ _
  exact hmem

end GlobalTheory.CompanionTheory.LinRedFactor
