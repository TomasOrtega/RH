import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality

open Module Submodule

noncomputable section

namespace Formalism.F

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Establish `hd` using `discreteTopology_span_range_of_linearIndependent u hu`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Use `haveI := hd`. Establish `hZ : LinearIndependent ℤ u` using `hu.restrict_scalars' ℤ`. Rewrite using `[covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span hZ)]`.

Simplify using `only [Basis.span_apply]`.
-/
theorem discreteTopology_span_range_and_covol {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E)
    (hu : LinearIndependent ℝ u) :
    DiscreteTopology (span ℤ (Set.range u)) ∧
      covol (span ℤ (Set.range u)) = Real.sqrt (Matrix.gram ℝ u).det := by
  have hd := discreteTopology_span_range_of_linearIndependent u hu
  refine ⟨hd, ?_⟩
  haveI := hd
  have hZ : LinearIndependent ℤ u := hu.restrict_scalars' ℤ
  rw [covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span hZ)]
  simp only [Basis.span_apply]

/- English proof (translation)
Set `b₁` to `Module.finBasis ℤ L₁`. Set `b₂` to `Module.finBasis ℤ L₂`. Set `v₁ : Fin (Module.finrank ℤ L₁) → E` to `fun i => (b₁ i : E)`. Set `v₂ : Fin (Module.finrank ℤ L₂) → E` to `fun i => (b₂ i : E)`. Establish `hv₁ : LinearIndependent ℝ v₁` using `linearIndependent_coe_basis''' L₁ b₁`.

Establish `hv₂ : LinearIndependent ℝ v₂` using `linearIndependent_coe_basis''' L₂ b₂`. Establish `horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0` using `fun i j => h _ (b₁ i).2 _ (b₂ j).2`. Establish `horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0` using `fun i j => by`. Rewrite using `[real_inner_comm]`. Conclude with `horth j i`.

Establish `hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂))`. Apply `Submodule.IsOrtho.disjoint` to reduce the goal to its premises. Rewrite using `[Submodule.isOrtho_span]`. Introduce and unpack `_ ⟨i, rfl⟩ _ ⟨j, rfl⟩`. Conclude with `horth i j`.

Establish `hli` using `hv₁.sum_type hv₂ hdisj`. Establish `hs₁ : span ℤ (Set.range v₁) = L₁` using `span_range_coe_basis' L₁ b₁`. Establish `hs₂ : span ℤ (Set.range v₂) = L₂` using `span_range_coe_basis' L₂ b₂`. Establish `hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂`. Rewrite using `[Set.Sum.elim_range, Submodule.span_union, hs₁, hs₂]`.

Take `⟨hd, hc⟩` from `discreteTopology_span_range_and_covol _ hli`. Rewrite `hd`, `hc` using `[hspan]`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `hc₁ : covol L₁ = Real.sqrt (Matrix.gram ℝ v₁).det` using `covol_eq_gram E L₁ _ b₁`. Establish `hc₂ : covol L₂ = Real.sqrt (Matrix.gram ℝ v₂).det` using `covol_eq_gram E L₂ _ b₂`.

Establish `hp₁ : 0 ≤ (Matrix.gram ℝ v₁).det` using `(det_gram_basis_pos L₁ b₁).le`. Establish `hg : Matrix.gram ℝ (Sum.elim v₁ v₂) = Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂)`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']`. Rewrite using `[hc, hc₁, hc₂, hg, Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul hp₁]`.
-/
theorem discreteTopology_sup_and_covol_sup (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) :
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ covol (L₁ ⊔ L₂) = covol L₁ * covol L₂ := by
  classical

  let b₁ := Module.finBasis ℤ L₁
  let b₂ := Module.finBasis ℤ L₂
  let v₁ : Fin (Module.finrank ℤ L₁) → E := fun i => (b₁ i : E)
  let v₂ : Fin (Module.finrank ℤ L₂) → E := fun i => (b₂ i : E)
  have hv₁ : LinearIndependent ℝ v₁ := linearIndependent_coe_basis''' L₁ b₁
  have hv₂ : LinearIndependent ℝ v₂ := linearIndependent_coe_basis''' L₂ b₂
  have horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0 := fun i j => h _ (b₁ i).2 _ (b₂ j).2
  have horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0 := fun i j => by
    rw [real_inner_comm]; exact horth j i
  have hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂)) := by
    apply Submodule.IsOrtho.disjoint
    rw [Submodule.isOrtho_span]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact horth i j
  have hli := hv₁.sum_type hv₂ hdisj
  have hs₁ : span ℤ (Set.range v₁) = L₁ := span_range_coe_basis' L₁ b₁
  have hs₂ : span ℤ (Set.range v₂) = L₂ := span_range_coe_basis' L₂ b₂
  have hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hs₁, hs₂]
  obtain ⟨hd, hc⟩ := discreteTopology_span_range_and_covol _ hli
  rw [hspan] at hd hc
  refine ⟨hd, ?_⟩
  have hc₁ : covol L₁ = Real.sqrt (Matrix.gram ℝ v₁).det := covol_eq_gram E L₁ _ b₁
  have hc₂ : covol L₂ = Real.sqrt (Matrix.gram ℝ v₂).det := covol_eq_gram E L₂ _ b₂
  have hp₁ : 0 ≤ (Matrix.gram ℝ v₁).det := (det_gram_basis_pos L₁ b₁).le
  have hg : Matrix.gram ℝ (Sum.elim v₁ v₂) =
      Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']
  rw [hc, hc₁, hc₂, hg, Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul hp₁]

/- English proof (translation)
Use `haveI := hL`. Distinguish the cases in `hN : N = ⊥`. Substitute `hN` using the available equality. Establish `h0 : covol (⊥ : Submodule ℤ E) = 1` using `(covol_basic_properties E).1`. Establish `hr : rk (⊥ : Submodule ℤ E) = 0` using `by simp [rk]`.

Simplify using `[deg, h0, hr]`. Use `haveI : DiscreteTopology N := discreteTopology_of_le hNL`. Establish `hs : slope N ≤ muMax L` using `slopeLeMuMax_of (slopesBdd_of gram_det_le) E L N hL hNL hN`. Establish `hk : 0 < rk N` using `Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN)`. Establish `hk' : (0 : ℝ) < (rk N : ℝ)` using `by exact_mod_cast hk`.

Unfold `slope at hs`. Rewrite `hs` using `[div_le_iff₀ hk']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degree_le_rank_mul_maxSlope (L N : Submodule ℤ E) (hL : DiscreteTopology L) (hNL : N ≤ L) :
    deg N ≤ rk N * muMax L := by
  haveI := hL
  by_cases hN : N = ⊥
  · subst hN
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · haveI : DiscreteTopology N := discreteTopology_of_le hNL
    have hs : slope N ≤ muMax L := slopeLeMuMax_of (slopesBdd_of gram_det_le) E L N hL hNL hN
    have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN)
    have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith

/- English proof (translation)
Use `haveI := hQ`. Distinguish the cases in `hQ0 : Q = ⊥`. Substitute `hQ0` using the available equality. Establish `h0 : covol (⊥ : Submodule ℤ E) = 1` using `(covol_basic_properties E).1`. Establish `hr : rk (⊥ : Submodule ℤ E) = 0` using `by simp [rk]`.

Simplify using `[deg, h0, hr]`. Establish `hs` using `slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0 ψ 1 hinj (fun x => by simpa using hψ x)`. Rewrite `hs` using `[Real.log_one, add_zero]`. Establish `hk : 0 < rk Q` using `Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)`. Establish `hk' : (0 : ℝ) < (rk Q : ℝ)` using `by exact_mod_cast hk`.

Unfold `slope at hs`. Rewrite `hs` using `[div_le_iff₀ hk']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degree_le_rank_mul_maxSlope_of_injective (Q M : Submodule ℤ E) (hQ : DiscreteTopology Q)
    (hM : DiscreteTopology M) (ψ : Q →ₗ[ℤ] M) (hinj : Function.Injective ψ)
    (hψ : ∀ x : Q, ‖((ψ x : M) : E)‖ ≤ ‖(x : E)‖) : deg Q ≤ rk Q * muMax M := by
  haveI := hQ
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · have hs := slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0
      ψ 1 hinj (fun x => by simpa using hψ x)
    rw [Real.log_one, add_zero] at hs
    have hk : 0 < rk Q := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)
    have hk' : (0 : ℝ) < (rk Q : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `haveI := h1`. Use `haveI := h2`. Use `haveI := hd`. Use `haveI hNd : DiscreteTopology N := discreteTopology_of_le hN`. Take `⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection` from `⟨_, rfl⟩`.

Establish `hortho : span ℝ (L₁ : Set E) ≤ (span ℝ (L₂ : Set E))ᗮ`. Rewrite using `[← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]`. Introduce `x hx y hy`. Conclude with `h x hx y hy`. Establish `hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0` using `fun x hx => by`.

Rewrite using `[hPdef, Submodule.starProjection_apply_eq_zero_iff]`. Conclude with `hortho hx`. Establish `hP1 : ∀ x ∈ L₁, P x = 0` using `fun x hx => hP0 x (subset_span hx)`. Establish `hP2 : ∀ x ∈ L₂, P x = x` using `fun x hx => by`. Rewrite using `[hPdef, Submodule.starProjection_eq_self_iff]`.

Conclude with `subset_span hx`. Establish `hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁`. Introduce `x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add, hP1 y hy, hP2 z hz, zero_add, add_sub_cancel_right]`.

Conclude with `⟨hz, hy⟩`. Establish `hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖` using `fun x => by`. Rewrite using `[hPdef]`. Conclude with `Submodule.norm_starProjection_apply_le _ x`. Use `set K : Submodule ℤ E := N ⊓ L₁ with hK`.

Establish `hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E)` using `Submodule.span_mono (fun x hx => hx.2)`. Establish `hsat : IsSaturated N K`. Use `⟨inf_le_left, fun x hx hxs => ⟨hx, ?_⟩⟩` and prove the remaining obligations. Establish `h0 : P x = 0` using `hP0 x (hKspan hxs)`. Use `(hP3 x (hN hx)).2` as an intermediate fact.

Rewrite `this` using `[h0, sub_zero]`. Then use the resulting hypothesis. Take `⟨hQd, hrk, hdeg⟩` from `degree_quotient E N K hNd hsat`. Use `set Q := quot N K with hQ`. Establish `hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x`. Introduce `x hx`.

Rewrite using `[Submodule.starProjection_orthogonal_val, map_sub]`. Establish `hS : (span ℝ (K : Set E)).starProjection x ∈ span ℝ (L₁ : Set E)`. Apply `hKspan` to reduce the goal to its premises. Rewrite using `[Submodule.starProjection_apply]`. Conclude with `SetLike.coe_mem _`.

Rewrite using `[hP0 _ hS, sub_zero]`. Establish `hQmem : ∀ y ∈ Q, P y ∈ L₂`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Express the relevant statement in the definitionally equal form `P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂`.

Rewrite using `[hPR x hx]`. Conclude with `(hP3 x (hN hx)).1`. Set `ψ : Q →ₗ[ℤ] L₂` to `LinearMap.codRestrict L₂ ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)`. Establish `hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y` using `fun y => rfl`. Establish `hinj : Function.Injective ψ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy0`. Establish `hPy : P y = 0`. Rewrite using `[← hψ, hy0]`. Both sides reduce to the same expression.

Take `⟨y, hyQ⟩` from `y`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hyQ`. Express the relevant statement in the definitionally equal form `P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 at hPy`. Rewrite `hPy` using `[hPR x hx]`. Establish `hx1 : x ∈ L₁`.

Use `(hP3 x (hN hx)).2` as an intermediate fact. Rewrite `this` using `[hPy, sub_zero]`. Then use the resulting hypothesis. Establish `hxK : x ∈ span ℝ (K : Set E)` using `subset_span ⟨hx, hx1⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(span ℝ (K : Set E))ᗮ.starProjection x = 0`.

Rewrite using `[Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]`. Establish `hnorm : ∀ y : Q, ‖((ψ y : L₂) : E)‖ ≤ ‖(y : E)‖` using `fun y => by`. Rewrite using `[hψ]`. Conclude with `hPnorm _`. Establish `hdK : deg K ≤ rk K * muMax L₁` using `degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right`.

Establish `hdQ : deg Q ≤ rk Q * muMax L₂` using `degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj hnorm`. Establish `hk : 0 < rk N` using `Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)`. Establish `hk' : (0 : ℝ) < (rk N : ℝ)` using `by exact_mod_cast hk`. Establish `hK0 : (0 : ℝ) ≤ (rk K : ℝ)` using `Nat.cast_nonneg _`. Establish `hQ0 : (0 : ℝ) ≤ (rk Q : ℝ)` using `Nat.cast_nonneg _`.

Establish `e1 : (rk K : ℝ) * muMax L₁ ≤ (rk K : ℝ) * max (muMax L₁) (muMax L₂)` using `mul_le_mul_of_nonneg_left (le_max_left _ _) hK0`. Establish `e2 : (rk Q : ℝ) * muMax L₂ ≤ (rk Q : ℝ) * max (muMax L₁) (muMax L₂)` using `mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0`. Establish `hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ)` using `by exact_mod_cast hrk`. Unfold `slope`. Rewrite using `[div_le_iff₀ hk', hdeg, hrk']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_le_max_maxSlope (L₁ L₂ : Submodule ℤ E) (h1 : DiscreteTopology L₁)
    (h2 : DiscreteTopology L₂) (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0)
    (hd : DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E))
    (N : Submodule ℤ E) (hN : N ≤ L₁ ⊔ L₂) (hN0 : N ≠ ⊥) :
    slope N ≤ max (muMax L₁) (muMax L₂) := by
  haveI := h1
  haveI := h2
  haveI := hd
  haveI hNd : DiscreteTopology N := discreteTopology_of_le hN

  obtain ⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection := ⟨_, rfl⟩
  have hortho : span ℝ (L₁ : Set E) ≤ (span ℝ (L₂ : Set E))ᗮ := by
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    intro x hx y hy
    exact h x hx y hy
  have hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0 := fun x hx => by
    rw [hPdef, Submodule.starProjection_apply_eq_zero_iff]
    exact hortho hx
  have hP1 : ∀ x ∈ L₁, P x = 0 := fun x hx => hP0 x (subset_span hx)
  have hP2 : ∀ x ∈ L₂, P x = x := fun x hx => by
    rw [hPdef, Submodule.starProjection_eq_self_iff]
    exact subset_span hx
  have hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hP1 y hy, hP2 z hz, zero_add, add_sub_cancel_right]
    exact ⟨hz, hy⟩
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by
    rw [hPdef]; exact Submodule.norm_starProjection_apply_le _ x

  set K : Submodule ℤ E := N ⊓ L₁ with hK
  have hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E) :=
    Submodule.span_mono (fun x hx => hx.2)
  have hsat : IsSaturated N K := by
    refine ⟨inf_le_left, fun x hx hxs => ⟨hx, ?_⟩⟩
    have h0 : P x = 0 := hP0 x (hKspan hxs)
    have := (hP3 x (hN hx)).2
    rwa [h0, sub_zero] at this
  obtain ⟨hQd, hrk, hdeg⟩ := degree_quotient E N K hNd hsat
  set Q := quot N K with hQ

  have hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x := by
    intro x hx
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hS : (span ℝ (K : Set E)).starProjection x ∈ span ℝ (L₁ : Set E) := by
      apply hKspan
      rw [Submodule.starProjection_apply]
      exact SetLike.coe_mem _
    rw [hP0 _ hS, sub_zero]
  have hQmem : ∀ y ∈ Q, P y ∈ L₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂
    rw [hPR x hx]
    exact (hP3 x (hN hx)).1
  let ψ : Q →ₗ[ℤ] L₂ := LinearMap.codRestrict L₂
    ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)
  have hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y := fun y => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have hPy : P y = 0 := by
      rw [← hψ, hy0]; rfl
    obtain ⟨y, hyQ⟩ := y
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyQ
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 at hPy
    rw [hPR x hx] at hPy
    have hx1 : x ∈ L₁ := by
      have := (hP3 x (hN hx)).2
      rwa [hPy, sub_zero] at this
    have hxK : x ∈ span ℝ (K : Set E) := subset_span ⟨hx, hx1⟩
    apply Subtype.ext
    change (span ℝ (K : Set E))ᗮ.starProjection x = 0
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]
  have hnorm : ∀ y : Q, ‖((ψ y : L₂) : E)‖ ≤ ‖(y : E)‖ := fun y => by
    rw [hψ]; exact hPnorm _
  have hdK : deg K ≤ rk K * muMax L₁ := degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right
  have hdQ : deg Q ≤ rk Q * muMax L₂ := degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj hnorm
  have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ (rk K : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ (rk Q : ℝ) := Nat.cast_nonneg _
  have e1 : (rk K : ℝ) * muMax L₁ ≤ (rk K : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  have e2 : (rk Q : ℝ) * muMax L₂ ≤ (rk Q : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0
  have hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ) := by exact_mod_cast hrk
  unfold slope
  rw [div_le_iff₀ hk', hdeg, hrk']
  linarith

end

/- English proof (translation)
Introduce `E _ _ _ L₁ L₂ h1 h2 h`. Use `haveI := h1`. Use `haveI := h2`. Take `⟨hd, hc⟩` from `discreteTopology_sup_and_covol_sup L₁ L₂ h`. Use `⟨hd, ?_, ?_⟩` and prove the remaining obligations.

Establish `p1` using `covol_pos_of_discrete L₁`. Establish `p2` using `covol_pos_of_discrete L₂`. Unfold `deg`. Rewrite using `[hc, Real.log_mul p1.ne' p2.ne']`. Expand and normalize the polynomial expressions, which then agree.

Introduce `hL1 hL2`. Apply `le_antisymm` to reduce the goal to its premises. Use `show sSup (slopes (L₁ ⊔ L₂)) ≤ _`. Use `csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `t ⟨N, hN, hN0, rfl⟩`.

Conclude with `slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0`. Establish `hmono` using `muMaxMono_of (slopesBdd_of gram_det_le)`. Conclude with `max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1) (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)`.
-/
theorem orthogonal_sum_slope : OrthSum := by
  intro E _ _ _ L₁ L₂ h1 h2 h
  haveI := h1
  haveI := h2
  obtain ⟨hd, hc⟩ := discreteTopology_sup_and_covol_sup L₁ L₂ h
  refine ⟨hd, ?_, ?_⟩
  · have p1 := covol_pos_of_discrete L₁
    have p2 := covol_pos_of_discrete L₂
    unfold deg
    rw [hc, Real.log_mul p1.ne' p2.ne']
    ring
  · intro hL1 hL2
    apply le_antisymm
    · show sSup (slopes (L₁ ⊔ L₂)) ≤ _
      refine csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      exact slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0
    · have hmono := muMaxMono_of (slopesBdd_of gram_det_le)
      exact max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1)
        (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)

end Formalism.F
