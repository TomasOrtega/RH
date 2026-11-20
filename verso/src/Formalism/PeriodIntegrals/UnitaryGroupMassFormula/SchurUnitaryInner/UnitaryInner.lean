import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable

namespace PI.UnitaryGroupMassFormula.SchurClosable.Main

open Filter Topology

/- English proof (translation)
The claim follows from `(⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y`.
-/
theorem unitary_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : inner ℂ (T x) (T y) = inner ℂ x y :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

/- English proof (translation)
Distinguish the cases in `h : ∃ x : D, (x : H) ≠ 0`. Take `⟨x₀, hx₀⟩` from `h`. Establish `hn : 0 < ‖(x₀ : H)‖` using `norm_pos_iff.mpr hx₀`. Establish `hs : 0 < ‖(x₀ : H)‖ ^ 2` using `pow_pos hn 2`. Establish `ht : 0 ≤ ‖A x₀‖ ^ 2` using `by positivity`.

Establish `h0` using `hK x₀ x₀`. Rewrite `h0` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Use `⟨‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2, div_nonneg ht hs.le, fun x y => ?_⟩` and prove the remaining obligations. Establish `hxy` using `hK x y`. Establish `hsC : ((‖(x₀ : H)‖ : ℂ)) ^ 2 ≠ 0`.

Establish `: ((‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hs.ne'`. Simplify using `using this`. Establish `key : ((‖(x₀ : H)‖ : ℂ)) ^ 2 * inner ℂ (A x) (A y) = ((‖A x₀‖ : ℂ)) ^ 2 * inner ℂ (x : H) (y : H)`. Take the linear combination `(inner ℂ (A x) (A y) + inner ℂ (x : H) (y : H)) * h0 - (((‖(x₀ : H)‖ : ℂ)) ^ 2 + ((‖A x₀‖ : ℂ)) ^ 2) * hxy`. Establish `e1 : ((‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ) = ((‖A x₀‖ : ℂ)) ^ 2 / ((‖(x₀ : H)‖ : ℂ)) ^ 2` using `by push_cast; ring`.

Rewrite using `[e1, div_mul_eq_mul_div, eq_div_iff hsC]`. Take the linear combination `key`. Simplify using `only [not_exists, not_not] at h`. Use `⟨0, le_rfl, fun x y => ?_⟩` and prove the remaining obligations. Establish `hx : x = 0` using `Subtype.ext (h x)`.

Simplify using `[hx]`.
-/
theorem alg {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (D : Submodule ℂ H) (A : D →ₗ[ℂ] H') (a : ℂ)
    (hK : ∀ x y : D,
      inner ℂ (x : H) (y : H) = a * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H) := by
  by_cases h : ∃ x : D, (x : H) ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h
    have hn : 0 < ‖(x₀ : H)‖ := norm_pos_iff.mpr hx₀
    have hs : 0 < ‖(x₀ : H)‖ ^ 2 := pow_pos hn 2
    have ht : 0 ≤ ‖A x₀‖ ^ 2 := by positivity
    have h0 := hK x₀ x₀
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
    refine ⟨‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2, div_nonneg ht hs.le, fun x y => ?_⟩
    have hxy := hK x y
    have hsC : ((‖(x₀ : H)‖ : ℂ)) ^ 2 ≠ 0 := by
      have : ((‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
      simpa using this
    have key : ((‖(x₀ : H)‖ : ℂ)) ^ 2 * inner ℂ (A x) (A y)
        = ((‖A x₀‖ : ℂ)) ^ 2 * inner ℂ (x : H) (y : H) := by
      linear_combination (inner ℂ (A x) (A y) + inner ℂ (x : H) (y : H)) * h0
        - (((‖(x₀ : H)‖ : ℂ)) ^ 2 + ((‖A x₀‖ : ℂ)) ^ 2) * hxy
    have e1 : ((‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ)
        = ((‖A x₀‖ : ℂ)) ^ 2 / ((‖(x₀ : H)‖ : ℂ)) ^ 2 := by push_cast; ring
    rw [e1, div_mul_eq_mul_div, eq_div_iff hsC]
    linear_combination key
  · simp only [not_exists, not_not] at h
    refine ⟨0, le_rfl, fun x y => ?_⟩
    have hx : x = 0 := Subtype.ext (h x)
    simp [hx]

/- English proof (translation)
Introduce `G H H' _ _ _ _ _ _ _ π π' hπ hπ' hirr D A hD hinv hint hclos`. Set `e` to `WithLp.prodContinuousLinearEquiv 2 ℂ H H'`. Set `gr : D →ₗ[ℂ] WithLp 2 (H × H')` to `e.symm.toLinearEquiv.toLinearMap ∘ₗ (D.subtype.prod A)`. Establish `hgr : ∀ x : D, gr x = WithLp.toLp 2 ((x : H), A x)` using `fun x => rfl`. Set `Γ₀ : Submodule ℂ (WithLp 2 (H × H'))` to `LinearMap.range gr`.

Establish `hgrΓ : ∀ x : D, gr x ∈ Γ₀.topologicalClosure` using `fun x => Γ₀.le_topologicalClosure (LinearMap.mem_range_self gr x)`. Set `U : G → (WithLp 2 (H × H') →L[ℂ] WithLp 2 (H × H'))` to `fun g => e.symm.toContinuousLinearMap ∘L ((π g).prodMap (π' g)) ∘L e.toContinuousLinearMap`. Establish `hU : ∀ g v, U g v = WithLp.toLp 2 (π g (WithLp.ofLp v).1, π' g (WithLp.ofLp v).2)` using `fun g v => rfl`. Establish `hUΓ : ∀ g, ∀ v ∈ Γ₀.topologicalClosure, U g v ∈ Γ₀.topologicalClosure`. Introduce `g`.

Establish `hle : Γ₀ ≤ (Γ₀.topologicalClosure).comap (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H'))`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `show U g (gr x) ∈ Γ₀.topologicalClosure`. Establish `: U g (gr x) = gr ⟨π g x, hinv g x x.2⟩`. Simplify using `only [hU, hgr]`.

Rewrite using `[hint g x (hinv g x x.2)]`. Rewrite using `[this]`. Conclude with `hgrΓ _`. Establish `hcl : IsClosed (((Γ₀.topologicalClosure).comap (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H')) : Submodule ℂ _) : Set (WithLp 2 (H × H')))`. Conclude with `Γ₀.isClosed_topologicalClosure.preimage (U g).continuous`.

Conclude with `fun v hv => Submodule.topologicalClosure_minimal Γ₀ hle hcl hv`. Establish `hUinner : ∀ g v w, inner ℂ (U g v) (U g w) = inner ℂ v w`. Introduce `g v w`. Simplify using `only [hU, WithLp.prod_inner_apply, unitary_inner (π g) (hπ g), unitary_inner (π' g) (hπ' g)]`. Establish `hπinv : ∀ g x, π g (π g⁻¹ x) = x`.

Introduce `g x`. Use `show (π g * π g⁻¹) x = x`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hπ'inv : ∀ g x, π' g (π' g⁻¹ x) = x`.

Introduce `g x`. Use `show (π' g * π' g⁻¹) x = x`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hUinv : ∀ g w, U g (U g⁻¹ w) = w`.

Introduce `g w`. Simplify using `only [hU, hπinv, hπ'inv, Prod.mk.eta, WithLp.toLp_ofLp]`. Establish `hPcomm : ∀ g h, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (π g h, (0 : H'))) = U g ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H'))))`. Introduce `g h`. Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises.

Conclude with `hUΓ g _ ((Γ₀.topologicalClosure).starProjection_apply_mem _)`. Introduce `w hw`. Establish `h1 : WithLp.toLp 2 (π g h, (0 : H')) = U g (WithLp.toLp 2 (h, (0 : H')))`. Simplify using `[hU]`. Rewrite using `[h1, ← hUinv g w, ← map_sub, hUinner]`.

Conclude with `Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure) _ _ (hUΓ g⁻¹ w hw)`. Set `M : H →L[ℂ] H` to `(ContinuousLinearMap.fst ℂ H H') ∘L e.toContinuousLinearMap ∘L (Γ₀.topologicalClosure).starProjection ∘L e.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.inl ℂ H H')`. Establish `hM : ∀ h, M h = (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H'))))).1` using `fun h => rfl`. Establish `hMc : ∀ g, M.comp (π g) = (π g).comp M`. Introduce `g`.

Use extensionality with `h`. Simplify using `only [ContinuousLinearMap.comp_apply, hM, hPcomm, hU, WithLp.ofLp_toLp]`. Take `⟨c₀, hc₀⟩` from `hirr M hMc`. Establish `hMx : ∀ h, M h = c₀ • h` using `fun h => by rw [hc₀]; simp`. Establish `hinj : ∀ v ∈ Γ₀.topologicalClosure, (WithLp.ofLp v).1 = 0 → v = 0`.

Introduce `v hv h1`. Establish `hv' : v ∈ closure (Γ₀ : Set (WithLp 2 (H × H')))`. Rewrite using `[← Submodule.topologicalClosure_coe]` and apply the resulting hypothesis. Take `⟨s, hs, hlim⟩` from `mem_closure_iff_seq_limit.mp hv'`. Use `choose u hu using fun n => LinearMap.mem_range.mp (hs n)`.

Establish `hc1 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).1)` using `continuous_fst.comp (WithLp.prod_continuous_ofLp ..)`. Establish `hc2 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).2)` using `continuous_snd.comp (WithLp.prod_continuous_ofLp ..)`. Establish `t1 : Tendsto (fun n => ((u n : D) : H)) atTop (𝓝 0)`. Use `(hc1.tendsto v).comp hlim` as an intermediate fact. Rewrite `this` using `[h1]`.

Use `this.congr (fun n => ?_)` and prove the remaining obligations. Simplify using `[Function.comp, ← hu n, hgr]`. Establish `t2 : Tendsto (fun n => A (u n)) atTop (𝓝 (WithLp.ofLp v).2)`. Use `((hc2.tendsto v).comp hlim).congr (fun n => ?_)` and prove the remaining obligations. Simplify using `[Function.comp, ← hu n, hgr]`.

Establish `h2` using `hclos u _ t1 t2`. Establish `h3 : WithLp.ofLp v = 0` using `Prod.ext h1 h2`. Combine the equalities or inequalities in the displayed calculation. Establish `hPx : ∀ x : D, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H'))) = c₀ • gr x`. Introduce `x`.

Establish `hmem : (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H'))) - c₀ • gr x ∈ Γ₀.topologicalClosure` using `Submodule.sub_mem _ ((Γ₀.topologicalClosure).starProjection_apply_mem _) (Submodule.smul_mem _ c₀ (hgrΓ x))`. Establish `hfst : (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H'))) - c₀ • gr x)).1 = 0`. Use `hMx x` as an intermediate fact. Rewrite `this` using `[hM]`. Simplify using `[hgr]`.

Conclude with `sub_eq_zero.mpr this`. Conclude with `sub_eq_zero.mp (hinj _ hmem hfst)`. Establish `hK : ∀ x y : D, inner ℂ (x : H) (y : H) = (starRingEnd ℂ c₀) * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y))`. Introduce `x y`. Establish `h0` using `Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure) (WithLp.toLp 2 ((x : H), (0 : H'))) (gr y) (hgrΓ y)`.

Rewrite `h0` using `[inner_sub_left, sub_eq_zero, hPx, inner_smul_left]`. Simplify using `only [hgr, WithLp.prod_inner_apply, inner_zero_left, add_zero] at h0`. Conclude with `h0`. Conclude with `alg D A _ hK`.
-/
theorem schurClosable : Formalism.IndefR.Leaf.SchurClosable := by
  intro G H H' _ _ _ _ _ _ _ π π' hπ hπ' hirr D A hD hinv hint hclos
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H H'
  let gr : D →ₗ[ℂ] WithLp 2 (H × H') := e.symm.toLinearEquiv.toLinearMap ∘ₗ (D.subtype.prod A)
  have hgr : ∀ x : D, gr x = WithLp.toLp 2 ((x : H), A x) := fun x => rfl
  let Γ₀ : Submodule ℂ (WithLp 2 (H × H')) := LinearMap.range gr
  have hgrΓ : ∀ x : D, gr x ∈ Γ₀.topologicalClosure :=
    fun x => Γ₀.le_topologicalClosure (LinearMap.mem_range_self gr x)

  let U : G → (WithLp 2 (H × H') →L[ℂ] WithLp 2 (H × H')) := fun g =>
    e.symm.toContinuousLinearMap ∘L ((π g).prodMap (π' g)) ∘L e.toContinuousLinearMap
  have hU : ∀ g v, U g v = WithLp.toLp 2 (π g (WithLp.ofLp v).1, π' g (WithLp.ofLp v).2) :=
    fun g v => rfl
  have hUΓ : ∀ g, ∀ v ∈ Γ₀.topologicalClosure, U g v ∈ Γ₀.topologicalClosure := by
    intro g
    have hle : Γ₀ ≤ (Γ₀.topologicalClosure).comap
        (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H')) := by
      rintro _ ⟨x, rfl⟩
      show U g (gr x) ∈ Γ₀.topologicalClosure
      have : U g (gr x) = gr ⟨π g x, hinv g x x.2⟩ := by
        simp only [hU, hgr]
        rw [hint g x (hinv g x x.2)]
      rw [this]
      exact hgrΓ _
    have hcl : IsClosed (((Γ₀.topologicalClosure).comap
        (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H')) : Submodule ℂ _) :
        Set (WithLp 2 (H × H'))) := by
      exact Γ₀.isClosed_topologicalClosure.preimage (U g).continuous
    exact fun v hv => Submodule.topologicalClosure_minimal Γ₀ hle hcl hv
  have hUinner : ∀ g v w, inner ℂ (U g v) (U g w) = inner ℂ v w := by
    intro g v w
    simp only [hU, WithLp.prod_inner_apply, unitary_inner (π g) (hπ g),
      unitary_inner (π' g) (hπ' g)]
  have hπinv : ∀ g x, π g (π g⁻¹ x) = x := by
    intro g x
    show (π g * π g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hπ'inv : ∀ g x, π' g (π' g⁻¹ x) = x := by
    intro g x
    show (π' g * π' g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hUinv : ∀ g w, U g (U g⁻¹ w) = w := by
    intro g w
    simp only [hU, hπinv, hπ'inv, Prod.mk.eta, WithLp.toLp_ofLp]

  have hPcomm : ∀ g h, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (π g h, (0 : H')))
      = U g ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H')))) := by
    intro g h
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hUΓ g _ ((Γ₀.topologicalClosure).starProjection_apply_mem _)
    · intro w hw
      have h1 : WithLp.toLp 2 (π g h, (0 : H')) = U g (WithLp.toLp 2 (h, (0 : H'))) := by
        simp [hU]
      rw [h1, ← hUinv g w, ← map_sub, hUinner]
      exact Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure) _ _
        (hUΓ g⁻¹ w hw)

  let M : H →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H') ∘L e.toContinuousLinearMap ∘L
      (Γ₀.topologicalClosure).starProjection ∘L e.symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.inl ℂ H H')
  have hM : ∀ h, M h =
      (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H'))))).1 :=
    fun h => rfl
  have hMc : ∀ g, M.comp (π g) = (π g).comp M := by
    intro g
    ext h
    simp only [ContinuousLinearMap.comp_apply, hM, hPcomm, hU, WithLp.ofLp_toLp]
  obtain ⟨c₀, hc₀⟩ := hirr M hMc
  have hMx : ∀ h, M h = c₀ • h := fun h => by rw [hc₀]; simp

  have hinj : ∀ v ∈ Γ₀.topologicalClosure, (WithLp.ofLp v).1 = 0 → v = 0 := by
    intro v hv h1
    have hv' : v ∈ closure (Γ₀ : Set (WithLp 2 (H × H'))) := by
      rwa [← Submodule.topologicalClosure_coe]
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hv'
    choose u hu using fun n => LinearMap.mem_range.mp (hs n)
    have hc1 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).1) :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp ..)
    have hc2 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).2) :=
      continuous_snd.comp (WithLp.prod_continuous_ofLp ..)
    have t1 : Tendsto (fun n => ((u n : D) : H)) atTop (𝓝 0) := by
      have := (hc1.tendsto v).comp hlim
      rw [h1] at this
      refine this.congr (fun n => ?_)
      simp [Function.comp, ← hu n, hgr]
    have t2 : Tendsto (fun n => A (u n)) atTop (𝓝 (WithLp.ofLp v).2) := by
      refine ((hc2.tendsto v).comp hlim).congr (fun n => ?_)
      simp [Function.comp, ← hu n, hgr]
    have h2 := hclos u _ t1 t2
    have h3 : WithLp.ofLp v = 0 := Prod.ext h1 h2
    calc v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
      _ = 0 := by rw [h3]; rfl

  have hPx : ∀ x : D, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H')))
      = c₀ • gr x := by
    intro x
    have hmem : (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H')))
        - c₀ • gr x ∈ Γ₀.topologicalClosure :=
      Submodule.sub_mem _ ((Γ₀.topologicalClosure).starProjection_apply_mem _)
        (Submodule.smul_mem _ c₀ (hgrΓ x))
    have hfst : (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection
        (WithLp.toLp 2 ((x : H), (0 : H'))) - c₀ • gr x)).1 = 0 := by
      have := hMx x
      rw [hM] at this
      simp [hgr]
      exact sub_eq_zero.mpr this
    exact sub_eq_zero.mp (hinj _ hmem hfst)
  have hK : ∀ x y : D, inner ℂ (x : H) (y : H)
      = (starRingEnd ℂ c₀) * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y)) := by
    intro x y
    have h0 := Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure)
      (WithLp.toLp 2 ((x : H), (0 : H'))) (gr y) (hgrΓ y)
    rw [inner_sub_left, sub_eq_zero, hPx, inner_smul_left] at h0
    simp only [hgr, WithLp.prod_inner_apply, inner_zero_left, add_zero] at h0
    exact h0
  exact alg D A _ hK

end PI.UnitaryGroupMassFormula.SchurClosable.Main
