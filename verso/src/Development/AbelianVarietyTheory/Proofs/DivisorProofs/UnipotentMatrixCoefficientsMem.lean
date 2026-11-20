import Mathlib

namespace GlobalTheory.CommRepBlocks

open Module Matrix

variable {G : Type} [CommGroup G] [TopologicalSpace G] (H : Set G) (S : Submodule ℂ (G → ℂ))

def BlockHyp : Prop :=
  ∀ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ),
    (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) → (∀ γ ∈ H, ρ γ = 1) →
    (∀ i j, Continuous fun s => ρ s i j) → ∀ i j, (fun s => ρ s i j) ∈ S

/- English proof (translation)
Set `b` to `Module.finBasis ℂ V`. Set `e` to `LinearMap.toMatrixAlgEquiv b`. Set `ρ : G →* Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ` to `(e.toRingEquiv.toMonoidHom).comp T`. Establish `hρ : ∀ s, ρ s = LinearMap.toMatrix b b (T s)` using `fun s => by`. Use extensionality with `i j`.

Simplify using `[ρ, e, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]`. Establish `hmem : ∀ i j, (fun s => ρ s i j) ∈ S`. Apply `hS _ ρ χ` to reduce the goal to its premises. Introduce `s`. Establish `h` using `(hnil s).map e`.

Rewrite `h` using `[map_sub, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]`. Conclude with `h`. Introduce `γ hγ`. Simplify using `[ρ, hH γ hγ]`. Introduce `i j`.

Establish `: (fun s => ρ s i j) = fun s => b.coord i (T s (b j))`. Use function extensionality and compare the values at `s`. Rewrite using `[hρ, LinearMap.toMatrix_apply]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hc _ _`. Establish `key : (fun s => φ (T s v)) = ∑ i, ∑ j, (φ (b i) * b.repr v j) • (fun s => ρ s i j)`. Use function extensionality and compare the values at `s`. Establish `h1 : ∀ i, b.repr (T s v) i = ∑ j, ρ s i j * b.repr v j` using `fun i => by`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b (T s) v, hρ]`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `congrArg φ (b.sum_repr (T s v))`. Rewrite `h2` using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul] at h2`.

Conclude with `h2.symm`. Use `_ = _ := by`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem i j)`.
-/
theorem coeff_mem_of_scalar_add_nilpotent (hS : BlockHyp H S) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (T : G →* Module.End ℂ V) (χ : G → ℂ)
    (hnil : ∀ s, IsNilpotent (T s - algebraMap ℂ (Module.End ℂ V) (χ s)))
    (hH : ∀ γ ∈ H, T γ = 1)
    (hc : ∀ (φ : Module.Dual ℂ V) v, Continuous fun s => φ (T s v))
    (φ : Module.Dual ℂ V) (v : V) : (fun s => φ (T s v)) ∈ S := by
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  let ρ : G →* Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
    (e.toRingEquiv.toMonoidHom).comp T
  have hρ : ∀ s, ρ s = LinearMap.toMatrix b b (T s) := fun s => by
    ext i j
    simp [ρ, e, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hmem : ∀ i j, (fun s => ρ s i j) ∈ S := by
    apply hS _ ρ χ
    · intro s
      have h := (hnil s).map e
      rw [map_sub, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one] at h
      exact h
    · intro γ hγ
      simp [ρ, hH γ hγ]
    · intro i j
      have : (fun s => ρ s i j) = fun s => b.coord i (T s (b j)) := by
        funext s; rw [hρ, LinearMap.toMatrix_apply]; rfl
      rw [this]; exact hc _ _
  have key : (fun s => φ (T s v)) = ∑ i, ∑ j, (φ (b i) * b.repr v j) • (fun s => ρ s i j) := by
    funext s
    have h1 : ∀ i, b.repr (T s v) i = ∑ j, ρ s i j * b.repr v j := fun i => by
      rw [← LinearMap.toMatrix_mulVec_repr b b (T s) v, hρ]; rfl
    calc φ (T s v) = ∑ i, b.repr (T s v) i * φ (b i) := by
          have h2 := congrArg φ (b.sum_repr (T s v))
          rw [map_sum] at h2
          simp only [map_smul, smul_eq_mul] at h2
          exact h2.symm
      _ = _ := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem i j)

/- English proof (translation)
Establish `hcomm' : ∀ s t, Commute (T s) (T t)` using `fun s t => by show T s * T t = T t * T s`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Establish `hcomm : Pairwise fun s t => Commute (T s) (T t)` using `fun s t _ => hcomm' s t`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute (fun s => T s) hcomm (fun s => Module.End.iSup_maxGenEigenspace_eq_top _)`. Establish `hv : v ∈ ⨆ χ : G → ℂ, ⨅ s, (T s).maxGenEigenspace (χ s)` using `by rw [htop]; trivial`.

Use `Submodule.iSup_induction _ (motive := fun v => ∀ φ : Module.Dual ℂ V, (fun s => φ (T s v)) ∈ S) hv ?_ ?_ ?_ φ` and prove the remaining obligations. Introduce `χ w hw φ`. Set `W` to `⨅ s, (T s).maxGenEigenspace (χ s)`. Establish `hmaps : ∀ s, Set.MapsTo (T s) W W` using `fun s x hx => by`. Simplify using `only [W, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢`.

Introduce `t`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm' t s) (χ t) (hx t)`. Set `T' : G →* Module.End ℂ W` to `{ toFun := fun s => (T s).restrict (hmaps s) map_one' := by ext x; simp map_mul' := by intro s t; ext x; simp only [map_mul, Module.End.mul_apply]; rfl }`. Establish `hT' : ∀ s (x : W), ((T' s x : W) : V) = T s x` using `fun s x => rfl`. Establish `hnil : ∀ s, IsNilpotent (T' s - algebraMap ℂ (Module.End ℂ W) (χ s))`.

Introduce `s`. Establish `hle : W ≤ (T s).maxGenEigenspace (χ s)` using `iInf_le _ s`. Establish `h0` using `(T s).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ s)`. Establish `hm : Set.MapsTo (T s - algebraMap ℂ (Module.End ℂ V) (χ s)) W W` using `fun x hx => by`. Use `hmaps s hx` as an intermediate fact.

Simplify using `only [SetLike.mem_coe] at this hx ⊢`. Simplify using `only [LinearMap.sub_apply, Module.algebraMap_end_apply]`. Conclude with `W.sub_mem this (W.smul_mem _ hx)`. Establish `h1` using `Module.End.isNilpotent_restrict_of_le (hp := hm) hle h0`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `only [LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_smul, hT']`. Use `show _ = (T s - algebraMap ℂ (Module.End ℂ V) (χ s)) x`. Simplify using the standard rewrite rules. Establish `hwS` using `coeff_mem_of_scalar_add_nilpotent H S hS T' χ hnil (fun γ hγ => by ext x; simp [hT', hH γ hγ]) (fun φ' x => by`.

Take `⟨ψ, hψ⟩` from `LinearMap.exists_extend φ'`. Establish `: (fun s => φ' (T' s x)) = fun s => ψ (T s x)`. Use function extensionality and compare the values at `s`. Rewrite using `[← hψ]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hc ψ x)`. Use the proof step `(φ.comp W.subtype) ⟨w, hw⟩`. Conclude with `hwS`. Introduce `φ`.

Establish `: (fun s => φ (T s 0)) = 0` using `by funext s; simp`. Rewrite using `[this]`. Conclude with `S.zero_mem`. Introduce `x y hx hy φ`. Establish `: (fun s => φ (T s (x + y))) = (fun s => φ (T s x)) + fun s => φ (T s y)`.

Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `S.add_mem (hx φ) (hy φ)`.
-/
theorem coeff_mem_general (hS : BlockHyp H S) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (T : G →* Module.End ℂ V)
    (hH : ∀ γ ∈ H, T γ = 1)
    (hc : ∀ (φ : Module.Dual ℂ V) v, Continuous fun s => φ (T s v))
    (φ : Module.Dual ℂ V) (v : V) : (fun s => φ (T s v)) ∈ S := by
  have hcomm' : ∀ s t, Commute (T s) (T t) := fun s t => by
    show T s * T t = T t * T s
    rw [← map_mul, ← map_mul, mul_comm]
  have hcomm : Pairwise fun s t => Commute (T s) (T t) := fun s t _ => hcomm' s t
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun s => T s) hcomm (fun s => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hv : v ∈ ⨆ χ : G → ℂ, ⨅ s, (T s).maxGenEigenspace (χ s) := by rw [htop]; trivial
  refine Submodule.iSup_induction _ (motive := fun v => ∀ φ : Module.Dual ℂ V, (fun s => φ (T s v)) ∈ S)
    hv ?_ ?_ ?_ φ
  · intro χ w hw φ
    let W := ⨅ s, (T s).maxGenEigenspace (χ s)
    have hmaps : ∀ s, Set.MapsTo (T s) W W := fun s x hx => by
      simp only [W, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
      intro t
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm' t s) (χ t) (hx t)
    let T' : G →* Module.End ℂ W :=
      { toFun := fun s => (T s).restrict (hmaps s)
        map_one' := by ext x; simp
        map_mul' := by intro s t; ext x; simp only [map_mul, Module.End.mul_apply]; rfl }
    have hT' : ∀ s (x : W), ((T' s x : W) : V) = T s x := fun s x => rfl
    have hnil : ∀ s, IsNilpotent (T' s - algebraMap ℂ (Module.End ℂ W) (χ s)) := by
      intro s
      have hle : W ≤ (T s).maxGenEigenspace (χ s) := iInf_le _ s
      have h0 := (T s).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ s)
      have hm : Set.MapsTo (T s - algebraMap ℂ (Module.End ℂ V) (χ s)) W W := fun x hx => by
        have := hmaps s hx
        simp only [SetLike.mem_coe] at this hx ⊢
        simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
        exact W.sub_mem this (W.smul_mem _ hx)
      have h1 := Module.End.isNilpotent_restrict_of_le (hp := hm) hle h0
      convert h1 using 1
      ext x
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_smul, hT']
      show _ = (T s - algebraMap ℂ (Module.End ℂ V) (χ s)) x
      simp
    have hwS := coeff_mem_of_scalar_add_nilpotent H S hS T' χ hnil
      (fun γ hγ => by ext x; simp [hT', hH γ hγ])
      (fun φ' x => by
        obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ'
        have : (fun s => φ' (T' s x)) = fun s => ψ (T s x) := by
          funext s; rw [← hψ]; rfl
        rw [this]; exact hc ψ x)
      (φ.comp W.subtype) ⟨w, hw⟩
    exact hwS
  · intro φ
    have : (fun s => φ (T s 0)) = 0 := by funext s; simp
    rw [this]; exact S.zero_mem
  · intro x y hx hy φ
    have : (fun s => φ (T s (x + y))) = (fun s => φ (T s x)) + fun s => φ (T s y) := by
      funext s; simp
    rw [this]; exact S.add_mem (hx φ) (hy φ)

/- English proof (translation)
Introduce `G _ _ H S hS d ρ hH hρc i j`. Set `T : G →* Module.End ℂ (Fin d → ℂ)` to `((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toRingEquiv.toMonoidHom).comp ρ`. Establish `hT : ∀ s v, T s v = ρ s *ᵥ v` using `fun s v => rfl`. Establish `hmain` using `coeff_mem_general H S hS T (fun γ hγ => LinearMap.ext fun v => by simp [hT, hH γ hγ]) (fun φ v => by`. Establish `hcv : Continuous fun s => ρ s *ᵥ v` using `continuous_pi fun k => by`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `continuous_finset_sum _ fun l _ => (hρc k l).mul continuous_const`. Simplify using `only [hT]`. Conclude with `(LinearMap.continuous_of_finiteDimensional φ).comp hcv)`. Use the proof step `(LinearMap.proj i) (Pi.single j 1)`.

Establish `: (fun s => ρ s i j) = fun s => (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) (T s (Pi.single j 1))`. Use function extensionality and compare the values at `s`. Simplify using `[hT, Matrix.mulVec_single_one]`. Rewrite using `[this]`. Conclude with `hmain`.
-/
theorem coeff_mem_of_blocks : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G)
    (S : Submodule ℂ (G → ℂ)), (∀ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ),
      (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) → (∀ γ ∈ H, ρ γ = 1) →
      (∀ i j, Continuous fun s => ρ s i j) → ∀ i j, (fun s => ρ s i j) ∈ S) →
    ∀ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), (∀ γ ∈ H, ρ γ = 1) →
      (∀ i j, Continuous fun s => ρ s i j) → ∀ i j, (fun s => ρ s i j) ∈ S := by
  intro G _ _ H S hS d ρ hH hρc i j
  let T : G →* Module.End ℂ (Fin d → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toRingEquiv.toMonoidHom).comp ρ
  have hT : ∀ s v, T s v = ρ s *ᵥ v := fun s v => rfl
  have hmain := coeff_mem_general H S hS T
    (fun γ hγ => LinearMap.ext fun v => by simp [hT, hH γ hγ])
    (fun φ v => by
      have hcv : Continuous fun s => ρ s *ᵥ v :=
        continuous_pi fun k => by
          simp only [Matrix.mulVec, dotProduct]
          exact continuous_finset_sum _ fun l _ => (hρc k l).mul continuous_const
      simp only [hT]
      exact (LinearMap.continuous_of_finiteDimensional φ).comp hcv)
    (LinearMap.proj i) (Pi.single j 1)
  have : (fun s => ρ s i j) = fun s => (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) (T s (Pi.single j 1)) := by
    funext s
    simp [hT, Matrix.mulVec_single_one]
  rw [this]; exact hmain

end GlobalTheory.CommRepBlocks
