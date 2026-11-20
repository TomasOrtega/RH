import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

namespace UpperTheory.V.Lit.Dr

open groupCohomology

/- English proof (translation)
Introduce `Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift`. Use `choose y hy using fun i => hsurj (w i)`. Establish `hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0`. Introduce `i γ`. Rewrite using `[map_sub, hπ, hy, hw, sub_self]`.

Use `choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)`. Establish `hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM)`. Introduce `i`. Rewrite using `[groupCohomology.mem_cocycles₁_iff]`. Introduce `g h`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[Rep.of_ρ]`. Express the relevant statement in the definitionally equal form `ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)`. Rewrite using `[map_add, hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws.

Set `v : Fin n → groupCohomology (Rep.of ρM) 1` to `fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩`. Establish `hli : LinearIndependent ℂ v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hsum : (∑ i, g i • v i) = (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM)))`.

Simplify using `only [map_sum, map_smul, v]`. Rewrite `hg` using `[hsum, groupCohomology.H1π_eq_zero_iff]`. Take `⟨m, hm⟩` from `hg`. Establish `key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i`. Rewrite using `[Submodule.coe_sum]`.

Both sides reduce to the same expression. Establish `hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ`. Introduce `γ`. Use `congrFun hm γ` as an intermediate fact. Rewrite `this` using `[groupCohomology.d₀₁_hom_apply, Rep.of_ρ]`.

Rewrite using `[this]`. Conclude with `(congrFun key γ).trans (Finset.sum_apply _ _ _)`. Establish `hzero` using `hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩`. Introduce `i`. Rewrite using `[hzero]`.

Both sides reduce to the same expression. Introduce `γ`. Establish `h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i)`. Rewrite using `[← map_sub, hm', map_sum]`. Simplify using `only [map_smul, hφ]`.

Rewrite `h1` using `[hι]`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib] at h1`. Rewrite `h1` using `[sub_eq_iff_eq_add]`.

Rewrite using `[h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]`. Simplify using `only [map_smul, hy]`. Use `hli.cardinal_le_rank` as an intermediate fact.

Simplify using `using this`.
-/
theorem shiftOne : ShiftOne := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift
  classical
  choose y hy using fun i => hsurj (w i)
  have hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0 := by
    intro i γ
    rw [map_sub, hπ, hy, hw, sub_self]
  choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)
  have hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM) := by
    intro i
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [Rep.of_ρ]
    change ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)
    rw [map_add, hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]
    abel
  let v : Fin n → groupCohomology (Rep.of ρM) 1 :=
    fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i, g i • v i) =
        (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) := by
      simp only [map_sum, map_smul, v]
    rw [hsum, groupCohomology.H1π_eq_zero_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i := by
      rw [Submodule.coe_sum]
      rfl
    have hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ := by
      intro γ
      have := congrFun hm γ
      rw [groupCohomology.d₀₁_hom_apply, Rep.of_ρ] at this
      rw [this]
      exact (congrFun key γ).trans (Finset.sum_apply _ _ _)
    have hzero := hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩
    · intro i
      rw [hzero]
      rfl
    · intro γ
      have h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i) := by
        rw [← map_sub, hm', map_sum]
        simp only [map_smul, hφ]
      rw [hι] at h1
      rw [map_sub, map_sum]
      simp only [map_smul]
      simp only [smul_sub, Finset.sum_sub_distrib] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    · rw [map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]
      simp only [map_smul, hy]
  have := hli.cardinal_le_rank
  simpa using this

end UpperTheory.V.Lit.Dr
