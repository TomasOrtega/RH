import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ n _ _ K r ρ hρ hfin`. Set `F : ↥(GK K) → (n → n → Om l)` to `fun g i j => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)`. Establish `hF : Continuous F` using `continuous_pi fun i => continuous_pi fun j => hρ.cont i j`. Set `cm : GL n ↥(MaximalUnramifiedExtension l) → (n → n → Om l)` to `fun M i j => (((M : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)`. Establish `hcm : Function.Injective cm`.

Introduce `M M' h`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Establish `hone : ∀ i j, (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) = (1 : Matrix n n (Om l)) i j`. Introduce `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Set `T : Set (n → n → Om l)` to `cm '' (ρ '' (IK K : Set ↥(GK K)) \ {1})`. Establish `hT : T.Finite` using `(hfin.sdiff).image cm`. Set `V : Set (n → n → Om l)` to `{x | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} ∩ Tᶜ`. Establish `hV : IsOpen V`.

Use `IsOpen.inter ?_ hT.isClosed.isOpen_compl` and prove the remaining obligations. Establish `: {x : n → n → Om l | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} = ⋂ i, ⋂ j, {x : n → n → Om l | ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1}`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const`. Establish `h1V : F 1 ∈ V`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Use `show ‖(((ρ 1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1`. Rewrite using `[map_one, Units.val_one, hone, sub_self, norm_zero]`.

Conclude with `one_pos`. Introduce and unpack `⟨M, hM, hMF⟩`. Establish `hM1 : M = ρ 1` using `hcm hMF`. Conclude with `hM.2 (by rw [hM1, map_one]; rfl)`. Establish `hU : IsOpen (F ⁻¹' V)` using `hV.preimage hF`.

Take `⟨U', hU', hUe'⟩` from `isOpen_induced_iff.1 hU`. Establish `h1' : (1 : GQ l) ∈ U'`. Establish `: (1 : ↥(GK K)) ∈ Subtype.val ⁻¹' U'`. Rewrite using `[hUe']`. Conclude with `h1V`.

Conclude with `this`. Take `⟨E, hE, hEU⟩` from `(krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')`. Use `⟨supExt K ⟨E, hE⟩, le_sup_left, ?_⟩` and prove the remaining obligations. Establish `key : ∀ g : ↥(GK (supExt K ⟨E, hE⟩)), F ⟨g, GK_le (K` using `K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ ∈ V := by`. Introduce `g`.

Establish `: (⟨g, GK_le (K` using `K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ Subtype.val ⁻¹' U' := hEU (GK_le (K := ⟨E, hE⟩) (K' := supExt K ⟨E, hE⟩) le_sup_right g.2)`. Rewrite `this` using `[hUe']`. Conclude with `this`. Use `⟨fun g hg => ?_, fun g i j => (key g).1 i j⟩` and prove the remaining obligations. Establish `hin : (⟨g, GK_le (K` using `K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ IK K := by`.

Establish `hmap : (IK (supExt K ⟨E, hE⟩)).map (Subgroup.inclusion (GK_le (K` using `K) (K' := supExt K ⟨E, hE⟩) le_sup_left)) ≤ IK K := by`. Unfold `IK`. Rewrite using `[MonoidHom.map_closure]`. Apply `Subgroup.closure_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`.

Introduce `x hx`. Conclude with `hσ x hx`. Conclude with `hmap ⟨g, hg, rfl⟩`. Assume the negation of the conclusion as `hne`. Conclude with `(key g).2 ⟨_, ⟨⟨_, hin, rfl⟩, hne⟩, rfl⟩`.
-/
theorem unr_of_finite_inertia : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite →
    ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1), (∀ g ∈ IK K', ρ ⟨g, GK_le hK g.2⟩ = 1) ∧
      ∀ (g : ↥(GK K')) i j, ‖(((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) -
        (1 : Matrix n n (Om l)) i j‖ < 1 := by
  intro l _ n _ _ K r ρ hρ hfin
  let F : ↥(GK K) → (n → n → Om l) := fun g i j => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hF : Continuous F := continuous_pi fun i => continuous_pi fun j => hρ.cont i j
  let cm : GL n ↥(MaximalUnramifiedExtension l) → (n → n → Om l) := fun M i j => (((M : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hcm : Function.Injective cm := by
    intro M M' h
    ext i j
    exact congrFun (congrFun h i) j
  have hone : ∀ i j, (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) = (1 : Matrix n n (Om l)) i j := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  let T : Set (n → n → Om l) := cm '' (ρ '' (IK K : Set ↥(GK K)) \ {1})
  have hT : T.Finite := (hfin.sdiff).image cm
  let V : Set (n → n → Om l) := {x | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} ∩ Tᶜ
  have hV : IsOpen V := by
    refine IsOpen.inter ?_ hT.isClosed.isOpen_compl
    have : {x : n → n → Om l | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} =
        ⋂ i, ⋂ j, {x : n → n → Om l | ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} := by
      ext
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const
  have h1V : F 1 ∈ V := by
    refine ⟨fun i j => ?_, ?_⟩
    · show ‖(((ρ 1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1
      rw [map_one, Units.val_one, hone, sub_self, norm_zero]
      exact one_pos
    · rintro ⟨M, hM, hMF⟩
      have hM1 : M = ρ 1 := hcm hMF
      exact hM.2 (by rw [hM1, map_one]; rfl)
  have hU : IsOpen (F ⁻¹' V) := hV.preimage hF
  obtain ⟨U', hU', hUe'⟩ := isOpen_induced_iff.1 hU
  have h1' : (1 : GQ l) ∈ U' := by
    have : (1 : ↥(GK K)) ∈ Subtype.val ⁻¹' U' := by
      rw [hUe']
      exact h1V
    exact this
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')
  refine ⟨supExt K ⟨E, hE⟩, le_sup_left, ?_⟩
  have key : ∀ g : ↥(GK (supExt K ⟨E, hE⟩)),
      F ⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ ∈ V := by
    intro g
    have : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ Subtype.val ⁻¹' U' :=
      hEU (GK_le (K := ⟨E, hE⟩) (K' := supExt K ⟨E, hE⟩) le_sup_right g.2)
    rw [hUe'] at this
    exact this
  refine ⟨fun g hg => ?_, fun g i j => (key g).1 i j⟩
  have hin : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ IK K := by
    have hmap : (IK (supExt K ⟨E, hE⟩)).map (Subgroup.inclusion (GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left)) ≤
        IK K := by
      unfold IK
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      intro x hx
      exact hσ x hx
    exact hmap ⟨g, hg, rfl⟩
  by_contra hne
  exact (key g).2 ⟨_, ⟨⟨_, hin, rfl⟩, hne⟩, rfl⟩

end GlobalTheory.PMon
