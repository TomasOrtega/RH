import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use extensionality with `h`. Simplify using `[MonoidAlgebra.single_mul_single, Finsupp.single_apply]`.
-/
private theorem coeffSum (Λ G : Type) [CommRing Λ] [Group G] [Fintype G] (x : MonoidAlgebra Λ G) :
    ∑ g : G, (MonoidAlgebra.single g (1:Λ)) * MonoidAlgebra.single (1:G) (((MonoidAlgebra.single g⁻¹ (1:Λ)) * x).coeff 1) = x := by
  classical
  ext h
  simp [MonoidAlgebra.single_mul_single, Finsupp.single_apply]

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def.1 h`. Set `e : MonoidAlgebra Λ G →+ MonoidAlgebra Λ G` to `{ toFun := fun x => MonoidAlgebra.single (1:G) (x.coeff 1) map_zero' := by simp map_add' := by intro x y; simp [MonoidAlgebra.single_add] }`. Use `⟨(Finsupp.linearCombination (MonoidAlgebra Λ G) (id : N → N)).toAddMonoidHom.comp ((Finsupp.mapRange.addMonoidHom e).comp s.toAddMonoidHom), fun m => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hs m]`. Simplify using `only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← map_smul, ← map_sum]`.

Use `congr 1`. Use `ext1 n`. Rewrite using `[Finsupp.finset_sum_apply]`. Simplify using `only [map_smul, Finsupp.smul_apply, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Conclude with `coeffSum Λ G (s m n)`.
-/
private theorem higman (Λ G N : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup N]
    [Module (MonoidAlgebra Λ G) N] (h : Module.Projective (MonoidAlgebra Λ G) N) :
    ∃ φ : N →+ N, ∀ m, ∑ g : G, MonoidAlgebra.single g (1:Λ) • φ (MonoidAlgebra.single g⁻¹ (1:Λ) • m) = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.1 h
  let e : MonoidAlgebra Λ G →+ MonoidAlgebra Λ G :=
    { toFun := fun x => MonoidAlgebra.single (1:G) (x.coeff 1)
      map_zero' := by simp
      map_add' := by intro x y; simp [MonoidAlgebra.single_add] }
  refine ⟨(Finsupp.linearCombination (MonoidAlgebra Λ G) (id : N → N)).toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom e).comp s.toAddMonoidHom), fun m => ?_⟩
  conv_rhs => rw [← hs m]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← map_smul, ← map_sum]
  congr 1
  ext1 n
  rw [Finsupp.finset_sum_apply]
  simp only [map_smul, Finsupp.smul_apply, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact coeffSum Λ G (s m n)

/- English proof (translation)
Introduce `Λ G M _ _ _ _ _ ρ hP`. Take `⟨φ₀, hφ₀⟩` from `higman Λ G ρ.asModule hP`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : M →+ M, ∀ m, ∑ g : G, ρ g (φ (ρ g⁻¹ m)) = m := by`. Use `⟨ρ.asModuleEquiv.toLinearMap.toAddMonoidHom.comp (φ₀.comp ρ.asModuleEquiv.symm.toLinearMap.toAddMonoidHom), fun m => ?_⟩` and prove the remaining obligations. Use `congrArg ρ.asModuleEquiv (hφ₀ (ρ.asModuleEquiv.symm m))` as an intermediate fact.

Rewrite `this` using `[map_sum, LinearEquiv.apply_symm_apply]`. Rewrite using `[← this]`. Use `conv_lhs => rw [this]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `[Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_symm_map_rho]`.

Both sides reduce to the same expression. Use `⟨fun m hm => ⟨φ m, ?_⟩, fun S hS m hm => ?_⟩` and prove the remaining obligations. Simplify `hφ m` using `only [hm]`. Use `set I : Submodule Λ M := ⨆ g ∈ S, LinearMap.range (ρ g - 1) with hI`. Establish `key : ∀ g : G, ∀ x, ρ g x - x ∈ I`.

Introduce `g`. Establish `hg : g ∈ Subgroup.closure S` using `hS ▸ Subgroup.mem_top g`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`. Introduce `x`.

Conclude with `Submodule.mem_iSup_of_mem g (Submodule.mem_iSup_of_mem hg ⟨x, rfl⟩)`. Consider the case `one => intro x`. Simplify using the standard rewrite rules. Consider the case `mul a b _ _ ha hb`. Introduce `x`.

Use `I.add_mem (ha (ρ b x)) (hb x)` as an intermediate fact. Simplify using `using this`. Consider the case `inv a _ ha`. Introduce `x`. Use `I.neg_mem (ha (ρ a⁻¹ x))` as an intermediate fact.

Simplify using `using this`. Establish `h0 : ∑ g : G, φ (ρ g⁻¹ m) = 0`. Rewrite using `[← map_sum, ← map_zero φ, ← hm]`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)`.

Establish `: m = ∑ g : G, (ρ g (φ (ρ g⁻¹ m)) - φ (ρ g⁻¹ m))`. Rewrite using `[Finset.sum_sub_distrib, hφ, h0, sub_zero]`. Rewrite using `[this]`. Conclude with `I.sum_mem fun g _ => key g _`.
-/
theorem UpperTheory.V.Pa.Lev.projNorm :
    ∀ (Λ G M : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M), Module.Projective (MonoidAlgebra Λ G) ρ.asModule → (∀ m, (∀ g, ρ g m = m) → ∃ m', ∑ g, ρ g m' = m) ∧ ∀ S : Set G, Subgroup.closure S = ⊤ → ∀ m, ∑ g, ρ g m = 0 → m ∈ ⨆ g ∈ S, LinearMap.range (ρ g - 1) := by
  intro Λ G M _ _ _ _ _ ρ hP
  obtain ⟨φ₀, hφ₀⟩ := higman Λ G ρ.asModule hP
  obtain ⟨φ, hφ⟩ : ∃ φ : M →+ M, ∀ m, ∑ g : G, ρ g (φ (ρ g⁻¹ m)) = m := by
    refine ⟨ρ.asModuleEquiv.toLinearMap.toAddMonoidHom.comp (φ₀.comp ρ.asModuleEquiv.symm.toLinearMap.toAddMonoidHom), fun m => ?_⟩
    have := congrArg ρ.asModuleEquiv (hφ₀ (ρ.asModuleEquiv.symm m))
    rw [map_sum, LinearEquiv.apply_symm_apply] at this
    rw [← this]
    conv_lhs => rw [this]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_symm_map_rho]
    rfl
  refine ⟨fun m hm => ⟨φ m, ?_⟩, fun S hS m hm => ?_⟩
  · simpa only [hm] using hφ m
  · set I : Submodule Λ M := ⨆ g ∈ S, LinearMap.range (ρ g - 1) with hI
    have key : ∀ g : G, ∀ x, ρ g x - x ∈ I := by
      intro g
      have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        intro x
        exact Submodule.mem_iSup_of_mem g (Submodule.mem_iSup_of_mem hg ⟨x, rfl⟩)
      | one => intro x; simp
      | mul a b _ _ ha hb =>
        intro x
        have := I.add_mem (ha (ρ b x)) (hb x)
        simpa using this
      | inv a _ ha =>
        intro x
        have := I.neg_mem (ha (ρ a⁻¹ x))
        simpa using this
    have h0 : ∑ g : G, φ (ρ g⁻¹ m) = 0 := by
      rw [← map_sum, ← map_zero φ, ← hm]
      congr 1
      exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
    have : m = ∑ g : G, (ρ g (φ (ρ g⁻¹ m)) - φ (ρ g⁻¹ m)) := by
      rw [Finset.sum_sub_distrib, hφ, h0, sub_zero]
    rw [this]
    exact I.sum_mem fun g _ => key g _
