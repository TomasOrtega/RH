import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `e : D' = D.restrictScalars Q`. Use extensionality with `x`. Conclude with `h x`. Establish `h1 : finrank Q ↥D' = finrank Q E * finrank E ↥D`. Rewrite using `[Module.finrank_mul_finrank, e]`.

Both sides reduce to the same expression. Establish `h2 : finrank Q V = finrank Q E * finrank E V` using `(Module.finrank_mul_finrank Q E V).symm`. Establish `hp : 0 < finrank Q E` using `Module.finrank_pos`. Rewrite using `[h1, h2, mul_left_comm]`. Conclude with `Nat.mul_right_inj hp.ne'`.
-/
private theorem finrank_key {Q E M V : Type} [Field Q] [Field E] [Algebra Q E] [FiniteDimensional Q E]
    [AddCommGroup M] [Module E M] [Module Q M] [IsScalarTower Q E M]
    [AddCommGroup V] [Module E V] [Module Q V] [IsScalarTower Q E V]
    (D : Submodule E M) (D' : Submodule Q M) (h : ∀ x, x ∈ D' ↔ x ∈ D) (n : ℕ) :
    finrank Q ↥D' = n * finrank Q V ↔ finrank E ↥D = n * finrank E V := by
  have e : D' = D.restrictScalars Q := by
    ext x
    exact h x
  have h1 : finrank Q ↥D' = finrank Q E * finrank E ↥D := by
    rw [Module.finrank_mul_finrank, e]
    rfl
  have h2 : finrank Q V = finrank Q E * finrank E V := (Module.finrank_mul_finrank Q E V).symm
  have hp : 0 < finrank Q E := Module.finrank_pos
  rw [h1, h2, mul_left_comm]
  exact Nat.mul_right_inj hp.ne'

/- English proof (translation)
Introduce `l _ K E _ _ _ V _ _ _ _ _ _ _ _ _ ρ`. Establish `hB : ∀ g x, actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVB ((PP l).PD K) ρ g x`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `tmul v b => rfl`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hD : ∀ g x, actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVdR ((PP l).PD K) ρ g x`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b => rfl`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hC : ∀ g x, actC (GK K).subtype ρ g x = actVB ((PP l).PD K) ρ g x`. Introduce `g x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b`. Express the relevant statement in the definitionally equal form `ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQ (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB g b`. Rewrite using `[(PP l).PD_actB]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `finrank_key (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _` and prove the remaining obligations. Simplify using `only [Formalism.WeaklyAdmissibleFiltrations.Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hB]`. Use `finrank_key (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _` and prove the remaining obligations.

Simplify using `only [Formalism.WeaklyAdmissibleFiltrations.DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hD]`. Use extensionality with `c`. Express the relevant statement in the definitionally equal form `(c ∈ ReciprocityTheory.Gal.Z1 ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC (GK K).subtype ρ g x - x) ↔ (c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) ρ g x - x)`. Simplify using `only [hC]`. Conclude with `Iff.rfl`.
-/
theorem UpperTheory.V.Loc.isCrField :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E ↥(GK K) V), (Crys K ρ ↔ IsCrys ((PP l).PD K) ρ) ∧ (DeRham K ρ ↔ IsDR ((PP l).PD K) ρ) ∧ UpperTheory.V.Loc.finiteCocycles (GK K).subtype ρ = Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) ρ := by
  intro l _ K E _ _ _ V _ _ _ _ _ _ _ _ _ ρ
  have hB : ∀ g x, actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hD : ∀ g x, actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVdR ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hC : ∀ g x, actC (GK K).subtype ρ g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQ (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB g b
      rw [(PP l).PD_actB]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨?_, ?_, ?_⟩
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hB]
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hD]
  · ext c
    change (c ∈ ReciprocityTheory.Gal.Z1 ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC (GK K).subtype ρ g x - x) ↔
      (c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) ρ g x - x)
    simp only [hC]
    exact Iff.rfl
