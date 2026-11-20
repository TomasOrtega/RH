import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.InvBaseChange

open TensorProduct

namespace PI.CoefExt

section

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W W₂ : Type} [AddCommGroup W] [Module K W]
  [AddCommGroup W₂] [Module K W₂]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a w`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Consider the case `add x y hx hy`. Simplify using `only [map_add, hx, hy]`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem coord_baseChange {ι : Type} [DecidableEq ι] (b : Module.Basis ι K L) (f : W →ₗ[K] W₂) (x : L ⊗[K] W) :
    equivFinsuppOfBasisLeft b (f.baseChange L x)
      = Finsupp.mapRange f f.map_zero (equivFinsuppOfBasisLeft b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
    ext i
    simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i
    simp

end

/- English proof (translation)
Introduce `LL LL' _ _ _ W _ _ G T`. Use `set V : Submodule LL W := ⨅ g, LinearMap.ker (T g - LinearMap.id) with hV`. Establish `memV : ∀ w, w ∈ V ↔ ∀ g, T g w = w`. Introduce `w`. Simplify using `[hV, Submodule.mem_iInf, sub_eq_zero]`.

Take `⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι LL LL')` from `⟨_, ⟨Module.Free.chooseBasis LL LL'⟩⟩`. Establish `hinj : Function.Injective (V.subtype.baseChange LL')`. Introduce `z₁ z₂ h`. Establish `h'` using `congrArg (equivFinsuppOfBasisLeft b) h`. Rewrite `h'` using `[coord_baseChange b V.subtype z₁, coord_baseChange b V.subtype z₂]`.

Apply `(equivFinsuppOfBasisLeft b).injective` to reduce the goal to its premises. Use extensionality with `i`. Use `congrArg (fun c => c i) h'` as an intermediate fact. Simplify using `using this`. Establish `hrange : (⨅ g, LinearMap.ker ((T g).baseChange LL' - LinearMap.id) : Submodule LL' (LL' ⊗[LL] W)) = LinearMap.range (V.subtype.baseChange LL')`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hfix : ∀ g, (T g).baseChange LL' x = x`. Introduce `g`. Use `(Submodule.mem_iInf _).1 hx g` as an intermediate fact.

Simplify `this` using `[sub_eq_zero]`. Establish `hc : ∀ i, equivFinsuppOfBasisLeft b x i ∈ V`. Introduce `i`. Rewrite using `[memV]`. Introduce `g`.

Use `congrArg (fun c => c i) (coord_baseChange b (T g) x)` as an intermediate fact. Simplify using `only [hfix g, Finsupp.mapRange_apply] at this`. Conclude with `this.symm`. Rewrite using `[← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]`. Unfold `Finsupp.sum`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `LinearMap.mem_range.2 ⟨b i ⊗ₜ ⟨_, hc i⟩, by simp⟩`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Submodule.mem_iInf]`. Introduce `g`.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v`. Establish `hv` using `(memV v).1 v.2 g`.

Simplify using `[hv]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]`.
-/
theorem invBaseChange : InvBaseChange := by
  intro LL LL' _ _ _ W _ _ G T
  classical
  set V : Submodule LL W := ⨅ g, LinearMap.ker (T g - LinearMap.id) with hV
  have memV : ∀ w, w ∈ V ↔ ∀ g, T g w = w := by
    intro w
    simp [hV, Submodule.mem_iInf, sub_eq_zero]
  obtain ⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι LL LL') :=
    ⟨_, ⟨Module.Free.chooseBasis LL LL'⟩⟩
  have hinj : Function.Injective (V.subtype.baseChange LL') := by
    intro z₁ z₂ h
    have h' := congrArg (equivFinsuppOfBasisLeft b) h
    rw [coord_baseChange b V.subtype z₁,
      coord_baseChange b V.subtype z₂] at h'
    apply (equivFinsuppOfBasisLeft b).injective
    ext i
    have := congrArg (fun c => c i) h'
    simpa using this
  have hrange : (⨅ g, LinearMap.ker ((T g).baseChange LL' - LinearMap.id) :
      Submodule LL' (LL' ⊗[LL] W)) = LinearMap.range (V.subtype.baseChange LL') := by
    apply le_antisymm
    · intro x hx
      have hfix : ∀ g, (T g).baseChange LL' x = x := by
        intro g
        have := (Submodule.mem_iInf _).1 hx g
        simpa [sub_eq_zero] using this
      have hc : ∀ i, equivFinsuppOfBasisLeft b x i ∈ V := by
        intro i
        rw [memV]
        intro g
        have := congrArg (fun c => c i) (coord_baseChange b (T g) x)
        simp only [hfix g, Finsupp.mapRange_apply] at this
        exact this.symm
      rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]
      unfold Finsupp.sum
      refine Submodule.sum_mem _ fun i _ => ?_
      exact LinearMap.mem_range.2 ⟨b i ⊗ₜ ⟨_, hc i⟩, by simp⟩
    · rintro _ ⟨z, rfl⟩
      rw [Submodule.mem_iInf]
      intro g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
        have hv := (memV v).1 v.2 g
        simp [hv]
      | add x y hx hy => simp only [map_add, hx, hy]
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end PI.CoefExt
