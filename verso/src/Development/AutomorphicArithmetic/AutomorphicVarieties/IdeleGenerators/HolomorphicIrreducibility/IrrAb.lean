import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford

open Matrix Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.U3

/- English proof (translation)
Introduce `l _ Γ _ _ _ n r hr hio H H' hH hle hab`. Establish `h0` using `hio H hH`. Establish `hne : (⊤ : Submodule (Formalism.ConjugateSelfDual.Qbar l) (Fin n → Formalism.ConjugateSelfDual.Qbar l)) ≠ ⊥` using `h0.1`. Use `haveI : Nontrivial (Fin n → Formalism.ConjugateSelfDual.Qbar l) := Submodule.nontrivial_iff (Formalism.ConjugateSelfDual.Qbar l) |>.mp ⟨_, _, hne⟩`. Establish `hn : n ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hne (Subsingleton.elim _ _)`. Use `⟨hne, fun _ _ _ => trivial, fun W _ hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Establish `hab' : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ H'.subgroupOf H` using `fun a b => Subgroup.mem_subgroupOf.mpr (hab a a.2 b b.2)`.

Use `haveI : (H'.subgroupOf H).Normal := ⟨fun x hx g => by`. Use `(H'.subgroupOf H).mul_mem (hab' g x) hx` as an intermediate fact. Simplify using `using this⟩`. Take `⟨φ, hφ1, -, hφn, M, hM⟩` from `exists_selfTwist (r.comp H.subtype) (H'.subgroupOf H) hab' (fun U hU => h0.2.2 U le_top fun g v hv => hU g trivial v hv) (fun h => hcon (h W fun g hg v hv => hW ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ v hv))`. Establish `hM' : ∀ g : H, ((φ g : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) • ((M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) = (r g : Matrix (Fin n) (Fin n) (Formali …` using `fun g => by`.

Use `hM g trivial` as an intermediate fact. Rewrite `this` using `[Matrix.mul_smul]`. Conclude with `this`. Establish `hiff : ∀ g : H, φ g = 1 ↔ (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M` using `fun g => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `hM' g` as an intermediate fact. Rewrite `this` using `[h, Units.val_one, one_smul]`. Then use the resulting hypothesis. Introduce `h`. Establish `h1` using `hM' g`.

Rewrite `h1` using `[← h]`. Use `haveI : NeZero n := ⟨hn⟩`. Establish `h2 : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) ≠ 0` using `(M * r g).ne_zero`. Conclude with `Units.ext (smul_left_injective _ h2 (h1.trans (one_smul _ _).symm))`. Establish `hcl : IsClosed (φ.ker : Set H)`.

Establish `hc : Continuous fun g : H => (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))` using `Units.continuous_val.comp (hr.comp continuous_subtype_val)`. Establish `: (φ.ker : Set H) = {g : H | (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M}` using `Set.ext fun g => hiff g`. Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)`. Use `haveI : NeZero n := ⟨hn⟩`.

Establish `hrg : φ.range ≤ rootsOfUnity n (Formalism.ConjugateSelfDual.Qbar l)`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[mem_rootsOfUnity]`. Conclude with `DFunLike.congr_fun hφn g`. Use `haveI : Finite φ.range := Finite.of_injective _ (Subgroup.inclusion_injective hrg)`.

Use `haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ`. Establish `hop : IsOpen (φ.ker : Set H)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl`. Establish `hop' : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `hH.isOpenMap_subtype_val _ hop`.

Establish `h1` using `hio _ hop'`. Take `⟨a, ha⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)))`. Establish `htop` using `(h1.2.2 (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a) le_top (by`. Introduce and unpack `⟨_, g, hg, rfl⟩ v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`.

Express the relevant statement in the definitionally equal form `(M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v) = a • ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, (hiff g).mp hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])).resolve_left ha`. Establish `hMa : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = a • 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Establish `: v ∈ Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `this` using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Apply `hφ1` to reduce the goal to its premises. Use `ext1 g`. Conclude with `(hiff g).mpr (by rw [hMa]; simp)`.
-/
theorem UpperTheory.V.Sd.irrAb :
    UpperTheory.V.Sd.IrrAb := by
  intro l _ Γ _ _ _ n r hr hio H H' hH hle hab
  have h0 := hio H hH
  have hne : (⊤ : Submodule (Formalism.ConjugateSelfDual.Qbar l) (Fin n → Formalism.ConjugateSelfDual.Qbar l)) ≠ ⊥ := h0.1
  haveI : Nontrivial (Fin n → Formalism.ConjugateSelfDual.Qbar l) := Submodule.nontrivial_iff (Formalism.ConjugateSelfDual.Qbar l) |>.mp ⟨_, _, hne⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hne (Subsingleton.elim _ _)
  refine ⟨hne, fun _ _ _ => trivial, fun W _ hW => ?_⟩
  by_contra hcon
  have hab' : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ H'.subgroupOf H := fun a b =>
    Subgroup.mem_subgroupOf.mpr (hab a a.2 b b.2)
  haveI : (H'.subgroupOf H).Normal := ⟨fun x hx g => by
    have := (H'.subgroupOf H).mul_mem (hab' g x) hx
    simpa using this⟩
  obtain ⟨φ, hφ1, -, hφn, M, hM⟩ := exists_selfTwist (r.comp H.subtype) (H'.subgroupOf H) hab'
    (fun U hU => h0.2.2 U le_top fun g v hv => hU g trivial v hv)
    (fun h => hcon (h W fun g hg v hv => hW ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ v hv))
  have hM' : ∀ g : H, ((φ g : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) • ((M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    have := hM g trivial
    rw [Matrix.mul_smul] at this
    exact this
  have hiff : ∀ g : H, φ g = 1 ↔ (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    constructor
    · intro h
      have := hM' g
      rwa [h, Units.val_one, one_smul] at this
    · intro h
      have h1 := hM' g
      rw [← h] at h1
      haveI : NeZero n := ⟨hn⟩
      have h2 : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) ≠ 0 :=
        (M * r g).ne_zero
      exact Units.ext (smul_left_injective _ h2 (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set H) := by
    have hc : Continuous fun g : H => (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) :=
      Units.continuous_val.comp (hr.comp continuous_subtype_val)
    have : (φ.ker : Set H) = {g : H | (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M} := Set.ext fun g => hiff g
    rw [this]
    exact isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)
  haveI : NeZero n := ⟨hn⟩
  have hrg : φ.range ≤ rootsOfUnity n (Formalism.ConjugateSelfDual.Qbar l) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hφn g
  haveI : Finite φ.range := Finite.of_injective _ (Subgroup.inclusion_injective hrg)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker : Set H) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hop' : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hop
  have h1 := hio _ hop'
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)))
  have htop := (h1.2.2 (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a) le_top (by
    rintro ⟨_, g, hg, rfl⟩ v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    change (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v) =
      a • ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, (hiff g).mp hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])).resolve_left ha
  have hMa : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = a • 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a := by
      rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at this
    rw [this]; simp
  apply hφ1
  ext1 g
  exact (hiff g).mpr (by rw [hMa]; simp)
