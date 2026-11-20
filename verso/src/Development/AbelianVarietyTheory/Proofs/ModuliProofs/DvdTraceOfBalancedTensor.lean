import Mathlib

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨U, ⟨hUW, hU0, hUs⟩, hmin⟩` from `(wellFounded_lt (α := Submodule K V)).has_min {U | U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, le_rfl, hW, hs⟩`. Take `⟨v, hvU, hv0⟩` from `(Submodule.ne_bot_iff U).1 hU0`. Use `⟨v, hUW hvU, hv0, fun i => ?_⟩` and prove the remaining obligations. Use `haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0`. Take `⟨l, hl⟩` from `Module.End.exists_eigenvalue ((T i).restrict (hUs i))`.

Take `⟨w, hw⟩` from `hl.exists_hasEigenvector`. Establish `hw1 : T i w = l • (w : V)` using `congrArg Subtype.val hw.apply_eq_smul`. Establish `hw0 : (w : V) ≠ 0` using `fun h => hw.2 (Subtype.ext h)`. Set `U' : Submodule K V` to `U ⊓ LinearMap.ker (T i - l • LinearMap.id)`. Establish `hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ T i x = l • x`.

Introduce `x`. Simplify using `[U', sub_eq_zero]`. Establish `hU' : U' = U`. Assume the negation of the conclusion as `hne`. Use `hmin U' ⟨le_trans inf_le_left hUW, ?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)` and prove the remaining obligations.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨w, (hmem _).2 ⟨w.2, hw1⟩, hw0⟩`. Introduce `j x hx`. Take `⟨h1, h2⟩` from `(hmem x).1 hx`. Conclude with `(hmem _).2 ⟨hUs j x h1, by rw [hT, h2, map_smul]⟩`. Conclude with `⟨l, ((hmem v).1 (hU'.symm ▸ hvU)).2⟩`.
-/
theorem exists_common_eigenvector_mem {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : ι → V →ₗ[K] V)
    (hT : ∀ i j v, T i (T j v) = T j (T i v)) (W : Submodule K V) (hW : W ≠ ⊥)
    (hs : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ l : K, T i v = l • v := by
  obtain ⟨U, ⟨hUW, hU0, hUs⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min
      {U | U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, le_rfl, hW, hs⟩
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).1 hU0
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T i).restrict (hUs i))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw1 : T i w = l • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let U' : Submodule K V := U ⊓ LinearMap.ker (T i - l • LinearMap.id)
  have hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ T i x = l • x := by
    intro x
    simp [U', sub_eq_zero]
  have hU' : U' = U := by
    by_contra hne
    refine hmin U' ⟨le_trans inf_le_left hUW, ?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
    · exact (Submodule.ne_bot_iff _).2 ⟨w, (hmem _).2 ⟨w.2, hw1⟩, hw0⟩
    · intro j x hx
      obtain ⟨h1, h2⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨hUs j x h1, by rw [hT, h2, map_smul]⟩
  exact ⟨l, ((hmem v).1 (hU'.symm ▸ hvU)).2⟩

section
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]

/- English proof (translation)
Establish `h1 : ∀ t : H ⊗[O] H, LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) t = LinearMap.lTensor H α (((1 : H) ⊗ₜ[O] h) * t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`.

Consider the case `add x y hx hy => simp only [map_add, mul_add, hx, hy]`. Establish `h2 : ∀ t : H ⊗[O] H, h • LinearMap.lTensor H α t = LinearMap.lTensor H α ((h ⊗ₜ[O] (1 : H)) * t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]`. Rewrite using `[h1, h2, hΘ]`.
-/
theorem lTensor_comp_mulLeft_of_balanced {N : Type*} [AddCommGroup N] [Module O N]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (α : H →ₗ[O] N) (h : H) :
    LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) Θ = h • LinearMap.lTensor H α Θ := by
  have h1 : ∀ t : H ⊗[O] H, LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) t
      = LinearMap.lTensor H α (((1 : H) ⊗ₜ[O] h) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h2 : ∀ t : H ⊗[O] H, h • LinearMap.lTensor H α t
      = LinearMap.lTensor H α ((h ⊗ₜ[O] (1 : H)) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]
  rw [h1, h2, hΘ]

noncomputable def contractRight (Θ : H ⊗[O] H) : Module.Dual O H →ₗ[O] H where
  toFun α := TensorProduct.rid O H (LinearMap.lTensor H α Θ)
  map_add' a b := by simp [LinearMap.lTensor_add]
  map_smul' c a := by simp [LinearMap.lTensor_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem contractRight_apply (Θ : H ⊗[O] H) (α : Module.Dual O H) :
    contractRight Θ α = TensorProduct.rid O H (LinearMap.lTensor H α Θ) := rfl

/- English proof (translation)
Proceed by induction on `Θ using TensorProduct.induction_on with`. Consider the case `zero => simp [contractRight_apply]`. Consider the case `tmul x y`. Simplify using `only [contractRight_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr]`. Consider the case `add x y hx hy`.

Simplify using `only [contractRight_apply, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib] at *`. Rewrite using `[hx, hy]`.
-/
theorem sum_contractRight_coord_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) : ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] b j = Θ := by
  induction Θ using TensorProduct.induction_on with
  | zero => simp [contractRight_apply]
  | tmul x y =>
    simp only [contractRight_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr]
  | add x y hx hy =>
    simp only [contractRight_apply, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib] at *
    rw [hx, hy]

/- English proof (translation)
Establish `htr : Algebra.trace O H = ∑ j, (b.coord j) ∘ₗ LinearMap.mulLeft O (b j)`. Use extensionality with `y`. Rewrite using `[Algebra.trace_eq_matrix_trace b]`. Simplify using `[Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]`. Establish `hr : ∀ (h : H) (t : H ⊗[O] O), TensorProduct.rid O H (h • t) = h * TensorProduct.rid O H t`.

Introduce `h t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]`.

Use `conv_rhs => rw [← sum_contractRight_coord_tmul b Θ]`. Rewrite using `[htr, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[contractRight_apply, lTensor_comp_mulLeft_of_balanced Θ hΘ, hr, ← contractRight_apply]`. Simplify using `[mul_comm]`.
-/
theorem contractRight_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) :
    contractRight Θ (Algebra.trace O H) = Algebra.TensorProduct.lmul' O Θ := by
  have htr : Algebra.trace O H = ∑ j, (b.coord j) ∘ₗ LinearMap.mulLeft O (b j) := by
    ext y
    rw [Algebra.trace_eq_matrix_trace b]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]
  have hr : ∀ (h : H) (t : H ⊗[O] O),
      TensorProduct.rid O H (h • t) = h * TensorProduct.rid O H t := by
    intro h t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]
  conv_rhs => rw [← sum_contractRight_coord_tmul b Θ]
  rw [htr, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractRight_apply, lTensor_comp_mulLeft_of_balanced Θ hΘ, hr, ← contractRight_apply]
  simp [mul_comm]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Set `b` to `Module.Free.chooseBasis O H`. Use `haveI : FiniteDimensional K (H →ₗ[O] K) := Module.Finite.equiv (b.constr K)`. Establish `hsm : ∀ (l : K) (a : H →ₗ[O] K), LinearMap.lTensor H a Θ = 0 → LinearMap.lTensor H (l • a) Θ = 0`. Introduce `l a ha`.

Establish `: l • a = LinearMap.mulLeft O l ∘ₗ a` using `by ext; simp`. Rewrite using `[this, LinearMap.lTensor_comp, LinearMap.comp_apply, ha, map_zero]`. Set `W : Submodule K (H →ₗ[O] K)` to `{ carrier := {a | LinearMap.lTensor H a Θ = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Simplify using `[LinearMap.lTensor_add, ha, hb]`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun l a ha => hsm l a ha }`. Set `T : H → (H →ₗ[O] K) →ₗ[K] (H →ₗ[O] K)` to `fun h => { toFun := fun a => a ∘ₗ LinearMap.mulLeft O h map_add' := fun a b => by ext; simp map_smul' := fun l a => by ext; simp }`. Take `⟨v, hvW, hv0, hv⟩` from `exists_common_eigenvector_mem T (fun i j a => by ext; simp [T, mul_left_comm]) W ((Submodule.ne_bot_iff _).2 ⟨α, hα, hne⟩) (fun h a ha => by`. Express the relevant statement in the definitionally equal form `LinearMap.lTensor H (a ∘ₗ LinearMap.mulLeft O h) Θ = 0`.

Rewrite using `[lTensor_comp_mulLeft_of_balanced Θ hΘ, show LinearMap.lTensor H a Θ = 0 from ha, smul_zero])`. Use `choose l hl using hv`. Establish `hl' : ∀ h x, v (h * x) = l h * v x` using `fun h x => by`. Simplify `LinearMap.congr_fun (hl h) x` using `[T]`. Establish `hv1 : v 1 ≠ 0`.

Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Use extensionality with `x`. Simplify `hl' x 1` using `[h0]`. Set `ga : H →ₐ[O] K` to `AlgHom.ofLinearMap ((v 1)⁻¹ • v) (by simp [hv1]) (by`.

Introduce `x y`. Establish `h1` using `hl' x y`. Establish `h2` using `hl' x 1`. Rewrite `h2` using `[mul_one]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, h1, h2]`.

Use the proof step `field_simp)`. Apply `hK ga` to reduce the goal to its premises. Establish `: ∀ t : H ⊗[O] H, Algebra.TensorProduct.map (AlgHom.id O H) ga t = LinearMap.lTensor H ((v 1)⁻¹ • v) t`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [ga]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[this]`. Conclude with `hsm _ _ hvW`.
-/
theorem eq_zero_of_lTensor_eq_zero_of_balanced [Module.Free O H] [Module.Finite O H]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra O K]
    (hK : ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0)
    (α : H →ₗ[O] K) (hα : LinearMap.lTensor H α Θ = 0) : α = 0 := by
  classical
  by_contra hne
  let b := Module.Free.chooseBasis O H
  haveI : FiniteDimensional K (H →ₗ[O] K) := Module.Finite.equiv (b.constr K)
  have hsm : ∀ (l : K) (a : H →ₗ[O] K), LinearMap.lTensor H a Θ = 0 →
      LinearMap.lTensor H (l • a) Θ = 0 := by
    intro l a ha
    have : l • a = LinearMap.mulLeft O l ∘ₗ a := by ext; simp
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, ha, map_zero]
  let W : Submodule K (H →ₗ[O] K) :=
    { carrier := {a | LinearMap.lTensor H a Θ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        simp [LinearMap.lTensor_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun l a ha => hsm l a ha }
  let T : H → (H →ₗ[O] K) →ₗ[K] (H →ₗ[O] K) := fun h =>
    { toFun := fun a => a ∘ₗ LinearMap.mulLeft O h
      map_add' := fun a b => by ext; simp
      map_smul' := fun l a => by ext; simp }
  obtain ⟨v, hvW, hv0, hv⟩ := exists_common_eigenvector_mem T
    (fun i j a => by ext; simp [T, mul_left_comm]) W
    ((Submodule.ne_bot_iff _).2 ⟨α, hα, hne⟩)
    (fun h a ha => by
      change LinearMap.lTensor H (a ∘ₗ LinearMap.mulLeft O h) Θ = 0
      rw [lTensor_comp_mulLeft_of_balanced Θ hΘ, show LinearMap.lTensor H a Θ = 0 from ha,
        smul_zero])
  choose l hl using hv
  have hl' : ∀ h x, v (h * x) = l h * v x := fun h x => by
    simpa [T] using LinearMap.congr_fun (hl h) x
  have hv1 : v 1 ≠ 0 := by
    intro h0
    apply hv0
    ext x
    simpa [h0] using hl' x 1
  let ga : H →ₐ[O] K := AlgHom.ofLinearMap ((v 1)⁻¹ • v) (by simp [hv1]) (by
    intro x y
    have h1 := hl' x y
    have h2 := hl' x 1
    rw [mul_one] at h2
    simp only [LinearMap.smul_apply, smul_eq_mul, h1, h2]
    field_simp)
  apply hK ga
  have : ∀ t : H ⊗[O] H, Algebra.TensorProduct.map (AlgHom.id O H) ga t
      = LinearMap.lTensor H ((v 1)⁻¹ • v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ga]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact hsm _ _ hvW

end

/- English proof (translation)
Introduce `O H _ _ _ _ _ _ Θ c ⟨hΘ, hc, hK⟩ h`. Set `b` to `Module.Free.chooseBasis O H`. Set `K` to `AlgebraicClosure (IsLocalRing.ResidueField O)`. Establish `hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0`. Introduce `a ha`.

Rewrite using `[IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) K, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]`. Establish `hdet : IsUnit (LinearMap.toMatrix b.dualBasis b (contractRight Θ)).det`. Assume the negation of the conclusion as `hnu`. Establish `h0` using `hm _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)`. Rewrite `h0` using `[RingHom.map_det]`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hv0` to reduce the goal to its premises. Establish `: b.constr O v = 0`. Apply `eq_zero_of_lTensor_eq_zero_of_balanced Θ hΘ K (hK K hm)` to reduce the goal to its premises. Establish `hv' : ∀ i, ∑ j, b.repr (contractRight Θ (b.coord j)) i • v j = 0`.

Introduce `i`. Use `congrFun hv i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, Algebra.smul_def, Module.Basis.coe_dualBasis]`. Establish `e : LinearMap.lTensor H (b.constr O v) Θ = ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j` using `by conv_lhs => rw [← sum_contractRight_coord_tmul b Θ]`. Simplify using `[map_sum]`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr (contractRight Θ (b.coord j))]`. Simplify using `only [TensorProduct.sum_tmul, TensorProduct.smul_tmul]`.

Use `_ = 0 := by`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← TensorProduct.tmul_sum, hv', TensorProduct.tmul_zero, Finset.sum_const_zero]`. Conclude with `(b.constr O).injective (by rw [this, map_zero])`. Set `e` to `LinearEquiv.ofIsUnitDet hdet`.

Establish `he : ∀ a, e a = contractRight Θ a` using `fun a => rfl`. Establish `: Algebra.trace O H = c • e.symm 1`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, e.apply_symm_apply, he, contractRight_trace b Θ hΘ, hc, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[this]`.

Conclude with `Dvd.intro _ rfl`.
-/
theorem dvd_trace_of_balanced_tensor :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  intro O H _ _ _ _ _ _ Θ c ⟨hΘ, hc, hK⟩ h
  classical
  let b := Module.Free.chooseBasis O H
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) K,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  have hdet : IsUnit (LinearMap.toMatrix b.dualBasis b (contractRight Θ)).det := by
    by_contra hnu
    have h0 := hm _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [RingHom.map_det] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have : b.constr O v = 0 := by
      apply eq_zero_of_lTensor_eq_zero_of_balanced Θ hΘ K (hK K hm)
      have hv' : ∀ i, ∑ j, b.repr (contractRight Θ (b.coord j)) i • v j = 0 := by
        intro i
        have := congrFun hv i
        simpa [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, Algebra.smul_def,
          Module.Basis.coe_dualBasis] using this
      have e : LinearMap.lTensor H (b.constr O v) Θ
          = ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j := by
        conv_lhs => rw [← sum_contractRight_coord_tmul b Θ]
        simp [map_sum]
      rw [e]
      calc ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j
          = ∑ j, ∑ i, b i ⊗ₜ[O] (b.repr (contractRight Θ (b.coord j)) i • v j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            conv_lhs => rw [← b.sum_repr (contractRight Θ (b.coord j))]
            simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
        _ = 0 := by
            rw [Finset.sum_comm]
            simp only [← TensorProduct.tmul_sum, hv', TensorProduct.tmul_zero,
              Finset.sum_const_zero]
    exact (b.constr O).injective (by rw [this, map_zero])
  let e := LinearEquiv.ofIsUnitDet hdet
  have he : ∀ a, e a = contractRight Θ a := fun a => rfl
  have : Algebra.trace O H = c • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, he, contractRight_trace b Θ hΘ, hc, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Dvd.intro _ rfl

end GlobalTheory
