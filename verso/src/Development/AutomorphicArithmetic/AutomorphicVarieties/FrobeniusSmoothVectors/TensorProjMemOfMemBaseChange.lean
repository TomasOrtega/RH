import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis k H`. Establish `hli : LinearIndependent K (fun j => ι (e j))`. Rewrite using `[linearIndependent_iff']`. Introduce `s c hc j hj`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff k]`.

Introduce `l`. Establish `h1` using `congrArg (π l) hc`. Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [hπ] at h1`. Conclude with `linearIndependent_iff'.1 e.linearIndependent s (fun j => l (c j)) h1 j hj`.

Establish `hsp : ⊤ ≤ Submodule.span K (Set.range fun j => ι (e j))`. Rewrite using `[← hs, Submodule.span_le]`. Introduce and unpack `_ ⟨h, rfl⟩`. Establish `hh : h ∈ Submodule.span k (Set.range e)` using `by rw [e.span_eq]; trivial`. Proceed by induction on `hh using Submodule.span_induction with`.

Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [hι]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[← (Module.Basis.mk hli hsp).mk_eq_rank'', ← e.mk_eq_rank'']`.
-/
private theorem rank_eq_of_scalar_extension_data {H H' : Type} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module K H']
    (ι : H →+ H') (hι : ∀ (a : k) h, ι (a • h) = algebraMap k K a • ι h)
    (π : (K →ₗ[k] k) → H' →+ H) (hπ : ∀ l c h, π l (c • ι h) = l c • h)
    (hs : Submodule.span K (Set.range ι) = ⊤) : Module.rank K H' = Module.rank k H := by
  classical
  let e := Module.Free.chooseBasis k H
  have hli : LinearIndependent K (fun j => ι (e j)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro l
    have h1 := congrArg (π l) hc
    rw [map_sum, map_zero] at h1
    simp only [hπ] at h1
    exact linearIndependent_iff'.1 e.linearIndependent s (fun j => l (c j)) h1 j hj
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun j => ι (e j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have hh : h ∈ Submodule.span k (Set.range e) := by rw [e.span_eq]; trivial
    induction hh using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hι]; exact Submodule.smul_mem _ _ hx
  rw [← (Module.Basis.mk hli hsp).mk_eq_rank'', ← e.mk_eq_rank'']

variable {W : Type} [AddCommGroup W] [Module k W]

private noncomputable def n4p (l : K →ₗ[k] k) : K ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap ∘ₗ l.rTensor W

/- English proof (translation)
Simplify using `[n4p]`.
-/
@[simp] private theorem tensor_proj_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c ⊗ₜ[k] x) = l c • x := by
  simp [n4p]

/- English proof (translation)
Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensor_proj_tmul]`.
-/
private theorem tensor_proj_smul_one_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c • ((1 : K) ⊗ₜ[k] x)) = l c • x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensor_proj_tmul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c x => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
private theorem tensor_proj_baseChange_map (l : K →ₗ[k] k) (f : W →ₗ[k] W) (x : K ⊗[k] W) :
    n4p l (f.baseChange K x) = f (n4p l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c x => simpa using b.smul_mem _ x.2`. Consider the case `add x y hx hy => simpa using add_mem hx hy`.
-/
private theorem tensor_proj_mem_of_mem_baseChange (l : K →ₗ[k] k) (b : Submodule k W) (x : K ⊗[k] W) (hx : x ∈ b.baseChange K) :
    n4p l x ∈ b := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simpa using b.smul_mem _ x.2
  | add x y hx hy => simpa using add_mem hx hy

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨∅, fun t _ => by simp⟩`. Consider the case `tmul c x`. Use `⟨(e.repr c).support, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1 : c = ∑ i ∈ t, e.repr c i • e i` using `by conv_lhs => rw [← e.linearCombination_repr c, Finsupp.linearCombination_apply]`.

Conclude with `Finsupp.sum_of_support_subset _ ht _ (fun _ _ => by simp)`. Use `conv_lhs => rw [h1]`. Rewrite using `[TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tensor_proj_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨s', hs'⟩` from `hy`. Use `⟨s ∪ s', fun t ht => ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [hs t (Finset.subset_union_left.trans ht), hs' t (Finset.subset_union_right.trans ht)]`. Simplify using `[← Finset.sum_add_distrib, TensorProduct.tmul_add]`.
-/
private theorem baseChange_eq_sum_coord_basis {I : Type} (e : Module.Basis I k K) (x : K ⊗[k] W) :
    ∃ s : Finset I, ∀ t : Finset I, s ⊆ t → x = ∑ i ∈ t, e i • ((1 : K) ⊗ₜ[k] n4p (e.coord i) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun t _ => by simp⟩
  | tmul c x =>
    refine ⟨(e.repr c).support, fun t ht => ?_⟩
    have h1 : c = ∑ i ∈ t, e.repr c i • e i := by
      conv_lhs => rw [← e.linearCombination_repr c, Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset _ ht _ (fun _ _ => by simp)
    conv_lhs => rw [h1]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensor_proj_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    conv_lhs => rw [hs t (Finset.subset_union_left.trans ht), hs' t (Finset.subset_union_right.trans ht)]
    simp [← Finset.sum_add_distrib, TensorProduct.tmul_add]

variable {G V : Type}

variable (K) in
private noncomputable def n4i : ((G → W) × (V → W)) →+ ((G → K ⊗[k] W) × (V → K ⊗[k] W)) where
  toFun y := (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]

private noncomputable def n4q (l : K →ₗ[k] k) : ((G → K ⊗[k] W) × (V → K ⊗[k] W)) →+ ((G → W) × (V → W)) where
  toFun y := (fun g => n4p l (y.1 g), fun v => n4p l (y.2 v))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [n4i]`.
-/
private theorem inclusion_smul_algebraMap (a : k) (y : (G → W) × (V → W)) :
    n4i (k := k) K (a • y) = algebraMap k K a • n4i (k := k) K y := by
  ext <;> simp [n4i]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [n4i, n4q, tensor_proj_smul_one_tmul]`.
-/
private theorem descend_smul_inclusion (l : K →ₗ[k] k) (c : K) (y : (G → W) × (V → W)) :
    n4q l (c • n4i (k := k) K y) = l c • y := by
  ext <;> simp [n4i, n4q, tensor_proj_smul_one_tmul]

variable [Group G] [TopologicalSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)
  (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (K ⊗[k] W))
  (hρ : ∀ g, ρ' g = (ρ g).baseChange K)

include hρ

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hy`. Use `⟨h1.comp (fun x => (1 : K) ⊗ₜ[k] x), fun s t => ?_, fun v s => ?_⟩` and prove the remaining obligations. Simplify using `[n4i, hρ, h2, TensorProduct.tmul_add]`. Use `Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v s)` as an intermediate fact. Simplify `this` using `[n4i, hρ, TensorProduct.tmul_sub]`.
-/
private theorem inclusion_cocycle_mem_Z1 (y) (hy : y ∈ Z1C loc ρ b) :
    n4i (k := k) K y ∈ Z1C loc ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (fun x => (1 : K) ⊗ₜ[k] x), fun s t => ?_, fun v s => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_add]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v s)
    simpa [n4i, hρ, TensorProduct.tmul_sub] using this

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hy`. Use `⟨h1.comp (n4p l), fun s t => ?_, fun v s => ?_⟩` and prove the remaining obligations. Simplify using `[n4q, hρ, h2, tensor_proj_baseChange_map]`. Use `tensor_proj_mem_of_mem_baseChange l _ _ (h3 v s)` as an intermediate fact. Simplify `this` using `[n4q, hρ, tensor_proj_baseChange_map]`.
-/
private theorem descend_cocycle_mem_Z1 (l : K →ₗ[k] k) (y) (hy : y ∈ Z1C loc ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ Z1C loc ρ b := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (n4p l), fun s t => ?_, fun v s => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v s)
    simpa [n4q, hρ, tensor_proj_baseChange_map] using this

omit [TopologicalSpace G] in
/- English proof (translation)
Take `⟨X, h2, h3⟩` from `hy`. Use `⟨1 ⊗ₜ X, fun s => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `[n4i, hρ, h2, TensorProduct.tmul_sub]`. Use `Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v)` as an intermediate fact. Simplify `this` using `[n4i, TensorProduct.tmul_sub]`.
-/
private theorem inclusion_coboundary_mem_B1 (y) (hy : y ∈ continuousCoboundaries1 ρ b) :
    n4i (k := k) K y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨1 ⊗ₜ X, fun s => ?_, fun v => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_sub]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v)
    simpa [n4i, TensorProduct.tmul_sub] using this

omit [TopologicalSpace G] in
/- English proof (translation)
Take `⟨X, h2, h3⟩` from `hy`. Use `⟨n4p l X, fun s => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `[n4q, hρ, h2, tensor_proj_baseChange_map]`. Use `tensor_proj_mem_of_mem_baseChange l _ _ (h3 v)` as an intermediate fact. Simplify `this` using `[n4q]`.
-/
private theorem descend_coboundary_mem_B1 (l : K →ₗ[k] k) (y) (hy : y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ continuousCoboundaries1 ρ b := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨n4p l X, fun s => ?_, fun v => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v)
    simpa [n4q] using this

/- English proof (translation)
Use `le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Set `e` to `Module.Free.chooseBasis k K choose s hs using fun x : K ⊗[k] W => baseChange_eq_sum_coord_basis e x`. Establish `hf : (Set.range y.1 ∪ Set.range y.2).Finite` using `hy.1.range_finite.union (Set.finite_range _)`. Establish `hy' : y = ∑ i ∈ hf.toFinset.biUnion s, e i • n4i (k` using `k) K (n4q (e.coord i) y) := by`. Use extensionality with `g`.

Rewrite using `[Prod.fst_sum, Finset.sum_apply]`. Conclude with `hs _ _ (Finset.subset_biUnion_of_mem s (by simp))`. Rewrite using `[Prod.snd_sum, Finset.sum_apply]`. Conclude with `hs _ _ (Finset.subset_biUnion_of_mem s (by simp))`. Rewrite using `[hy']`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, descend_cocycle_mem_Z1 loc ρ b ρ' hρ _ y hy, rfl⟩)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ y hy`.
-/
private theorem cocycles_baseChange_eq_span [CompactSpace G] [Finite V] :
    Z1C loc ρ' (fun v => (b v).baseChange K) =
      Submodule.span K (n4i (k := k) K '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) := by
  classical
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · let e := Module.Free.chooseBasis k K
    choose s hs using fun x : K ⊗[k] W => baseChange_eq_sum_coord_basis e x
    have hf : (Set.range y.1 ∪ Set.range y.2).Finite := hy.1.range_finite.union (Set.finite_range _)
    have hy' : y = ∑ i ∈ hf.toFinset.biUnion s, e i • n4i (k := k) K (n4q (e.coord i) y) := by
      ext g
      · rw [Prod.fst_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
      · rw [Prod.snd_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, descend_cocycle_mem_Z1 loc ρ b ρ' hρ _ y hy, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ y hy

/- English proof (translation)
Set `i0 : Z1C loc ρ b →+ Z1C loc ρ' (fun v => (b v).baseChange K)` to `{ toFun := fun y => ⟨n4i (k := k) K y.1, inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ _ y.2⟩ map_zero' := Subtype.ext (map_zero _) map_add' := fun x y => Subtype.ext (map_add _ _ _) }`. Set `q0 (l : K →ₗ[k] k) : Z1C loc ρ' (fun v => (b v).baseChange K) →+ Z1C loc ρ b` to `{ toFun := fun y => ⟨n4q l y.1, descend_cocycle_mem_Z1 loc ρ b ρ' hρ l _ y.2⟩ map_zero' := Subtype.ext (map_zero _) map_add' := fun x y => Subtype.ext (map_add _ _ _) }`. Set `i1 : H1C loc ρ b →+ H1C loc ρ' (fun v => (b v).baseChange K)` to `QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) i0 (fun y hy => inclusion_coboundary_mem_B1 ρ b ρ' hρ _ hy)`. Set `q1 (l : K →ₗ[k] k) : H1C loc ρ' (fun v => (b v).baseChange K) →+ H1C loc ρ b` to `QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (q0 l) (fun y hy => descend_coboundary_mem_B1 ρ b ρ' hρ l _ hy)`. Establish `hi : ∀ y, i1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (i0 y)` using `fun _ => rfl`.

Establish `hq : ∀ l y, q1 l (Submodule.Quotient.mk y) = Submodule.Quotient.mk (q0 l y)` using `fun _ _ => rfl`. Use `rank_eq_of_scalar_extension_data i1 (fun a h => ?_) q1 (fun l c h => ?_) ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`. Rewrite using `[← Submodule.Quotient.mk_smul, hi, hi, ← Submodule.Quotient.mk_smul]`. Use `congr 1`.

Conclude with `Subtype.ext (inclusion_smul_algebraMap a y.1)`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`. Rewrite using `[hi, ← Submodule.Quotient.mk_smul, hq, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (descend_smul_inclusion l c y.1)`.

Rewrite using `[eq_top_iff]`. Introduce `h hT`. Use `clear hT`. Take `⟨⟨y, hy⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`. Establish `hy'` using `hy`.

Rewrite `hy'` using `[cocycles_baseChange_eq_span loc ρ b ρ' hρ]`. Use `revert hy`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`.

Introduce `hy`. Conclude with `Submodule.subset_span ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩`. Consider the case `zero => intro hy`. Conclude with `zero_mem _`. Consider the case `add x y hx' hy' hx hy`.

Introduce `_`. Rewrite `hx'`, `hy'` using `[← cocycles_baseChange_eq_span loc ρ b ρ' hρ]`. Conclude with `add_mem (hx hx') (hy hy')`. Consider the case `smul a x hx' hx`. Introduce `_`.

Rewrite `hx'` using `[← cocycles_baseChange_eq_span loc ρ b ρ' hρ]`. Conclude with `Submodule.smul_mem _ a (hx hx')`.
-/
private theorem rank_H1_baseChange_eq [CompactSpace G] [Finite V] :
    Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  let i0 : Z1C loc ρ b →+ Z1C loc ρ' (fun v => (b v).baseChange K) :=
    { toFun := fun y => ⟨n4i (k := k) K y.1, inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let q0 (l : K →ₗ[k] k) : Z1C loc ρ' (fun v => (b v).baseChange K) →+ Z1C loc ρ b :=
    { toFun := fun y => ⟨n4q l y.1, descend_cocycle_mem_Z1 loc ρ b ρ' hρ l _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let i1 : H1C loc ρ b →+ H1C loc ρ' (fun v => (b v).baseChange K) :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) i0
      (fun y hy => inclusion_coboundary_mem_B1 ρ b ρ' hρ _ hy)
  let q1 (l : K →ₗ[k] k) : H1C loc ρ' (fun v => (b v).baseChange K) →+ H1C loc ρ b :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (q0 l)
      (fun y hy => descend_coboundary_mem_B1 ρ b ρ' hρ l _ hy)
  have hi : ∀ y, i1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (i0 y) := fun _ => rfl
  have hq : ∀ l y, q1 l (Submodule.Quotient.mk y) = Submodule.Quotient.mk (q0 l y) := fun _ _ => rfl
  refine rank_eq_of_scalar_extension_data i1 (fun a h => ?_) q1 (fun l c h => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [← Submodule.Quotient.mk_smul, hi, hi, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (inclusion_smul_algebraMap a y.1)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [hi, ← Submodule.Quotient.mk_smul, hq, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (descend_smul_inclusion l c y.1)
  · rw [eq_top_iff]
    intro h hT
    clear hT
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    have hy' := hy
    rw [cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hy'
    revert hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro hy
      exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
    | zero => intro hy; exact zero_mem _
    | add x y hx' hy' hx hy =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx' hy'
      exact add_mem (hx hx') (hy hy')
    | smul a x hx' hx =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx'
      exact Submodule.smul_mem _ a (hx hx')

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `k K G W V _ _ _ _ _ _ _ _ _ Gv _ _ loc ρ b ρ' hρ`. Conclude with `⟨cocycles_baseChange_eq_span loc ρ b ρ' hρ, rank_H1_baseChange_eq loc ρ b ρ' hρ⟩`.
-/
theorem UpperTheory.V.Fr.n4 :
    ∀ {k K G W V : Type} [Field k] [Field K] [Algebra k K] [Group G] [TopologicalSpace G] [CompactSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (TensorProduct k K W)), (∀ g, ρ' g = (ρ g).baseChange K) → Z1C loc ρ' (fun v => (b v).baseChange K) = Submodule.span K ((fun y : (G → W) × (V → W) => (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)) '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) ∧ Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  intro k K G W V _ _ _ _ _ _ _ _ _ Gv _ _ loc ρ b ρ' hρ
  exact ⟨cocycles_baseChange_eq_span loc ρ b ρ' hρ, rank_H1_baseChange_eq loc ρ b ρ' hρ⟩
