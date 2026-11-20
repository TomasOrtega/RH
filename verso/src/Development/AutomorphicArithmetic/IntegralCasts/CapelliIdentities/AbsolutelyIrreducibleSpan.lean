import Mathlib

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr.{u_1, u_2, u_3} :
    {k : Type u_1} → [Field k] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → {G : Type u_3} → (G → Matrix n n k) → Prop :=
    fun {k : Type u_1} [Field k] {n : Type u_2} [Fintype n] [DecidableEq n] {G : Type u_3} (ρ : G → Matrix n n k) ↦
      (∀ (W : Submodule k (n → k)), (∀ (g : G), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ (M : Matrix n n k), (∀ (g : G), M * ρ g = ρ g * M) → ∃ (c : k), M = c • (1 : Matrix n n k)

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan :
    Prop :=
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsLocalRing O] (n : Type) [inst_2 : Fintype n] [inst_3 : DecidableEq n]
      (G : Type) [inst_4 : Monoid G] (ρ : G →* Matrix n n O),
      (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr fun (g : G) ↦
          ((ρ : G → Matrix n n O) g).map (⇑(IsLocalRing.residue O) : O → IsLocalRing.ResidueField O)) →
        Submodule.span O (Set.range (⇑ρ : G → Matrix n n O)) = ⊤

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `set A : Subalgebra k (Module.End k (n → k)) := (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA`. Establish `hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A` using `fun g => ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩`. Establish `hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v` using `fun _ _ => rfl`. Establish `hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v` using `fun c v => by`.

Rewrite using `[hsm]`. Simplify using the standard rewrite rules. Use `haveI : IsSemisimpleModule A (n → k) := by`. Rewrite using `[isSemisimpleModule_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `W`. Set `W' : Submodule k (n → k)` to `{ carrier := W add_mem' := fun ha hb => W.add_mem ha hb zero_mem' := W.zero_mem smul_mem' := fun c v hv => by`. Rewrite using `[← hk]`. Conclude with `W.smul_mem _ hv }`. Establish `hW` using `h1 W' (fun g v hv => by`.

Use `W.smul_mem (⟨_, hmem g⟩ : A) hv` as an intermediate fact. Rewrite `this` using `[hsm]`. Conclude with `this)`. Break down `hW with hW | hW` into its components or cases. Establish `: W = ⊥`.

Use extensionality with `v`. Establish `: v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k))` using `by rw [hW]`. Conclude with `this`. Conclude with `⟨⊤, this ▸ isCompl_bot_top⟩`. Establish `: W = ⊤`.

Use extensionality with `v`. Establish `: v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k))` using `by rw [hW]`. Conclude with `this`. Conclude with `⟨⊥, this ▸ isCompl_top_bot⟩`. Establish `hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v`.

Introduce `φ`. Set `ψ : Module.End k (n → k)` to `{ toFun := φ map_add' := φ.map_add map_smul' := fun c v => by`. Rewrite using `[← hk, φ.map_smul, hk]`. Use `rfl }`. Take `⟨c, hc⟩` from `h2 (LinearMap.toMatrix' ψ) (fun g => by`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Conclude with `φ.map_smul (⟨_, hmem g⟩ : A) v)`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations.

Establish `h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k))`. Rewrite using `[← hc, Matrix.toLin'_toMatrix']`. Establish `h4 : φ v = ψ v` using `rfl`. Rewrite using `[h4, h3]`. Simplify using the standard rewrite rules.

Rewrite using `[eq_top_iff]`. Introduce `M _`. Set `f : Module.End (Module.End A (n → k)) (n → k)` to `{ toFun := Matrix.toLin' M map_add' := (Matrix.toLin' M).map_add map_smul' := fun φ v => by`. Take `⟨c, hc⟩` from `hsc φ`. Express the relevant statement in the definitionally equal form `Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)`.

Rewrite using `[hc, hc, map_smul] }`. Take `⟨r, hr⟩` from `jacobson_density f (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))`. Take `⟨r, N, hN, rfl⟩` from `r`. Establish `: M = N`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Apply `(Pi.basisFun k n).ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Pi.basisFun_apply]`. Conclude with `hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Conclude with `this ▸ hN`.
-/
private theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : Type} (ρ : G → Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Algebra.adjoin k (Set.range ρ) = ⊤ := by
  classical
  obtain ⟨h1, h2⟩ := h
  set A : Subalgebra k (Module.End k (n → k)) :=
    (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA
  have hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A := fun g =>
    ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  have hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v := fun _ _ => rfl
  have hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v := fun c v => by
    rw [hsm]; simp
  haveI : IsSemisimpleModule A (n → k) := by
    rw [isSemisimpleModule_iff]
    constructor
    intro W
    let W' : Submodule k (n → k) :=
      { carrier := W
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [← hk]; exact W.smul_mem _ hv }
    have hW := h1 W' (fun g v hv => by
      have := W.smul_mem (⟨_, hmem g⟩ : A) hv
      rw [hsm] at this
      exact this)
    rcases hW with hW | hW
    · have : W = ⊥ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊤, this ▸ isCompl_bot_top⟩
    · have : W = ⊤ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊥, this ▸ isCompl_top_bot⟩
  have hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v := by
    intro φ
    let ψ : Module.End k (n → k) :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun c v => by
          rw [← hk, φ.map_smul, hk]; rfl }
    obtain ⟨c, hc⟩ := h2 (LinearMap.toMatrix' ψ) (fun g => by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      refine LinearMap.ext fun v => ?_
      exact φ.map_smul (⟨_, hmem g⟩ : A) v)
    refine ⟨c, fun v => ?_⟩
    have h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k)) := by
      rw [← hc, Matrix.toLin'_toMatrix']
    have h4 : φ v = ψ v := rfl
    rw [h4, h3]
    simp
  rw [eq_top_iff]
  intro M _
  let f : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := Matrix.toLin' M
      map_add' := (Matrix.toLin' M).map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        change Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f
    (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))
  obtain ⟨r, N, hN, rfl⟩ := r
  have : M = N := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun k n).ext
    intro i
    rw [Pi.basisFun_apply]
    exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this ▸ hN

/- English proof (translation)
Introduce `O _ _ n _ _ G _ ρ h`. Establish `h1` using `UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h`. Set `π : Matrix n n O →+* Matrix n n (IsLocalRing.ResidueField O)` to `(IsLocalRing.residue O).mapMatrix`. Establish `h2 : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => π (ρ g)) = ⊤`. Rewrite using `[← Algebra.adjoin_eq_span_of_subset]`.

Conclude with `(congrArg Subalgebra.toSubmodule h1).trans rfl`. Introduce `x hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Establish `: x ∈ MonoidHom.mrange (π.toMonoidHom.comp ρ)` using `(Submonoid.closure_le (S := MonoidHom.mrange (π.toMonoidHom.comp ρ))).mpr (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩) hx`. Conclude with `this`.

Establish `h3 : ∀ X : Matrix n n (IsLocalRing.ResidueField O), ∃ Y ∈ Submodule.span O (Set.range (ρ : G → Matrix n n O)), π Y = X`. Introduce `X`. Establish `hX : X ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => π (ρ g))` using `h2 ▸ Submodule.mem_top`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`.

Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, Submodule.add_mem _ ha hb, map_add _ _ _⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨d, rfl⟩` from `IsLocalRing.residue_surjective c`.

Use `⟨d • a, Submodule.smul_mem _ _ ha, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[π]`. Rewrite using `[eq_top_iff]`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_` and prove the remaining obligations.

Introduce `M _`. Take `⟨Y, hY, hYM⟩` from `h3 (π M)`. Establish `h4 : M - Y ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Matrix n n O))`. Rewrite using `[Matrix.matrix_eq_sum_single (M - Y)]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `h5 : (M - Y) i j ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Establish `h6 : π (M - Y) = 0` using `by rw [map_sub, hYM, sub_self]`. Conclude with `congrFun (congrFun h6 i) j`. Establish `h7 : Matrix.single i j ((M - Y) i j) = (M - Y) i j • Matrix.single i j (1 : O)`.

Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[h7]`. Conclude with `Submodule.smul_mem_smul h5 Submodule.mem_top`. Establish `h8 : M = Y + (M - Y)` using `by abel`. Rewrite using `[h8]`.

Conclude with `Submodule.add_mem_sup hY h4`.
-/
theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan :
    UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan := by
  intro O _ _ n _ _ G _ ρ h
  have h1 := UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h
  let π : Matrix n n O →+* Matrix n n (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  have h2 : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) = ⊤ := by
    rw [← Algebra.adjoin_eq_span_of_subset]
    · exact (congrArg Subalgebra.toSubmodule h1).trans rfl
    · intro x hx
      apply Submodule.subset_span
      have : x ∈ MonoidHom.mrange (π.toMonoidHom.comp ρ) :=
        (Submonoid.closure_le (S := MonoidHom.mrange (π.toMonoidHom.comp ρ))).mpr
          (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩) hx
      exact this
  have h3 : ∀ X : Matrix n n (IsLocalRing.ResidueField O),
      ∃ Y ∈ Submodule.span O (Set.range (ρ : G → Matrix n n O)), π Y = X := by
    intro X
    have hX : X ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) := h2 ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨d • a, Submodule.smul_mem _ _ ha, ?_⟩
      ext i j
      simp [π]
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro M _
  obtain ⟨Y, hY, hYM⟩ := h3 (π M)
  have h4 : M - Y ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Matrix n n O)) := by
    rw [Matrix.matrix_eq_sum_single (M - Y)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h5 : (M - Y) i j ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have h6 : π (M - Y) = 0 := by rw [map_sub, hYM, sub_self]
      exact congrFun (congrFun h6 i) j
    have h7 : Matrix.single i j ((M - Y) i j) = (M - Y) i j • Matrix.single i j (1 : O) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h7]
    exact Submodule.smul_mem_smul h5 Submodule.mem_top
  have h8 : M = Y + (M - Y) := by abel
  rw [h8]
  exact Submodule.add_mem_sup hY h4
