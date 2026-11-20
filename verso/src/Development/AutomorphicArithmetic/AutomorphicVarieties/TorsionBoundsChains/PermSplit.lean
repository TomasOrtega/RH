import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G X _ _ U V hUV`. Set `F : (perm G U).IntertwiningMap (perm G X)` to `{ toLinearMap := Finsupp.lmapDomain ℤ ℤ (Subtype.val : U → X) isIntertwining' := by`. Introduce `g`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, perm_apply, Finsupp.lmapDomain_apply]`.

Rewrite using `[← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]`. Use `congr 1 }`. Set `Gm : (perm G X).IntertwiningMap (perm G V)` to `{ toLinearMap := Finsupp.lsubtypeDomain (V : Set X) isIntertwining' := by`. Introduce `g`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations.

Use extensionality with `⟨y, hy⟩`. Express the relevant statement in the definitionally equal form `(Finsupp.mapDomain (fun x => g • x) f) y = (Finsupp.mapDomain (fun v : V => g • v) (Finsupp.subtypeDomain (· ∈ V) f)) ⟨y, hy⟩`. Establish `hy' : g⁻¹ • y ∈ V` using `V.smul_mem _ hy`. Establish `e2 : (⟨y, hy⟩ : V) = g • (⟨g⁻¹ • y, hy'⟩ : V)` using `Subtype.ext (by simp)`. Rewrite using `[e2, Finsupp.mapDomain_apply (MulAction.injective g), Finsupp.subtypeDomain_apply]`.

Establish `e1 : y = g • (g⁻¹ • y)` using `(smul_inv_smul g y).symm`. Use `conv_lhs => rw [e1]`. Rewrite using `[Finsupp.mapDomain_apply (MulAction.injective g)] }`. Use `⟨Rep.ofHom F, Rep.ofHom Gm, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Rep.hom_ofHom]`.

Express the relevant statement in the definitionally equal form `Function.Injective (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))`. Conclude with `Finsupp.mapDomain_injective Subtype.val_injective`. Rewrite using `[Rep.hom_ofHom, Rep.hom_ofHom]`. Introduce `y`. Express the relevant statement in the definitionally equal form `Finsupp.subtypeDomain (· ∈ V) y = 0 ↔ y ∈ Set.range (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))`.

Prove the components needed by the constructor for the conclusion. Introduce `hy0`. Use `⟨Finsupp.subtypeDomain (· ∈ U) y, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Distinguish the cases in `hx : x ∈ U`.

Rewrite using `[show x = ((⟨x, hx⟩ : U) : X) from rfl, Finsupp.mapDomain_apply Subtype.val_injective, Finsupp.subtypeDomain_apply]`. Rewrite using `[Finsupp.mapDomain_notin_range _ _ (by rintro ⟨u, rfl⟩; exact hx u.2)]`. Establish `hxV : x ∈ V` using `(hUV x).2 hx`. Establish `h1` using `DFunLike.congr_fun hy0 ⟨x, hxV⟩`. Simplify using `only [Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply] at h1`.

Conclude with `h1.symm`. Introduce and unpack `⟨u, rfl⟩`. Use extensionality with `⟨x, hx⟩`. Rewrite using `[Finsupp.subtypeDomain_apply, Finsupp.mapDomain_notin_range _ _ ?_]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨w, rfl⟩`. Conclude with `((hUV _).1 hx) w.2`. Rewrite using `[Rep.hom_ofHom]`. Introduce `h`. Use `⟨Finsupp.mapDomain (Subtype.val : V → X) h, ?_⟩` and prove the remaining obligations.

Use extensionality with `⟨y, hy⟩`. Express the relevant statement in the definitionally equal form `Finsupp.mapDomain (Subtype.val : V → X) h ((⟨y, hy⟩ : V) : X) = h ⟨y, hy⟩`. Conclude with `Finsupp.mapDomain_apply Subtype.val_injective _ _`.
-/
theorem UpperTheory.V.KH.permSplit :
    ∀ (G X : Type) [Group G] [MulAction G X] (U V : SubMulAction G X), (∀ y, y ∈ V ↔ y ∉ U) →
      ∃ (f : permRep G U ⟶ permRep G X) (g : permRep G X ⟶ permRep G V),
        Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  intro G X _ _ U V hUV
  let F : (perm G U).IntertwiningMap (perm G X) :=
    { toLinearMap := Finsupp.lmapDomain ℤ ℤ (Subtype.val : U → X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        simp only [LinearMap.comp_apply, perm_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        congr 1 }
  let Gm : (perm G X).IntertwiningMap (perm G V) :=
    { toLinearMap := Finsupp.lsubtypeDomain (V : Set X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        ext ⟨y, hy⟩
        change (Finsupp.mapDomain (fun x => g • x) f) y =
          (Finsupp.mapDomain (fun v : V => g • v) (Finsupp.subtypeDomain (· ∈ V) f)) ⟨y, hy⟩
        have hy' : g⁻¹ • y ∈ V := V.smul_mem _ hy
        have e2 : (⟨y, hy⟩ : V) = g • (⟨g⁻¹ • y, hy'⟩ : V) := Subtype.ext (by simp)
        rw [e2, Finsupp.mapDomain_apply (MulAction.injective g), Finsupp.subtypeDomain_apply]
        have e1 : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
        conv_lhs => rw [e1]
        rw [Finsupp.mapDomain_apply (MulAction.injective g)] }
  refine ⟨Rep.ofHom F, Rep.ofHom Gm, ?_, ?_, ?_⟩
  · rw [Rep.hom_ofHom]
    change Function.Injective (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [Rep.hom_ofHom, Rep.hom_ofHom]
    intro y
    change Finsupp.subtypeDomain (· ∈ V) y = 0 ↔
      y ∈ Set.range (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    constructor
    · intro hy0
      refine ⟨Finsupp.subtypeDomain (· ∈ U) y, ?_⟩
      ext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : X) from rfl, Finsupp.mapDomain_apply Subtype.val_injective,
          Finsupp.subtypeDomain_apply]
      · rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨u, rfl⟩; exact hx u.2)]
        have hxV : x ∈ V := (hUV x).2 hx
        have h1 := DFunLike.congr_fun hy0 ⟨x, hxV⟩
        simp only [Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
        exact h1.symm
    · rintro ⟨u, rfl⟩
      ext ⟨x, hx⟩
      rw [Finsupp.subtypeDomain_apply, Finsupp.mapDomain_notin_range _ _ ?_]
      · simp
      · rintro ⟨w, rfl⟩
        exact ((hUV _).1 hx) w.2
  · rw [Rep.hom_ofHom]
    intro h
    refine ⟨Finsupp.mapDomain (Subtype.val : V → X) h, ?_⟩
    ext ⟨y, hy⟩
    change Finsupp.mapDomain (Subtype.val : V → X) h ((⟨y, hy⟩ : V) : X) = h ⟨y, hy⟩
    exact Finsupp.mapDomain_apply Subtype.val_injective _ _
