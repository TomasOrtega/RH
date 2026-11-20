import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω) (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)`. Establish `hg1 : g 1 = 1`. Use `LinearMap.congr_fun hg 1` as an intermediate fact. Simplify using `using this`. Set `m : Ω ⊗[L] Ω →ₗ[L] Ω` to `TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id`.

Establish `e` using `congrArg m h`. Simplify using `only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1, one_smul, LinearEquiv.coe_coe] at e`. Conclude with `⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩`.
-/
theorem mem_range_of_tmul_eq {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (x : Ω)
    (h : x ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] x) : x ∈ (algebraMap L Ω).range := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  let m : Ω ⊗[L] Ω →ₗ[L] Ω := TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id
  have e := congrArg m h
  simp only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1,
    one_smul, LinearEquiv.coe_coe] at e
  exact ⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩

/- English proof (translation)
Set `_` to `fn.toAlgebra`. Establish `e : CommRingCat.ofHom β ≫ CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) = CommRingCat.ofHom β ≫ CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst)`. Use extensionality with `o`. Establish `ho : cst (β o) = algebraMap Ω₀ Ω (a o)`. Rewrite using `[RingHom.algebraMap_toAlgebra]`.

Conclude with `(RingHom.congr_fun h o).symm`. Express the relevant statement in the definitionally equal form `cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)`. Rewrite using `[ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]`. Establish `e2` using `hβ.left_cancellation _ _ e`. Establish `key : ∀ u : F, ∃ w : Ω₀, fn w = cst u`.

Introduce `u`. Establish `hu` using `RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u`. Express the relevant statement in the definitionally equal form `cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu`. Take `⟨w, hw⟩` from `mem_range_of_tmul_eq (L := Ω₀) (cst u) hu`. Conclude with `⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩`.

Use `choose g hg using key`. Establish `inj` using `fn.injective`. Use `⟨{ toFun := g map_one' := inj (by rw [hg, map_one, map_one]) map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg]) map_zero' := inj (by rw [hg, map_zero, map_zero]) map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }, ?_⟩` and prove the remaining obligations. Use extensionality with `o`. Apply `inj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `fn (g (β o)) = fn (a o)`. Rewrite using `[hg]`. Conclude with `(RingHom.congr_fun h o).symm`.
-/
theorem factor_of_epi {O F Ω₀ Ω : Type} [CommRing O] [Field F] [Field Ω₀] [Field Ω]
    (β : O →+* F) (hβ : Epi (CommRingCat.ofHom β)) (a : O →+* Ω₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (h : fn.comp a = cst.comp β) : ∃ a' : F →+* Ω₀, a'.comp β = a := by
  let _ := fn.toAlgebra
  have e : CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) =
      CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst) := by
    ext o
    have ho : cst (β o) = algebraMap Ω₀ Ω (a o) := by
      rw [RingHom.algebraMap_toAlgebra]; exact (RingHom.congr_fun h o).symm
    change cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)
    rw [ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have e2 := hβ.left_cancellation _ _ e
  have key : ∀ u : F, ∃ w : Ω₀, fn w = cst u := by
    intro u
    have hu := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u
    change cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu
    obtain ⟨w, hw⟩ := mem_range_of_tmul_eq (L := Ω₀) (cst u) hu
    exact ⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩
  choose g hg using key
  have inj := fn.injective
  refine ⟨{ toFun := g
            map_one' := inj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := inj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }, ?_⟩
  ext o
  apply inj
  change fn (g (β o)) = fn (a o)
  rw [hg]
  exact (RingHom.congr_fun h o).symm

/- English proof (translation)
Establish `hf : IsField (X.presheaf.stalk (genPt ξ))` using `(RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)`. Establish `: y ∈ Set.range (X.fromSpecStalk (genPt ξ))` using `by rwa [Scheme.range_fromSpecStalk]`. Take `⟨q, rfl⟩` from `this`. Set `_` to `hf.toField`. Establish `: q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ))` using `Subsingleton.elim (α := PrimeSpectrum _) _ _`.

Rewrite using `[this, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem eq_genPt_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, rfl⟩ := this
  let _ := hf.toField
  have : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

/- English proof (translation)
Establish `hCi : IsIrreducible (irreducibleComponent y)` using `isIrreducible_irreducibleComponent`. Establish `hCc : IsClosed (irreducibleComponent y)` using `isClosed_irreducibleComponent`. Establish `hgen` using `hCi.isGenericPoint_genericPoint_closure`. Rewrite `hgen` using `[hCc.closure_eq]`. Establish `hη : hCi.genericPoint = y` using `hy _ (hgen.specializes mem_irreducibleComponent)`.

Rewrite `hgen` using `[hη]`. Establish `hmax` using `irreducibleComponent_mem_irreducibleComponents y`. Use `set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD`. Establish `hDc : IsClosed D`. Rewrite using `[hD, Set.sUnion_eq_biUnion]`.

Conclude with `Set.Finite.isClosed_biUnion (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset) fun C hC => isClosed_of_mem_irreducibleComponents C hC.1`. Establish `hyD : y ∉ D`. Introduce and unpack `⟨C, ⟨hC, hne⟩, hyC⟩`. Establish `hle : irreducibleComponent y ⊆ C`. Rewrite using `[← hgen.def]`.

Conclude with `(isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)`. Conclude with `hne (le_antisymm (hmax.2 hC.1 hle) hle)`. Take `⟨u, huD, huU⟩` from `hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩`. Establish `huC : u ∈ irreducibleComponent y`. Assume the negation of the conclusion as `hne`.

Use `huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩, mem_irreducibleComponent⟩` and prove the remaining obligations. Introduce `e`. Conclude with `hne (by`. Establish `: u ∈ irreducibleComponent u` using `mem_irreducibleComponent`. Rewrite `this` using `[Set.mem_singleton_iff.1 e]`.

Conclude with `this)`. Conclude with `(hgen.specializes huC).mem_open hU huU`.
-/
theorem mem_of_dense_of_noGen {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `hs`. Use `isProper_str O N` as an intermediate fact. Establish `: IsProper (i ≫ PSpace.str O N)` using `inferInstance`. Establish `hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β))` using `inferInstance`. Establish `hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β))` using `inferInstance`.

Establish `: IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)`. Establish `: CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β))` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)`. Establish `: IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β))` using `{}`. Use `infer_instance`.
-/
theorem noetherianSpace_baseChange {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono`. Establish `hepi : Epi (CommRingCat.ofHom β)`. Establish `h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op)` using `hmono`. Establish `h2 : Mono (CommRingCat.ofHom β).op` using `Scheme.Spec.mono_of_mono_map h1`. Conclude with `unop_epi_of_mono (CommRingCat.ofHom β).op`.

Set `a : O →+* A.Ω₀` to `(Spec.preimage (A.ξ₀ ≫ Y.s)).hom`. Establish `ha : spMap a = A.ξ₀ ≫ Y.s`. Simplify using `only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hfa : A.fn.comp a = A.cst.comp β`. Establish `h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β)`.

Rewrite using `[← A.cst_over]`. Establish `hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀` using `A.fn_over`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.

Use `_ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]`. Establish `h2` using `Spec.map_injective h1`. Conclude with `congrArg CommRingCat.Hom.hom h2`. Take `⟨a', ha'⟩` from `factor_of_epi β hepi a A.fn A.cst hfa`. Establish `hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β`.

Rewrite using `[← ha, ← ha']`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β)` to `pullback.lift A.ξ₀ (spMap a') hsq`. Establish `hz : z ≫ pullback.fst _ _ = A.ξ₀` using `pullback.lift_fst _ _ _`.

Set `y0 : ↥(pullback Y.s (spMap β))` to `z (IsLocalRing.closedPoint A.Ω₀)`. Establish `hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀` using `by show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _`. Rewrite using `[← hz]`. Both sides reduce to the same expression. Establish `hmax : ∀ y', y' ⤳ y0 → y' = y0`.

Introduce `y' hy`. Establish `h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀` using `hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous`. Establish `h2` using `eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1`. Conclude with `(pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)`. Use `noetherianSpace_baseChange Y.proj β` as an intermediate fact.

Use `Y.jQ_open` as an intermediate fact. Establish `hy0 : y0 ∈ Set.range Y.jQ` using `mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax`. Establish `hrange : Set.range z ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `: p = IsLocalRing.closedPoint A.Ω₀` using `Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _`.

Rewrite using `[this]`. Conclude with `hy0`. Use `⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩` and prove the remaining obligations. Use `show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, hz]`.
-/
theorem gen_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y),
    Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono
  have hepi : Epi (CommRingCat.ofHom β) := by
    have h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := hmono
    have h2 : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h1
    exact unop_epi_of_mono (CommRingCat.ofHom β).op
  let a : O →+* A.Ω₀ := (Spec.preimage (A.ξ₀ ≫ Y.s)).hom
  have ha : spMap a = A.ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : A.fn.comp a = A.cst.comp β := by
    have h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β) := by
      rw [← A.cst_over]
      have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
      calc spMap (A.fn.comp a) = spMap A.fn ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨a', ha'⟩ := factor_of_epi β hepi a A.fn A.cst hfa
  have hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β := by
    rw [← ha, ← ha']
    simp only [spMap, ← Spec.map_comp]; rfl
  let z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β) := pullback.lift A.ξ₀ (spMap a') hsq
  have hz : z ≫ pullback.fst _ _ = A.ξ₀ := pullback.lift_fst _ _ _
  let y0 : ↥(pullback Y.s (spMap β)) := z (IsLocalRing.closedPoint A.Ω₀)
  have hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀ := by
    show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _
    rw [← hz]
    rfl
  have hmax : ∀ y', y' ⤳ y0 → y' = y0 := by
    intro y' hy
    have h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀ := hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous
    have h2 := eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1
    exact (pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)
  have := noetherianSpace_baseChange Y.proj β
  have := Y.jQ_open
  have hy0 : y0 ∈ Set.range Y.jQ :=
    mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax
  have hrange : Set.range z ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint A.Ω₀ := Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _
    rw [this]
    exact hy0
  refine ⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩
  show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hz]

end GlobalTheory.CompanionTheory.Ar.GenOpen
