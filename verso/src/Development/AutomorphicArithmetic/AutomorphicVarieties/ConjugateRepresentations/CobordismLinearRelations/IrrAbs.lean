import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Use `haveI := IsSemisimpleModule.range Φ`. Use `haveI : IsSemisimpleModule R M := IsSemisimpleModule.congr (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)).symm`. Set `e : W →ₗ[R] (ι → M)` to `LinearMap.pi p`. Establish `he : Function.Injective e`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `w hw`. Conclude with `hp w fun i => congrFun hw i`. Use `haveI : IsSemisimpleModule R W := IsSemisimpleModule.of_injective e he`. Use `haveI : Nontrivial W := ⟨⟨x, 0, hx⟩⟩`. Take `⟨N, hN⟩` from `IsSemisimpleModule.exists_simple_submodule R W`.

Use `haveI := hN`. Use `haveI := IsSimpleModule.nontrivial R N`. Take `⟨y, hy⟩` from `exists_ne (0 : N)`. Establish `hex : ∃ i, p i (y : W) ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hy (Subtype.ext (hp _ h))`. Take `⟨i, hi⟩` from `hex`. Set `g : N →ₗ[R] M` to `(p i).comp N.subtype`. Establish `hg : Function.Injective g`.

Break down `g.injective_or_eq_zero with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (LinearMap.congr_fun h y) hi`. Take `⟨r, hr⟩` from `IsSemisimpleModule.extension_property g hg LinearMap.id`. Establish `hrΦ : r.comp Φ ≠ 0`.

Take `⟨z, hz⟩` from `hs (g y)`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Establish `h1` using `LinearMap.congr_fun h z`. Establish `h2` using `LinearMap.congr_fun hr y`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2`. Rewrite `h1` using `[hz]`. Rewrite using `[← h2, h1]`. Establish `hex2 : ∃ k, (r.comp Φ).comp (Finsupp.lsingle k) ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hrΦ` to reduce the goal to its premises. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `a b`. Simplify using `using LinearMap.congr_fun (h a) b`.

Take `⟨k, hk⟩` from `hex2`. Establish `hf0 : Function.Injective ((r.comp Φ).comp (Finsupp.lsingle k))` using `(LinearMap.injective_or_eq_zero _).resolve_right hk`. Conclude with `⟨N.subtype.comp ((r.comp Φ).comp (Finsupp.lsingle k)), N.injective_subtype.comp hf0⟩`.
-/
private theorem irrAbs_module {R M S W κ ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup W] [Module R W] [IsSimpleModule R S] [Finite ι] (Φ : (κ →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ)
    (p : ι → W →ₗ[R] M) (hp : ∀ w, (∀ i, p i w = 0) → w = 0) (x : W) (hx : x ≠ 0) :
    ∃ f : S →ₗ[R] W, Function.Injective f := by
  haveI := IsSemisimpleModule.range Φ
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)).symm
  let e : W →ₗ[R] (ι → M) := LinearMap.pi p
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hp w fun i => congrFun hw i
  haveI : IsSemisimpleModule R W := IsSemisimpleModule.of_injective e he
  haveI : Nontrivial W := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨N, hN⟩ := IsSemisimpleModule.exists_simple_submodule R W
  haveI := hN
  haveI := IsSimpleModule.nontrivial R N
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  have hex : ∃ i, p i (y : W) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (Subtype.ext (hp _ h))
  obtain ⟨i, hi⟩ := hex
  let g : N →ₗ[R] M := (p i).comp N.subtype
  have hg : Function.Injective g := by
    rcases g.injective_or_eq_zero with h | h
    · exact h
    · exact absurd (LinearMap.congr_fun h y) hi
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property g hg LinearMap.id
  have hrΦ : r.comp Φ ≠ 0 := by
    obtain ⟨z, hz⟩ := hs (g y)
    intro h
    apply hy
    have h1 := LinearMap.congr_fun h z
    have h2 := LinearMap.congr_fun hr y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2
    rw [hz] at h1
    rw [← h2, h1]
  have hex2 : ∃ k, (r.comp Φ).comp (Finsupp.lsingle k) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hrΦ
    apply Finsupp.lhom_ext
    intro a b
    simpa using LinearMap.congr_fun (h a) b
  obtain ⟨k, hk⟩ := hex2
  have hf0 : Function.Injective ((r.comp Φ).comp (Finsupp.lsingle k)) :=
    (LinearMap.injective_or_eq_zero _).resolve_right hk
  exact ⟨N.subtype.comp ((r.comp Φ).comp (Finsupp.lsingle k)), N.injective_subtype.comp hf0⟩

/- English proof (translation)
Introduce `G S V W ι _ _ _ _ _ _ _ _ _ ρS ρV ρW hirr hsup p hp hsep`. Set `F : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)} → (ρS.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule)` to `fun f => Representation.IntertwiningMap.equivLinearMapAsModule ρS ρV ((f.1).intertwiningMap_of_isIntertwiningMap ρS ρV f.2)`. Set `Φ` to `Finsupp.lsum ℕ F`. Establish `key : ∀ u : V, u ∈ (⨆ f : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)}, LinearMap.range f.1) → ∃ z, Φ z = (show ρV.asModule from u)`. Introduce `u hu`.

Use `Submodule.iSup_induction (motive := fun u : V => ∃ z, Φ z = (show ρV.asModule from u)) _ hu ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `f u ⟨s, rfl⟩`. Conclude with `⟨Finsupp.single f s, Finsupp.lsum_single ℕ F f s⟩`. Conclude with `⟨0, map_zero Φ⟩`. Introduce and unpack `a b ⟨za, ha⟩ ⟨zb, hb⟩`.

Conclude with `⟨za + zb, by rw [map_add, ha, hb]; rfl⟩`. Establish `hΦ : Function.Surjective Φ`. Introduce `v`. Conclude with `key v (by rw [hsup]; exact Submodule.mem_top)`. Set `P : ι → (ρW.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule)` to `fun i => Representation.IntertwiningMap.equivLinearMapAsModule ρW ρV ((p i).intertwiningMap_of_isIntertwiningMap ρW ρV (hp i))`.

Establish `hP : ∀ w : ρW.asModule, (∀ i, P i w = 0) → w = 0` using `fun w h => hsep w h`. Take `⟨x, hx⟩` from `exists_ne (0 : W)`. Use `haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρS.asModule := (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hirr`. Take `⟨f, hf⟩` from `irrAbs_module Φ hΦ P hP (show ρW.asModule from x) hx`. Set `f'` to `(Representation.IntertwiningMap.equivLinearMapAsModule ρS ρW).symm f`.

Conclude with `⟨f'.toLinearMap, hf, fun g v => f'.isIntertwining ρS ρW g v⟩`.
-/
theorem UpperTheory.V.Cj.irrAbs :
    UpperTheory.V.Cj.IrrAbs := by
  intro G S V W ι _ _ _ _ _ _ _ _ _ ρS ρV ρW hirr hsup p hp hsep
  classical
  let F : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)} →
      (ρS.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρS ρV
      ((f.1).intertwiningMap_of_isIntertwiningMap ρS ρV f.2)
  let Φ := Finsupp.lsum ℕ F
  have key : ∀ u : V, u ∈ (⨆ f : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)},
      LinearMap.range f.1) → ∃ z, Φ z = (show ρV.asModule from u) := by
    intro u hu
    refine Submodule.iSup_induction (motive := fun u : V => ∃ z, Φ z = (show ρV.asModule from u)) _ hu ?_ ?_ ?_
    · rintro f u ⟨s, rfl⟩
      exact ⟨Finsupp.single f s, Finsupp.lsum_single ℕ F f s⟩
    · exact ⟨0, map_zero Φ⟩
    · rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
      exact ⟨za + zb, by rw [map_add, ha, hb]; rfl⟩
  have hΦ : Function.Surjective Φ := by
    intro v
    exact key v (by rw [hsup]; exact Submodule.mem_top)
  let P : ι → (ρW.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρW ρV
      ((p i).intertwiningMap_of_isIntertwiningMap ρW ρV (hp i))
  have hP : ∀ w : ρW.asModule, (∀ i, P i w = 0) → w = 0 := fun w h => hsep w h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρS.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hirr
  obtain ⟨f, hf⟩ := irrAbs_module Φ hΦ P hP (show ρW.asModule from x) hx
  let f' := (Representation.IntertwiningMap.equivLinearMapAsModule ρS ρW).symm f
  exact ⟨f'.toLinearMap, hf, fun g v => f'.isIntertwining ρS ρW g v⟩
