import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf

variable {W Y : Scheme.{u}}

/- English proof (translation)
Set `_ : Algebra R S` to `φ.toAlgebra`. Establish `: Module.Flat R S` using `hφ`. Establish `halg : (algebraMap R S) = φ` using `rfl`. Establish `hex : Function.Exact (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L)) ((L.mkQ).comp (LinearMap.lsmul R R a))`. Rewrite using `[LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]`.

Establish `hex2` using `Module.Flat.lTensor_exact (M := S) hex`. Establish `key : ∀ s : S, s ∈ L.map φ → s ⊗ₜ[R] (L.mkQ (1 : R)) = 0`. Introduce `s hs`. Set `ψ : S →ₗ[S] S ⊗[R] (R ⧸ L)` to `{ toFun := fun t => t ⊗ₜ[R] (L.mkQ (1 : R)) map_add' := fun x y => TensorProduct.add_tmul x y _ map_smul' := fun c x => TensorProduct.smul_tmul' c x _ }`. Establish `hψ : ∀ t : S, ψ t = t ⊗ₜ[R] (L.mkQ (1 : R))` using `fun _ => rfl`.

Establish `hsub : L.map φ ≤ LinearMap.ker ψ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `l hl`. Establish `h0 : l • (L.mkQ (1 : R)) = 0`. Rewrite using `[← map_smul]`.

Simplify using `only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]`. Conclude with `hl`. Simplify using `only [Ideal.mem_comap, LinearMap.mem_ker, hψ]`. Rewrite using `[show φ l = l • (1 : S) from by rw [Algebra.smul_def, halg, mul_one], TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]`. Establish `hker` using `LinearMap.mem_ker.mp (hsub hs)`.

Rewrite `hker` using `[hψ]`. Then use the resulting hypothesis. Establish `hzero : (LinearMap.lTensor S ((L.mkQ).comp (LinearMap.lsmul R R a))) ((1 : S) ⊗ₜ[R] (1 : R)) = 0`. Rewrite using `[LinearMap.lTensor_tmul]`. Use `show (1 : S) ⊗ₜ[R] (L.mkQ (a * (1 : R))) = 0`. Rewrite using `[mul_one]`.

Establish `h1 : (L.mkQ a) = a • (L.mkQ (1 : R))`. Rewrite using `[← map_smul]`. Simplify using the standard rewrite rules. Rewrite using `[h1, ← TensorProduct.smul_tmul, show a • (1 : S) = φ a from by rw [Algebra.smul_def, halg, mul_one]]`. Conclude with `key _ h`.

Take `⟨v, hv⟩` from `(hex2 ((1 : S) ⊗ₜ[R] (1 : R))).mp hzero`. Establish `hrange : ∀ u : S ⊗[R] (Submodule.comap (LinearMap.lsmul R R a) L), (TensorProduct.rid R S) (LinearMap.lTensor S (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L)) u) ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L)`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul s c`. Rewrite using `[LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, halg]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ c.2)`. Consider the case `add u₁ u₂ h₁ h₂`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ h₁ h₂`. Establish `hfin` using `hrange v`. Rewrite `hfin` using `[hv, TensorProduct.rid_tmul, one_smul]`. Conclude with `hfin`.
-/
private theorem one_mem_map_colon_of_mem_map {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.Flat φ) (L : Ideal R) (a : R) (h : φ a ∈ L.map φ) :
    (1 : S) ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have halg : (algebraMap R S) = φ := rfl
  have hex : Function.Exact (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L))
      ((L.mkQ).comp (LinearMap.lsmul R R a)) := by
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
  have hex2 := Module.Flat.lTensor_exact (M := S) hex
  have key : ∀ s : S, s ∈ L.map φ → s ⊗ₜ[R] (L.mkQ (1 : R)) = 0 := by
    intro s hs
    let ψ : S →ₗ[S] S ⊗[R] (R ⧸ L) :=
      { toFun := fun t => t ⊗ₜ[R] (L.mkQ (1 : R))
        map_add' := fun x y => TensorProduct.add_tmul x y _
        map_smul' := fun c x => TensorProduct.smul_tmul' c x _ }
    have hψ : ∀ t : S, ψ t = t ⊗ₜ[R] (L.mkQ (1 : R)) := fun _ => rfl
    have hsub : L.map φ ≤ LinearMap.ker ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro l hl
      have h0 : l • (L.mkQ (1 : R)) = 0 := by
        rw [← map_smul]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]
        exact hl
      simp only [Ideal.mem_comap, LinearMap.mem_ker, hψ]
      rw [show φ l = l • (1 : S) from by rw [Algebra.smul_def, halg, mul_one],
        TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]
    have hker := LinearMap.mem_ker.mp (hsub hs)
    rwa [hψ] at hker
  have hzero : (LinearMap.lTensor S ((L.mkQ).comp (LinearMap.lsmul R R a)))
      ((1 : S) ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    show (1 : S) ⊗ₜ[R] (L.mkQ (a * (1 : R))) = 0
    rw [mul_one]
    have h1 : (L.mkQ a) = a • (L.mkQ (1 : R)) := by
      rw [← map_smul]; simp
    rw [h1, ← TensorProduct.smul_tmul,
      show a • (1 : S) = φ a from by rw [Algebra.smul_def, halg, mul_one]]
    exact key _ h
  obtain ⟨v, hv⟩ := (hex2 ((1 : S) ⊗ₜ[R] (1 : R))).mp hzero
  have hrange : ∀ u : S ⊗[R] (Submodule.comap (LinearMap.lsmul R R a) L),
      (TensorProduct.rid R S) (LinearMap.lTensor S
        (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L)) u)
      ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s c =>
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, halg]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ c.2)
    | add u₁ u₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ h₁ h₂
  have hfin := hrange v
  rw [hv, TensorProduct.rid_tmul, one_smul] at hfin
  exact hfin

/- English proof (translation)
Take `⟨m, hm, hCm⟩` from `C.exists_le_maximal hC`. Set `p : PrimeSpectrum Γ(X, U)` to `⟨m, hm.isPrime⟩`. Use `⟨hU.fromSpec.base p, ?_, ?_⟩` and prove the remaining obligations. Establish `hr : hU.fromSpec.base p ∈ Set.range hU.fromSpec.base` using `⟨p, rfl⟩`. Rewrite `hr` using `[hU.range_fromSpec]`.

Conclude with `hr`. Introduce `c hc hmem`. Establish `h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c` using `hmem`. Rewrite `h1` using `[hU.fromSpec_preimage_basicOpen]`. Establish `h2 : c ∉ m` using `h1`.

Conclude with `h2 (hCm hc)`.
-/
private theorem exists_not_mem_basicOpen_of_ne_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (C : Ideal Γ(X, U)) (hC : C ≠ ⊤) :
    ∃ x ∈ U, ∀ c ∈ C, x ∉ X.basicOpen c := by
  obtain ⟨m, hm, hCm⟩ := C.exists_le_maximal hC
  let p : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
  refine ⟨hU.fromSpec.base p, ?_, ?_⟩
  · have hr : hU.fromSpec.base p ∈ Set.range hU.fromSpec.base := ⟨p, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  · intro c hc hmem
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c := hmem
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∉ m := h1
    exact h2 (hCm hc)

/- English proof (translation)
Establish `hxr : x ∈ Set.range hU.fromSpec.base`. Rewrite using `[hU.range_fromSpec]`. Conclude with `hx`. Take `⟨p, hp⟩` from `hxr`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hsub : s ⊆ (p.asIdeal : Set Γ(X, U))`. Introduce `c hcs`. Establish `h1 : ¬ (p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c)`. Introduce `hmem`.

Conclude with `hcon c hcs (by rw [← hp]; exact hmem)`. Rewrite `h1` using `[hU.fromSpec_preimage_basicOpen]`. Establish `h2 : c ∈ p.asIdeal`. Assume the negation of the conclusion as `hcc`. Conclude with `h1 hcc`.

Simplify using `using h2`. Establish `hle` using `Ideal.span_le.mpr hsub`. Rewrite `hle` using `[hs]`. Conclude with `p.2.ne_top (top_le_iff.mp hle)`.
-/
private theorem exists_mem_basicOpen_of_span_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) (x : X) (hx : x ∈ U) :
    ∃ c ∈ s, x ∈ X.basicOpen c := by
  have hxr : x ∈ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact hx
  obtain ⟨p, hp⟩ := hxr
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ (p.asIdeal : Set Γ(X, U)) := by
    intro c hcs
    have h1 : ¬ (p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c) := by
      intro hmem
      exact hcon c hcs (by rw [← hp]; exact hmem)
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∈ p.asIdeal := by
      by_contra hcc
      exact h1 hcc
    simpa using h2
  have hle := Ideal.span_le.mpr hsub
  rw [hs] at hle
  exact p.2.ne_top (top_le_iff.mp hle)

/- English proof (translation)
Apply `AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat)` to reduce the goal to its premises. Apply the tactic sequence `all_goals assumption`.
-/
private theorem flat_appLE (g : W ⟶ Y) [AlgebraicGeometry.Flat g] (U : Y.affineOpens)
    (V : W.affineOpens) (e : (V : W.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) :
    RingHom.Flat (g.appLE (U : Y.Opens) (V : W.Opens) e).hom := by
  apply AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat)
  all_goals assumption

/- English proof (translation)
Assume the negation of the conclusion as `hCtop`. Take `⟨x, hxU, hx⟩` from `exists_not_mem_basicOpen_of_ne_top U.2 C hCtop`. Take `⟨w, hw⟩` from `AlgebraicGeometry.Surjective.surj (f := g) x`. Establish `hwU : w ∈ g ⁻¹ᵁ (U : Y.Opens)` using `by show g.base w ∈ (U : Y.Opens)`. Rewrite using `[hw]`.

Conclude with `hxU`. Take `⟨V, hV, hwV, hVU⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hwU`. Establish `hV' : IsAffineOpen V` using `hV`. Establish `hcomap0` using `Scheme.IdealSheafData.le_def.mp h ⟨V, hV'⟩`. Rewrite `hcomap0` using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U ⟨V, hV'⟩ hVU, Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U ⟨V, hV'⟩ hVU]`.

Establish `hcomap : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (I.ideal U) ≤ Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (J.ideal U)` using `hcomap0`. Establish `hflat : RingHom.Flat (g.appLE (U : Y.Opens) V hVU).hom` using `flat_appLE g U ⟨V, hV'⟩ hVU`. Establish `hone` using `one_mem_map_colon_of_mem_map (g.appLE (U : Y.Opens) V hVU).hom hflat (J.ideal U) a (hcomap (Ideal.mem_map_of_mem _ ha))`. Rewrite `hone` using `[← hCdef]`. Establish `htop : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom C = ⊤` using `(Ideal.eq_top_iff_one _).mpr hone`.

Establish `hspan : Ideal.span (((g.appLE (U : Y.Opens) V hVU).hom) '' (C : Set Γ(Y, (U : Y.Opens)))) = ⊤`. Rewrite using `[← Ideal.map_span, Ideal.span_eq]`. Conclude with `htop`. Take `⟨f, hf, hwf⟩` from `exists_mem_basicOpen_of_span_eq_top hV' _ hspan w hwV`. Take `⟨c, hc, hcf⟩` from `hf`.

Establish `hwb : w ∈ W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c)`. Rewrite using `[hcf]`. Conclude with `hwf`. Establish `hbeta : W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) ≤ g ⁻¹ᵁ (Y.basicOpen c)`. Rewrite using `[Scheme.preimage_basicOpen]`.

Simplify using `[Scheme.Hom.appLE]`. Establish `hmem` using `hbeta hwb`. Conclude with `hx c hc (by rw [← hw]; exact hmem)`.
-/
private theorem colon_eq_top_of_comap_le (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g ≤ J.comap g) (U : Y.affineOpens) (a : Γ(Y, (U : Y.Opens)))
    (ha : a ∈ I.ideal U) (C : Ideal Γ(Y, (U : Y.Opens)))
    (hCdef : C = Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U)) :
    C = ⊤ := by
  by_contra hCtop
  obtain ⟨x, hxU, hx⟩ := exists_not_mem_basicOpen_of_ne_top U.2 C hCtop
  obtain ⟨w, hw⟩ := AlgebraicGeometry.Surjective.surj (f := g) x
  have hwU : w ∈ g ⁻¹ᵁ (U : Y.Opens) := by
    show g.base w ∈ (U : Y.Opens)
    rw [hw]; exact hxU
  obtain ⟨V, hV, hwV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hwU
  have hV' : IsAffineOpen V := hV
  have hcomap0 := Scheme.IdealSheafData.le_def.mp h ⟨V, hV'⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U ⟨V, hV'⟩ hVU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U ⟨V, hV'⟩ hVU] at hcomap0
  have hcomap : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (I.ideal U) ≤
      Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (J.ideal U) := hcomap0
  have hflat : RingHom.Flat (g.appLE (U : Y.Opens) V hVU).hom := flat_appLE g U ⟨V, hV'⟩ hVU
  have hone := one_mem_map_colon_of_mem_map (g.appLE (U : Y.Opens) V hVU).hom hflat (J.ideal U) a
    (hcomap (Ideal.mem_map_of_mem _ ha))
  rw [← hCdef] at hone
  have htop : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom C = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr hone
  have hspan : Ideal.span (((g.appLE (U : Y.Opens) V hVU).hom) ''
      (C : Set Γ(Y, (U : Y.Opens)))) = ⊤ := by
    rw [← Ideal.map_span, Ideal.span_eq]
    exact htop
  obtain ⟨f, hf, hwf⟩ := exists_mem_basicOpen_of_span_eq_top hV' _ hspan w hwV
  obtain ⟨c, hc, hcf⟩ := hf
  have hwb : w ∈ W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) := by
    rw [hcf]; exact hwf
  have hbeta : W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) ≤ g ⁻¹ᵁ (Y.basicOpen c) := by
    rw [Scheme.preimage_basicOpen]
    simp [Scheme.Hom.appLE]
  have hmem := hbeta hwb
  exact hx c hc (by rw [← hw]; exact hmem)

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.le_def]`. Introduce `U a ha`. Establish `hC` using `colon_eq_top_of_comap_le g I J h U a ha _ rfl`. Establish `h1 : (1 : Γ(Y, (U : Y.Opens))) ∈ Submodule.comap (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U)`. Rewrite using `[hC]`.

Conclude with `Submodule.mem_top`. Establish `h2 : a * (1 : Γ(Y, (U : Y.Opens))) ∈ J.ideal U` using `h1`. Simplify using `using h2`.
-/
theorem le_of_comap_le (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g ≤ J.comap g) : I ≤ J := by
  rw [Scheme.IdealSheafData.le_def]
  intro U a ha
  have hC := colon_eq_top_of_comap_le g I J h U a ha _ rfl
  have h1 : (1 : Γ(Y, (U : Y.Opens))) ∈ Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U) := by
    rw [hC]; exact Submodule.mem_top
  have h2 : a * (1 : Γ(Y, (U : Y.Opens))) ∈ J.ideal U := h1
  simpa using h2

/- English proof (translation)
The claim follows from `le_antisymm (le_of_comap_le g I J (le_of_eq h)) (le_of_comap_le g J I (le_of_eq h.symm))`.
-/
theorem eq_of_comap_eq (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g = J.comap g) : I = J :=
  le_antisymm (le_of_comap_le g I J (le_of_eq h)) (le_of_comap_le g J I (le_of_eq h.symm))

end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
