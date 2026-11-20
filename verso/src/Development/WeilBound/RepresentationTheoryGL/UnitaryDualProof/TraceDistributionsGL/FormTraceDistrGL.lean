import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory PositivityTheory.PfBern.Unit

namespace PositivityTheory.RgUd.AB.Pf

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

/- English proof (translation)
Use `LinearMap.ext fun v => LinearMap.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply, LinearMap.zero_apply]`. Distinguish the cases in `hv0 : v = 0`. Rewrite using `[hv0, map_zero, LinearMap.zero_apply]`. Distinguish the cases in `hu0 : u = 0`.

Rewrite using `[hu0, map_zero]`. Establish `hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G)` using `Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))`. Take `⟨K, hKc, hKU⟩` from `exists_openSubgroup_isCompact_subset hU`. Establish `hKo : IsOpen ((K : Subgroup G) : Set G)` using `K.isOpen`. Use `hρ.2 (K : Subgroup G) hKc hKo` as an intermediate fact.

Establish `hvW : v ∈ fixedVectors ρ (K : Subgroup G)`. Rewrite using `[mem_fixedVectors]`. Introduce `x hx`. Conclude with `(hKU hx).1`. Establish `huW : u ∈ fixedVectors ρ (K : Subgroup G)`.

Rewrite using `[mem_fixedVectors]`. Introduce `x hx`. Conclude with `(hKU hx).2`. Establish `hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥` using `fun hb => hv0 (by`. Use `hvW` as an intermediate fact.

Rewrite `this` using `[hb]`. Conclude with `(Submodule.mem_bot ℂ).1 this)`. Use `set W := fixedVectors ρ (K : Subgroup G)`. Set `vW : W` to `⟨v, hvW⟩`. Set `uW : W` to `⟨u, huW⟩`.

Set `φ : W →ₗ[ℂ] ℂ` to `(B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype`. Set `A : Module.End ℂ W` to `φ.smulRight vW`. Take `⟨r, hr⟩` from `level_density (μ := μ) hKc hKo hρ.1 hW A`. Set `rf : locallyConstantCompactSupport G ℂ ℂ` to `(r : HeckeAlgebra μ)`. Establish `hbi : BiInv (K : Subgroup G) (rf : G → ℂ)` using `fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x`.

Establish `hf` using `h rf rf.2`. Rewrite `hf` using `[formD_apply, hPr rf]`. Express the relevant statement in the definitionally equal form `DF μ hρ hpos C rf = 0 at hf`. Rewrite `hf` using `[DF_eq μ hρ hpos hinv C _ hKc hKo hbi]`. Establish `hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v`.

Introduce `x`. Establish `e` using `congrArg (fun T : Module.End ℂ W => (T x : V)) hr`. Rewrite using `[← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]`. Both sides reduce to the same expression. Establish `huu : (B₀ u u) ≠ 0` using `fun e => by`.

Use `hpos u hu0` as an intermediate fact. Rewrite `this` using `[e]`. Simplify using `at this`. Use `set N := rN μ hρ hpos hKc hKo C rf with hN`. Establish `sN` using `rN_spec μ hρ hpos hKc hKo C rf`.

Set `m : W` to `(B₀ u u)⁻¹ • N uW`. Establish `hm : ∀ y : W, B₀ (m : V) y = C v y`. Introduce `y`. Use `sN uW y` as an intermediate fact. Rewrite `this` using `[hres]`.

Use `show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y`. Rewrite using `[map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ huu, one_mul]`. Establish `hNe : N = φ.smulRight m`. Use `riesz_unique hpos sN fun x y => ?_` and prove the remaining obligations. Use `show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y`.

Rewrite using `[hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]`. Both sides reduce to the same expression. Unfold `DK at hf`. Rewrite `hf` using `[← hN, hNe, LinearMap.trace_smulRight]`. Establish `: φ m = C v u` using `hm uW`.

Rewrite using `[← this]`. Conclude with `hf`.
-/
theorem formD_faithful [ρ.IsIrreducible] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (C : Sesq V)
    (h : ∀ f ∈ testFn G, formD μ hρ hpos hinv Pr C f = 0) : C = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun u => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, LinearMap.zero_apply]
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have huW : u ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  set W := fixedVectors ρ (K : Subgroup G)
  let vW : W := ⟨v, hvW⟩
  let uW : W := ⟨u, huW⟩
  let φ : W →ₗ[ℂ] ℂ := (B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : Module.End ℂ W := φ.smulRight vW
  obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW A
  let rf : locallyConstantCompactSupport G ℂ ℂ := (r : HeckeAlgebra μ)
  have hbi : BiInv (K : Subgroup G) (rf : G → ℂ) := fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x
  have hf := h rf rf.2
  rw [formD_apply, hPr rf] at hf
  change DF μ hρ hpos C rf = 0 at hf
  rw [DF_eq μ hρ hpos hinv C _ hKc hKo hbi] at hf
  have hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v := by
    intro x
    have e := congrArg (fun T : Module.End ℂ W => (T x : V)) hr
    rw [← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]
    rfl
  have huu : (B₀ u u) ≠ 0 := fun e => by
    have := hpos u hu0
    rw [e] at this
    simp at this
  set N := rN μ hρ hpos hKc hKo C rf with hN
  have sN := rN_spec μ hρ hpos hKc hKo C rf
  let m : W := (B₀ u u)⁻¹ • N uW
  have hm : ∀ y : W, B₀ (m : V) y = C v y := by
    intro y
    have := sN uW y
    rw [hres] at this
    show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y
    rw [map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ huu, one_mul]
  have hNe : N = φ.smulRight m := by
    refine riesz_unique hpos sN fun x y => ?_
    show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y
    rw [hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]
    rfl
  unfold DK at hf
  rw [← hN, hNe, LinearMap.trace_smulRight] at hf
  have : φ m = C v u := hm uW
  rw [← this]
  exact hf

end Faith

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩`. Use `borelize (GL (Fin (n + 1)) k)`. Use `hirr` as an intermediate fact. Use `GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))` as an intermediate fact. Take `⟨Pr, hPr⟩` from `exists_testProj (G := GL (Fin (n + 1)) k)`.

Conclude with `⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf, fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩`.
-/
theorem formTraceDistrGL : FormTraceDistrGL k := by
  intro n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := GL (Fin (n + 1)) k)
  exact ⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf,
    fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩

/- English proof (translation)
Introduce `n D hD g f hf`. Establish `hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k))` using `⟨hf, Set.subset_univ _⟩`. Establish `hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)), D (fun x => f (p * x * p⁻¹)) = D f`. Introduce `p hp f hf`. Use `hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1` as an intermediate fact.

Establish `e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹)`. Use function extensionality and compare the values at `x`. Unfold `conjFn`. Rewrite using `[inv_inv]`. Rewrite using `[← e]`.

Conclude with `this`. Use `hA n D hP g⁻¹ f hf'` as an intermediate fact. Establish `e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹)`. Use function extensionality and compare the values at `x`. Unfold `conjFn`.

Rewrite using `[inv_inv]`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem theoremA_of_thmA (hA : PositivityTheory.RgUd.ThmA k) : TheoremA k := by
  intro n D hD g f hf
  have hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)) := ⟨hf, Set.subset_univ _⟩
  have hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)),
      D (fun x => f (p * x * p⁻¹)) = D f := by
    intro p hp f hf
    have := hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1
    have e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹) := by
      funext x; unfold conjFn; rw [inv_inv]
    rw [← e]; exact this
  have := hA n D hP g⁻¹ f hf'
  have e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹) := by
    funext x; unfold conjFn; rw [inv_inv]
  rw [e]; exact this

/- English proof (translation)
Introduce `n V _ _ π hs hirr B hB β hβ`. Establish `hadm : GroundTheory.Automorphic.IsAdmissible π` using `(PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)`. Take `⟨c, hc⟩` from `hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ`. Conclude with `⟨c, fun v w => by rw [hc]; rfl⟩`.
-/
theorem thmB_of_kirillov (hK : KirillovForm k) : PositivityTheory.RgUd.ThmB k := by
  intro n V _ _ π hs hirr B hB β hβ
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)
  obtain ⟨c, hc⟩ := hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ
  exact ⟨c, fun v w => by rw [hc]; rfl⟩

/- English proof (translation)
The claim follows from `thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))`.
-/
theorem thmB (hA : PositivityTheory.RgUd.ThmA k) : PositivityTheory.RgUd.ThmB k :=
  thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))

end PositivityTheory.RgUd.AB.Pf
