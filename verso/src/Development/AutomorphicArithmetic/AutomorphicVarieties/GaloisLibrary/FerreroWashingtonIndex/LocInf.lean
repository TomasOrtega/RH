import GroundTheory.GlobalFields.HasseNorm
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `K _ _ _ x hx v`. Take `⟨W, rfl⟩` from `InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v`. Use `set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def`. Establish `hWu : W.LiesOver u` using `{ comp_eq := rfl }`. Establish `hu : u.IsReal` using `IsTotallyReal.isReal u`.

Establish `hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K))`. Establish `h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) = InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K)` using `by simp`. Rewrite using `[h0]`. Establish `h1` using `InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)`. Establish `h3` using `hx W.embedding`.

Break down `InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2` into its components or cases. Establish `h4` using `congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2`. Simplify using `only [RingHom.coe_comp, Function.comp_apply] at h4`. Rewrite `h3` using `[h4, ← h1]`. Rewrite `h3` using `[Complex.ofReal_re]`. Then use the resulting hypothesis.

Establish `h4` using `congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h4`. Rewrite `h3` using `[h4, ← h1]`. Rewrite `h3` using `[Complex.ofReal_re]`. Then use the resulting hypothesis. Use `letI : Algebra u.Completion W.Completion := NumberField.LiesOver.completionMap.toAlgebra`.

Use `set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he`. Use `set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha`. Use `set d := Module.finrank u.Completion W.Completion with hd_def`. Establish `hd : 0 < d`. Break down `W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h` into its components or cases.

Rewrite using `[hd_def, h.finrank_eq_one u]`. Evaluate the numerical expressions. Rewrite using `[hd_def, h.finrank_eq_two u]`. Evaluate the numerical expressions. Use `set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def`.

Establish `hr : r ^ d = a`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le, inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]`. Establish `ha0 : a ≠ 0`. Rewrite using `[ha]`.

Conclude with `(map_ne_zero _).mpr x.ne_zero`. Establish `hr0 : algebraMap u.Completion W.Completion r ≠ 0`. Rewrite using `[map_ne_zero]`. Introduce and unpack `h0`. Rewrite `hr` using `[h0, zero_pow hd.ne']`.

Conclude with `ha0 hr.symm`. Set `w0 : ↑(InfinitePlace.placesOver K u)` to `⟨W, hWu⟩`. Use `⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]`.

Rewrite using `[Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]), Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]`. Express the relevant statement in the definitionally equal form `Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a`. Rewrite using `[Algebra.norm_algebraMap, ← hd_def, hr]`.
-/
theorem UpperTheory.V.FW.locInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ), (∀ φ : K →+* ℂ, 0 < (φ (algebraMap (maximalRealSubfield K) K x)).re) → ∀ v, GroundTheory.Global.IdeleGroup.infiniteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.infiniteLocalNorm K v).range := by
  intro K _ _ _ x hx v
  classical
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v
  set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def
  have hWu : W.LiesOver u := { comp_eq := rfl }
  have hu : u.IsReal := IsTotallyReal.isReal u
  have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu
      (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) := by
    have h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) =
        InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K) := by simp
    rw [h0]
    have h1 := InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)
    have h3 := hx W.embedding
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_re] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
  letI : Algebra u.Completion W.Completion := NumberField.LiesOver.completionMap.toAlgebra
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
  set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha
  set d := Module.finrank u.Completion W.Completion with hd_def
  have hd : 0 < d := by
    rcases W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h
    · rw [hd_def, h.finrank_eq_one u]; norm_num
    · rw [hd_def, h.finrank_eq_two u]; norm_num
  set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def
  have hr : r ^ d = a := by
    apply e.injective
    rw [map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact (map_ne_zero _).mpr x.ne_zero
  have hr0 : algebraMap u.Completion W.Completion r ≠ 0 := by
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hd.ne'] at hr
    exact ha0 hr.symm
  let w0 : ↑(InfinitePlace.placesOver K u) := ⟨W, hWu⟩
  refine ⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩
  apply Units.ext
  simp only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
    Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]
  change Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a
  rw [Algebra.norm_algebraMap, ← hd_def, hr]
