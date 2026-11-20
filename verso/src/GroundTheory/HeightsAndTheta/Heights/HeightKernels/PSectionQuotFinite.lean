import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

variable {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩`. Consider the case `algebraMap r => rw [eq_intCast]`.

Conclude with `intCast_mem _ r`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`. Consider the case `mul x z _ _ hx hz => exact mul_mem hx hz`.
-/
theorem mem_blockFnField_of_mem_chartRingZ (t : T) {b : K'} (hb : b ∈ chartRingZ y (fun _ => t)) :
    b ∈ blockFnField y := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

/- English proof (translation)
Take `⟨D, hD0, hD⟩` from `exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)`. Use `⟨D, hD0, fun t => ?_⟩` and prove the remaining obligations. Establish `h` using `hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))`. Rewrite `h` using `[zsmul_eq_mul]`. Conclude with `h`.
-/
theorem exists_int_mul_coord_mem : ∃ D : ℤ, D ≠ 0 ∧ ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K' := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)
  refine ⟨D, hD0, fun t => ?_⟩
  have h := hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [zsmul_eq_mul] at h
  exact h

/- English proof (translation)
Take `⟨t0, ht0⟩` from `CurveAffineCharts.exists_chart y hy`. It suffices to establish `hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv`. Rewrite using `[← hr]`. Conclude with `r.2`.

Introduce `v`. Take `⟨t, -, ht⟩` from `Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩)) ⟨t0, Finset.mem_univ _⟩`. Establish `hyt : y ⟨(), t⟩ ≠ 0`. Introduce `h0`. Establish `h1` using `ht t0 (Finset.mem_univ _)`.

Rewrite `h1` using `[h0, map_zero]`. Conclude with `ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))`. Establish `hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t)` using `SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt`. Establish `h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1` using `(Valuation.mem_integer_iff _ _).mp (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)`. Establish `h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1`.

Take `⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩` from `⟨⟨_, hD t⟩, rfl⟩`. Rewrite using `[← hr]`. Conclude with `HeightOneSpectrum.valuation_le_one v r`. Establish `e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, map_mul]`. Conclude with `mul_le_one' h1 h2`.
-/
theorem int_mul_mem_of_mem_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) {D : ℤ}
    (hD : ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K') {m : K'} (hm : m ∈ sectionMod y) :
    (D : K') * m ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
    SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt
  have h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp
      (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)
  have h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1 := by
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩ :=
      ⟨⟨_, hD t⟩, rfl⟩
    rw [← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  have e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩) := by
    field_simp
  rw [e, map_mul]
  exact mul_le_one' h1 h2

/- English proof (translation)
Take `⟨D, hD0, hD⟩` from `exists_int_mul_coord_mem y`. Establish `: Module.Finite ℤ (integralClosure ℤ K')` using `inferInstanceAs (Module.Finite ℤ (𝓞 K'))`. Set `f : sectionMod y →+ integralClosure ℤ K'` to `{ toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩ map_zero' := Subtype.ext (mul_zero _) map_add' := fun a b => Subtype.ext (mul_add _ _ _) }`. Establish `hinj : Function.Injective f` using `fun a b h => by`. Establish `h' : (D : K') * a = (D : K') * b` using `congrArg (fun z : integralClosure ℤ K' => (z : K')) h`.

Conclude with `Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')`. Establish `hfin : Module.Finite ℤ (sectionMod y)` using `Module.Finite.of_injective f.toIntLinearMap hinj`. Conclude with `Module.Finite.iff_addGroup_fg.mp hfin`.
-/
theorem fg_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) : AddGroup.FG (sectionMod y) := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_coord_mem y
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : sectionMod y →+ integralClosure ℤ K' :=
    { toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun a b => Subtype.ext (mul_add _ _ _) }
  have hinj : Function.Injective f := fun a b h => by
    have h' : (D : K') * a = (D : K') * b := congrArg (fun z : integralClosure ℤ K' => (z : K')) h
    exact Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')
  have hfin : Module.Finite ℤ (sectionMod y) := Module.Finite.of_injective f.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.mp hfin

omit [NumberField K'] in

/- English proof (translation)
Introduce `h0`. Apply `hsP` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `s ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Use `erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]`.

Rewrite using `[h0, map_zero, zero_mul]`.
-/
theorem aeval_ne_zero {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

/- English proof (translation)
Use `set x := aeval y s with hxdef`. Establish `hx0 : x ≠ 0` using `aeval_ne_zero y hs hsP`. Take `⟨t, ht⟩` from `CurveAffineCharts.exists_chart y hy`. Establish `hmt : m / y ⟨(), t⟩ ∈ blockFnField y` using `mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)`. Establish `hxt : x / y ⟨(), t⟩ ∈ blockFnField y` using `mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)`.

Establish `hq : m / x ∈ blockFnField y`. Establish `e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `div_mem hmt hxt`.

Take `⟨n, hn, hnq⟩` from `CurveAffineCharts.exists_nat_mul_mem_curveRing y hq`. Use `⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_nat_mul_mem_span (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {m : K'} (hm : m ∈ sectionMod y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * m ∈ Submodule.span (curveRing y) {aeval y s} := by
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := aeval_ne_zero y hs hsP
  obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
  have hmt : m / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)
  have hxt : x / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)
  have hq : m / x ∈ blockFnField y := by
    have e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩) := by
      field_simp
    rw [e]
    exact div_mem hmt hxt
  obtain ⟨n, hn, hnq⟩ := CurveAffineCharts.exists_nat_mul_mem_curveRing y hq
  refine ⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

/- English proof (translation)
Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨n, hn, hnm⟩` from `exists_nat_mul_mem_span y hy hs hsP m.2`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Rewrite using `[Submodule.subtype_apply]`.

Simplify `hnm` using `[nsmul_eq_mul]`.
-/
theorem isTorsion (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) (q : sectionQuot y (aeval y s)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hy hs hsP m.2
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end SectionQuotientFinite

open SectionQuotientFinite in

/- English proof (translation)
Introduce `T _ K' _ _ y s hy hs hsP`. Establish `hfg : AddGroup.FG (sectionQuot y (aeval y s))` using `AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _) (hG := fg_sectionMod y hy)`. Set `_ : Module ℤ (sectionQuot y (aeval y s))` to `AddCommGroup.toIntModule _`. Establish `hfin : Module.Finite ℤ (sectionQuot y (aeval y s))` using `Module.Finite.iff_addGroup_fg.mpr hfg`. Use `Module.finite_of_fg_torsion _ fun q => ?_` and prove the remaining obligations.

Take `⟨n, hn, hnq⟩` from `isTorsion y hy hs hsP q`. Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((n : ℤ)) • q = 0`. Rewrite using `[natCast_zsmul]`. Conclude with `hnq`.
-/
theorem SectionQuotFinite.closed : SectionQuotFinite.Statement := by
  intro T _ K' _ _ y s hy hs hsP
  have hfg : AddGroup.FG (sectionQuot y (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := fg_sectionMod y hy)
  let _ : Module ℤ (sectionQuot y (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (sectionQuot y (aeval y s)) := Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨n, hn, hnq⟩ := isTorsion y hy hs hsP q
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • q = 0
  rw [natCast_zsmul]
  exact hnq

/- English proof (translation)
The claim follows from `SectionQuotFinite.closed`.
-/
theorem SectionQuotFinite.proof (_hC : CurveCharts.Statement) : SectionQuotFinite.Statement :=
  SectionQuotFinite.closed

end

end GroundTheory.Heights₂.Heights
