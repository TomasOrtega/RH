import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := (W.map (residue 𝒪)).toAffine.CoordinateRing) z`. Take `⟨a', rfl⟩` from `coordReduce_surjective W a`. Take `⟨s', rfl⟩` from `coordReduce_surjective W s`. Establish `hs' : s' ∈ (gaussPrime W).primeCompl` using `fun h => nonZeroDivisors.ne_zero hs (RingHom.mem_ker.1 h)`. Use `⟨IsLocalization.mk' (gaussRing W) a' ⟨s', hs'⟩, ?_⟩` and prove the remaining obligations.

Establish `hspec` using `IsLocalization.mk'_spec (gaussRing W) a' ⟨s', hs'⟩`. Use `congrArg (fun b => gaussResidue W (residue _ b)) hspec` as an intermediate fact. Simplify using `only [map_mul, gaussResidue_residue] at this`. Establish `hne : algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField (coordReduce W s') ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hs)`. Rewrite using `[eq_div_iff hne]`.

Conclude with `this`.
-/
theorem exists_gaussResidue_eq (z : (W.map (residue 𝒪)).toAffine.FunctionField) :
    ∃ b : gaussRing W, gaussResidue W (residue _ b) = z := by
  obtain ⟨a, s, hs, rfl⟩ :=
    IsFractionRing.div_surjective (A := (W.map (residue 𝒪)).toAffine.CoordinateRing) z
  obtain ⟨a', rfl⟩ := coordReduce_surjective W a
  obtain ⟨s', rfl⟩ := coordReduce_surjective W s
  have hs' : s' ∈ (gaussPrime W).primeCompl := fun h =>
    nonZeroDivisors.ne_zero hs (RingHom.mem_ker.1 h)
  refine ⟨IsLocalization.mk' (gaussRing W) a' ⟨s', hs'⟩, ?_⟩
  have hspec := IsLocalization.mk'_spec (gaussRing W) a' ⟨s', hs'⟩
  have := congrArg (fun b => gaussResidue W (residue _ b)) hspec
  simp only [map_mul, gaussResidue_residue] at this
  have hne : algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField (coordReduce W s') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hs)
  rw [eq_div_iff hne]
  exact this

end SlopeTestRemainingChoices

section Isog

variable [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

/- English proof (translation)
Use `letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _`. Establish `hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W') (pointCongr (gaussCurve_map_functionField K W W').symm φ.1) ≠ 0`. Introduce `h0`. Apply `reduceFF_isogeny_ne_zero K W W' φ` to reduce the goal to its premises. Simplify using `only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]`.

Rewrite using `[pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]`. Conclude with `h0`. Take `⟨x, y, h, e⟩` from `exists_integral_of_reducePoint_ne_zero _ _ hne`. Establish `e' : φ.1 = pointCongr (gaussCurve_map_functionField K W W') (Point.some _ _ h)`. Rewrite using `[← e, pointCongr_pointCongr]`.

Both sides reduce to the same expression. Rewrite `e'` using `[pointCongr_some]`. Conclude with `⟨x, y, _, e'⟩`.
-/
theorem exists_isogeny_coords : ∃ (x y : gaussRing W)
    (h : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap _ _ x) (algebraMap _ _ y)), φ.1 = Point.some _ _ h := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr (gaussCurve_map_functionField K W W').symm φ.1) ≠ 0 := by
    intro h0
    apply reduceFF_isogeny_ne_zero K W W' φ
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨x, y, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have e' : φ.1 = pointCongr (gaussCurve_map_functionField K W W') (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  exact ⟨x, y, _, e'⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨x, y, h, hφ⟩` from `exists_isogeny_coords K W W' φ`. Establish `hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) = algebraMap (gaussRing W) _ (algebraMap 𝒪 (gaussRing W) c)` using `fun c => by`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Establish `hxy : (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation x y`. Establish `h₁ : ((W'.map (algebraMap 𝒪 (gaussRing W))).map (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation (algebraMap _ _ x) (algebraMap _ _ y)`.

Rewrite using `[← map_baseChange_eq_map_of K W' (algebraMap 𝒪 (gaussRing W)) _ hjM]`. Conclude with `h.1`. Conclude with `(WeierstrassCurve.Affine.map_equation (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁`. Take `⟨h', hred⟩` from `reduceFF_some K W W' h`. Establish `hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h'`.

Rewrite using `[reduceIsogeny_val, hφ, hred]`. Establish `hx : Function.Injective (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Assume the negation of the conclusion as `hp0`.

Establish `hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x))`. Use `(reduceIsogeny K W W' φ).isGenPt` as an intermediate fact. Rewrite `this` using `[hφ']`. Conclude with `this`. Apply `hT` to reduce the goal to its premises.

Use `⟨p, hp0, ?_⟩` and prove the remaining obligations. Establish `key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x) p)`. Rewrite using `[aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]`. Rewrite using `[key, hp, map_zero]`. Use `set g := gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx`.

Establish `hσ : (φ.comap : _ →+* _).comp (algebraMap (gaussRing W') (W'.baseChange K).toAffine.FunctionField) = (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp g`. Apply `comp_algebraMap_gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx K` to reduce the goal to its premises. Introduce `c show φ.comap (algebraMap 𝒪 _ c) = _`. Rewrite using `[IsScalarTower.algebraMap_apply 𝒪 K, φ.comap.commutes, hjM]`. Use `show φ.comap (genX _) = _`.

Rewrite using `[φ.comap_genX, Isogeny.x, hφ]`. Both sides reduce to the same expression. Use `show φ.comap (genY _) = _`. Rewrite using `[φ.comap_genY, Isogeny.y, hφ]`. Both sides reduce to the same expression.

Establish `hring : (gaussResidue W).comp (fieldEvalRed W' (algebraMap 𝒪 (gaussRing W)) hxy hx) = ((reduceIsogeny K W W' φ).comap : _ →+* _)`. Apply `ringHom_ext_functionField` to reduce the goal to its premises. Introduce `c`. Rewrite using `[RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply, gaussResidue_comp_residueField_map]`. Conclude with `((reduceIsogeny K W W' φ).comap.commutes c).symm`.

Rewrite using `[RingHom.comp_apply, fieldEvalRed_genX] show _ = (reduceIsogeny K W W' φ).comap (genX _)`. Rewrite using `[Isogeny.comap_genX, Isogeny.x, hφ']`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, fieldEvalRed_genY] show _ = (reduceIsogeny K W W' φ).comap (genY _)`. Rewrite using `[Isogeny.comap_genY, Isogeny.y, hφ']`.

Both sides reduce to the same expression. Establish `hres : (gaussResidue W).comp (ResidueField.map g) = ((reduceIsogeny K W W' φ).comap : _ →+* _).comp (gaussResidue W')`. Rewrite using `[residueField_map_gaussLift, ← RingHom.comp_assoc, hring]`. Use `haveI := φ.finiteDimensional`. Use `haveI := (reduceIsogeny K W W' φ).finiteDimensional`.

Use `haveI : Module.Free (reduceIsogeny K W W' φ).comap.fieldRange (W.map (residue 𝒪)).toAffine.FunctionField := Module.Free.of_divisionRing _ _`. Use `set bb := Module.finBasis (reduceIsogeny K W W' φ).comap.fieldRange (W.map (residue 𝒪)).toAffine.FunctionField`. Use `choose b hb using fun i => exists_gaussResidue_eq W (bb i)`. Establish `hli : LinearIndependent φ.comap.fieldRange (fun i => algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (b i))` using `by classical`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc i₀`. Assume the negation of the conclusion as `hci`. Use `choose f hf using fun i => AlgHom.mem_fieldRange.1 (c i).2`. Take `⟨⟨s, hs⟩, hsf⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (gaussRing W')) Finset.univ f`. Use `choose a ha using fun i => hsf i (Finset.mem_univ i)`.

Establish `hrel : ∑ i, g (a i) * b i = 0`. Apply `IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Establish `h1` using `congrArg (fun z => φ.comap (algebraMap _ _ s) * z) hc`. Simplify using `only [mul_zero, Finset.mul_sum, Algebra.smul_def, IntermediateField.algebraMap_apply] at h1`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← RingHom.comp_apply (algebraMap (gaussRing W) _) g, ← hσ, RingHom.comp_apply, ← mul_assoc]`. Use `congr 1`. Rewrite using `[← hf i, ← map_mul]`.

Use `show φ.comap (algebraMap _ _ (a i)) = φ.comap (algebraMap _ _ s * f i)`. Rewrite using `[ha i, Algebra.smul_def]`. Establish `hinj : ∀ z : gaussRing W', z ≠ 0 → g z ≠ 0` using `fun z hz h0 => by`. Establish `h2 : (φ.comap : (W'.baseChange K).toAffine.FunctionField →+* (W.baseChange K).toAffine.FunctionField) (algebraMap (gaussRing W') (W'.baseChange K).toAffine.FunctionField z) = 0`. Rewrite using `[← RingHom.comp_apply, hσ, RingHom.comp_apply, h0, map_zero]`.

Rewrite `h2` using `[map_eq_zero_iff _ (RingHom.injective _), map_eq_zero_iff _ (IsFractionRing.injective _ _)]`. Conclude with `hz h2`. Establish `hai₀ : a i₀ ≠ 0`. Introduce `h0`. Apply `hci` to reduce the goal to its premises.

Use `ha i₀` as an intermediate fact. Rewrite `this` using `[h0, map_zero, eq_comm, smul_eq_zero]`. Break down `this with h1 | h1` into its components or cases. Conclude with `(nonZeroDivisors.ne_zero hs h1).elim`. Conclude with `Subtype.ext (by rw [← hf i₀, h1, map_zero]; rfl)`.

Take `⟨i₁, hi₁, hmin⟩` from `Finset.exists_min_image (Finset.univ.filter fun i => a i ≠ 0) (fun i => IsDiscreteValuationRing.addVal (gaussRing W') (a i)) ⟨i₀, by simp [hai₀]⟩`. Establish `hai₁ : a i₁ ≠ 0` using `(Finset.mem_filter.1 hi₁).2`. Establish `hdvd : ∀ i, a i₁ ∣ a i` using `fun i => by`. Distinguish the cases in `hi : a i = 0`. Rewrite using `[hi]`.

Conclude with `dvd_zero _`. Conclude with `(IsDiscreteValuationRing.addVal_le_iff_dvd).1 (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩))`. Use `choose a' ha' using hdvd`. Establish `ha'₁ : a' i₁ = 1`. Use `ha' i₁` as an intermediate fact.

Conclude with `(mul_eq_left₀ hai₁).1 this.symm`. Establish `hrel' : ∑ i, g (a' i) * b i = 0`. Establish `: g (a i₁) * ∑ i, g (a' i) * b i = 0`. Rewrite using `[Finset.mul_sum, ← hrel]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ha' i, map_mul, mul_assoc]`. Conclude with `(mul_eq_zero.1 this).resolve_left (hinj _ hai₁)`. Establish `hred'` using `congrArg (fun z => gaussResidue W (residue _ z)) hrel'`. Simplify using `only [map_sum, map_mul, map_zero, hb] at hred'`. Establish `hcoef : ∀ i, gaussResidue W (residue _ (g (a' i))) = (reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i)))` using `fun i => by`.

Rewrite using `[← ResidueField.map_residue, ← RingHom.comp_apply, hres]`. Both sides reduce to the same expression. Establish `hli'` using `bb.linearIndependent`. Rewrite `hli'` using `[Fintype.linearIndependent_iff]`. Establish `h0` using `hli' (fun i => ⟨(reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))), ⟨_, rfl⟩⟩) (by`.

Simplify using `only [Algebra.smul_def, IntermediateField.algebraMap_apply]`. Rewrite using `[← hred']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcoef])`. Use `i₁`.

Establish `h1` using `congrArg Subtype.val h0`. Simplify using `only [ha'₁, map_one, ZeroMemClass.coe_zero] at h1`. Conclude with `one_ne_zero h1`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`.

Conclude with `this`.
-/
theorem degree_reduceIsogeny_le : (reduceIsogeny K W W' φ).degree ≤ φ.degree := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) _ (algebraMap 𝒪 (gaussRing W) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation x y := by
    have h₁ : ((W'.map (algebraMap 𝒪 (gaussRing W))).map
        (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' (algebraMap 𝒪 (gaussRing W)) _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W)))
      (residue _ x)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := by
      have := (reduceIsogeny K W W' φ).isGenPt
      rw [hφ'] at this
      exact this
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W
        (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  set g := gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx
  have hσ : (φ.comap : _ →+* _).comp (algebraMap (gaussRing W')
      (W'.baseChange K).toAffine.FunctionField) =
        (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp g := by
    apply comp_algebraMap_gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx K
    · intro c
      show φ.comap (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, φ.comap.commutes, hjM]
    · show φ.comap (genX _) = _
      rw [φ.comap_genX, Isogeny.x, hφ]; rfl
    · show φ.comap (genY _) = _
      rw [φ.comap_genY, Isogeny.y, hφ]; rfl
  have hring : (gaussResidue W).comp (fieldEvalRed W' (algebraMap 𝒪 (gaussRing W)) hxy hx) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _) := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((reduceIsogeny K W W' φ).comap.commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX]
      show _ = (reduceIsogeny K W W' φ).comap (genX _)
      rw [Isogeny.comap_genX, Isogeny.x, hφ']; rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY]
      show _ = (reduceIsogeny K W W' φ).comap (genY _)
      rw [Isogeny.comap_genY, Isogeny.y, hφ']; rfl
  have hres : (gaussResidue W).comp (ResidueField.map g) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _).comp (gaussResidue W') := by
    rw [residueField_map_gaussLift, ← RingHom.comp_assoc, hring]
  haveI := φ.finiteDimensional
  haveI := (reduceIsogeny K W W' φ).finiteDimensional
  haveI : Module.Free (reduceIsogeny K W W' φ).comap.fieldRange
      (W.map (residue 𝒪)).toAffine.FunctionField := Module.Free.of_divisionRing _ _
  set bb := Module.finBasis (reduceIsogeny K W W' φ).comap.fieldRange
    (W.map (residue 𝒪)).toAffine.FunctionField
  choose b hb using fun i => exists_gaussResidue_eq W (bb i)
  have hli : LinearIndependent φ.comap.fieldRange
      (fun i => algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (b i)) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    by_contra hci
    choose f hf using fun i => AlgHom.mem_fieldRange.1 (c i).2
    obtain ⟨⟨s, hs⟩, hsf⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors (gaussRing W')) Finset.univ f
    choose a ha using fun i => hsf i (Finset.mem_univ i)

    have hrel : ∑ i, g (a i) * b i = 0 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      rw [map_sum, map_zero]
      have h1 := congrArg (fun z => φ.comap (algebraMap _ _ s) * z) hc
      simp only [mul_zero, Finset.mul_sum, Algebra.smul_def, IntermediateField.algebraMap_apply]
        at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← RingHom.comp_apply (algebraMap (gaussRing W) _) g, ← hσ, RingHom.comp_apply,
        ← mul_assoc]
      congr 1
      rw [← hf i, ← map_mul]
      show φ.comap (algebraMap _ _ (a i)) = φ.comap (algebraMap _ _ s * f i)
      rw [ha i, Algebra.smul_def]
    have hinj : ∀ z : gaussRing W', z ≠ 0 → g z ≠ 0 := fun z hz h0 => by
      have h2 : (φ.comap : (W'.baseChange K).toAffine.FunctionField →+*
          (W.baseChange K).toAffine.FunctionField) (algebraMap (gaussRing W')
          (W'.baseChange K).toAffine.FunctionField z) = 0 := by
        rw [← RingHom.comp_apply, hσ, RingHom.comp_apply, h0, map_zero]
      rw [map_eq_zero_iff _ (RingHom.injective _),
        map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
      exact hz h2
    have hai₀ : a i₀ ≠ 0 := by
      intro h0
      apply hci
      have := ha i₀
      rw [h0, map_zero, eq_comm, smul_eq_zero] at this
      rcases this with h1 | h1
      · exact (nonZeroDivisors.ne_zero hs h1).elim
      · exact Subtype.ext (by rw [← hf i₀, h1, map_zero]; rfl)
    obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => a i ≠ 0)
      (fun i => IsDiscreteValuationRing.addVal (gaussRing W') (a i)) ⟨i₀, by simp [hai₀]⟩
    have hai₁ : a i₁ ≠ 0 := (Finset.mem_filter.1 hi₁).2
    have hdvd : ∀ i, a i₁ ∣ a i := fun i => by
      by_cases hi : a i = 0
      · rw [hi]; exact dvd_zero _
      · exact (IsDiscreteValuationRing.addVal_le_iff_dvd).1
          (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩))
    choose a' ha' using hdvd
    have ha'₁ : a' i₁ = 1 := by
      have := ha' i₁
      exact (mul_eq_left₀ hai₁).1 this.symm
    have hrel' : ∑ i, g (a' i) * b i = 0 := by
      have : g (a i₁) * ∑ i, g (a' i) * b i = 0 := by
        rw [Finset.mul_sum, ← hrel]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha' i, map_mul, mul_assoc]
      exact (mul_eq_zero.1 this).resolve_left (hinj _ hai₁)
    have hred' := congrArg (fun z => gaussResidue W (residue _ z)) hrel'
    simp only [map_sum, map_mul, map_zero, hb] at hred'
    have hcoef : ∀ i, gaussResidue W (residue _ (g (a' i))) =
        (reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))) := fun i => by
      rw [← ResidueField.map_residue, ← RingHom.comp_apply, hres]; rfl
    have hli' := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli'
    have h0 := hli' (fun i => ⟨(reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))),
      ⟨_, rfl⟩⟩) (by
        simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
        rw [← hred']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoef])
      i₁
    have h1 := congrArg Subtype.val h0
    simp only [ha'₁, map_one, ZeroMemClass.coe_zero] at h1
    exact one_ne_zero h1
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

/- English proof (translation)
Establish `h1` using `degree_reduceIsogeny_le K W W' φ`. Establish `h2` using `degree_reduceIsogeny_le K W' W (dualOver φ)`. Rewrite `h2` using `[degree_dualOver]`. Establish `hc` using `reduceIsogeny_comp K W W' W (dualOver φ) φ`. Rewrite `hc` using `[dualOver_comp, reduceIsogeny_mulIsogeny]`.

Establish `hdeg` using `congrArg Isogeny.degree hc`. Rewrite `hdeg` using `[degree_mulIsogeny, Isogeny.degree_comp, Int.natAbs_natCast]`. Establish `hpos` using `φ.degree_pos`. Establish `hpos'` using `(reduceIsogeny K W W' φ).degree_pos`. Apply `le_antisymm h1` to reduce the goal to its premises.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree < φ.degree ^ 2`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_reduceIsogeny : (reduceIsogeny K W W' φ).degree = φ.degree := by
  have h1 := degree_reduceIsogeny_le K W W' φ
  have h2 := degree_reduceIsogeny_le K W' W (dualOver φ)
  rw [degree_dualOver] at h2
  have hc := reduceIsogeny_comp K W W' W (dualOver φ) φ
  rw [dualOver_comp, reduceIsogeny_mulIsogeny] at hc
  have hdeg := congrArg Isogeny.degree hc
  rw [degree_mulIsogeny, Isogeny.degree_comp, Int.natAbs_natCast] at hdeg
  have hpos := φ.degree_pos
  have hpos' := (reduceIsogeny K W W' φ).degree_pos
  apply le_antisymm h1
  by_contra hlt
  push_neg at hlt
  have : (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree <
      φ.degree ^ 2 := by
    calc (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree
        ≤ φ.degree * (reduceIsogeny K W W' φ).degree := Nat.mul_le_mul_right _ h2
      _ < φ.degree * φ.degree := Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = φ.degree ^ 2 := (sq _).symm
  omega

end Isog

section Hom

variable [W.IsElliptic] [W'.IsElliptic] [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

end Hom

end

end GroundTheory.Global
