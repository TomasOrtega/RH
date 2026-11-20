import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.IntDual

/- English proof (translation)
Use `letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `S` to `integralClosure ℤ_[l] LL`. Use `haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _`. Use `haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S`.

Establish `hinj : Function.Injective (algebraMap ℤ_[l] LL)`. Introduce `a c h`. Conclude with `IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)`. Use `haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by`. Establish `hr0 : algebraMap ℤ_[l] LL r ≠ 0`.

Introduce `h0`. Conclude with `hr.ne_zero (hinj (h0.trans (map_zero _).symm))`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (fun s : S => (s : LL)) hac`. Simplify using `only [Subalgebra.coe_smul, Algebra.smul_def] at h1`.

Conclude with `mul_left_cancel₀ hr0 h1⟩`. Use `haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S`. Set `bO` to `(Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)`. Set `b` to `bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL`.

Establish `hb : ∀ i, b i = (bO i : LL)` using `fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i`. Use `⟨_, b, fun i => ?_, fun x hx i => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `(bO i).2`. Use `bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i` as an intermediate fact.

Conclude with `⟨bO.repr ⟨x, hx⟩ i, this⟩`.
-/
theorem lattice_basis (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ_[l] LL),
      (∀ i, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (b i)) ∧
      ∀ x : LL, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x →
        ∀ i, ∃ z : ℤ_[l], b.repr x i = (z : ℚ_[l]) := by
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure ℤ_[l] LL
  haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S
  have hinj : Function.Injective (algebraMap ℤ_[l] LL) := by
    intro a c h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)
  haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by
    have hr0 : algebraMap ℤ_[l] LL r ≠ 0 := by
      intro h0; exact hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    apply Subtype.ext
    have h1 := congrArg (fun s : S => (s : LL)) hac
    simp only [Subalgebra.coe_smul, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hr0 h1⟩
  haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S
  let bO := (Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)
  let b := bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL
  have hb : ∀ i, b i = (bO i : LL) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i
  refine ⟨_, b, fun i => ?_, fun x hx i => ?_⟩
  · rw [hb]; exact (bO i).2
  · have := bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i
    exact ⟨bO.repr ⟨x, hx⟩ i, this⟩

/- English proof (translation)
Introduce `l _ LL _ _ _ O _ _ hO`. Establish `H` using `GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO`. Take `⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩` from `hO`. Use `haveI := hdom`. Use `haveI := hdvr`.

Use `haveI := hfrac`. Use `haveI := hfd`. Establish `hmem` using `H.1`. Take `⟨n, b, hbint, hcoord⟩` from `lattice_basis l LL`. Set `ι` to `algebraMap O LL`.

Establish `hιinj : Function.Injective ι` using `IsFractionRing.injective O LL`. Set `Tr` to `Algebra.trace ℚ_[l] LL`. Set `B` to `Algebra.traceForm ℚ_[l] LL`. Establish `hB : B.Nondegenerate` using `traceForm_nondegenerate ℚ_[l] LL`. Set `f'` to `B.dualBasis hB b`.

Establish `hcoef : ∀ x i, Tr (f' i * x) = b.repr x i`. Introduce `x i`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[Finset.mul_sum, map_sum]`. Establish `: ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0)`.

Introduce `j`. Rewrite using `[mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]`. Both sides reduce to the same expression. Repeatedly rewrite using `[this, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.

Set `Zs : Subring ℚ_[l]` to `(algebraMap ℤ_[l] ℚ_[l]).range`. Establish `hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l])`. Introduce `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`.

Conclude with `⟨z, hz.symm⟩`. Introduce and unpack `⟨z, hz⟩`. Conclude with `⟨z, hz.symm⟩`. Establish `hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o)` using `fun o => (hmem (ι o)).1 ⟨o, rfl⟩`. Establish `hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs`.

Introduce `i s`. Take `⟨z, hz⟩` from `hcoord (ι s) (hintO s) i`. Rewrite using `[hcoef, hZ]`. Conclude with `⟨z, hz⟩`. Take `⟨⟨c, hc⟩, hcint⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin n)) f'`.

Set `D` to `ι c`. Establish `hD : D ≠ 0`. Introduce `h0`. Conclude with `nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))`. Establish `ho : ∀ i, ∃ o : O, ι o = D * f' i`.

Introduce `i`. Take `⟨o, ho⟩` from `hcint i (Finset.mem_univ i)`. Conclude with `⟨o, by rw [ho, Algebra.smul_def]⟩`. Use `choose o hoD using ho`. Set `I : Ideal O` to `{ carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs} add_mem' := by`.

Introduce `a a' ha ha' s`. Establish `e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_add]`.

Conclude with `Zs.add_mem (ha s) (ha' s)`. Use the proof step `zero_mem' := by`. Introduce `s`. Simplify using `only [map_zero, mul_zero, zero_mul]`. Conclude with `Zs.zero_mem`.

Use the proof step `smul_mem' := by`. Introduce `r a ha s`. Establish `e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s)`. Rewrite using `[smul_eq_mul, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `ha (r * s) }`. Establish `hoI : ∀ i, o i ∈ I`. Introduce `i s`. Use `show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs`.

Rewrite using `[hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]`. Conclude with `hf'M i s`. Set `g` to `Submodule.IsPrincipal.generator I`. Establish `hgI : g ∈ I` using `Submodule.IsPrincipal.generator_mem I`. Establish `ha : ∀ i, ∃ a : O, a * g = o i`.

Introduce `i`. Establish `h` using `hoI i`. Rewrite `h` using `[← Submodule.IsPrincipal.span_singleton_generator I]`. Conclude with `Ideal.mem_span_singleton'.1 h`. Use `choose a hag using ha`.

Set `δ` to `D⁻¹ * ι g`. Set `lam : LL →ₗ[ℚ_[l]] ℚ_[l]` to `Tr.comp (LinearMap.mulLeft ℚ_[l] δ)`. Establish `hlam : ∀ y, lam y = Tr (δ * y)` using `fun y => rfl`. Establish `hδa : ∀ i, δ * ι (a i) = f' i`. Introduce `i`.

Use `show D⁻¹ * ι g * ι (a i) = f' i`. Rewrite using `[mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]`. Establish `he : ∀ i, ∃ e : O, ι e = b i` using `fun i => (hmem (b i)).2 (hbint i)`. Use `choose e he using he`. Use `⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩` and prove the remaining obligations.

Establish `hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (algebraMap ℚ_[l] LL (z : ℚ_[l]))` using `RingHom.isIntegralElem_map _`. Conclude with `(hmem _).2 hz`. Establish `h` using `hgI y`. Rewrite `h` using `[hZ]`. Take `⟨z, hz⟩` from `h`.

Conclude with `⟨z, by rw [hlam]; exact hz⟩`. Use `conv_lhs => rw [← b.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hlam, ← mul_assoc, hδa, hcoef, he]`.
-/
theorem intDual_coef : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  intro l _ LL _ _ _ O _ _ hO
  have H := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩ := hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  haveI := hfd
  have hmem := H.1
  obtain ⟨n, b, hbint, hcoord⟩ := lattice_basis l LL
  let ι := algebraMap O LL
  have hιinj : Function.Injective ι := IsFractionRing.injective O LL
  let Tr := Algebra.trace ℚ_[l] LL
  let B := Algebra.traceForm ℚ_[l] LL
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ_[l] LL
  let f' := B.dualBasis hB b
  have hcoef : ∀ x i, Tr (f' i * x) = b.repr x i := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.mul_sum, map_sum]
    have : ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0) := by
      intro j
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]
      rfl
    simp_rw [this, mul_ite, mul_one, mul_zero]
    simp

  let Zs : Subring ℚ_[l] := (algebraMap ℤ_[l] ℚ_[l]).range
  have hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l]) := by
    intro q; constructor
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
  have hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o) :=
    fun o => (hmem (ι o)).1 ⟨o, rfl⟩
  have hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs := by
    intro i s
    obtain ⟨z, hz⟩ := hcoord (ι s) (hintO s) i
    rw [hcoef, hZ]; exact ⟨z, hz⟩
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n)) f'
  let D := ι c
  have hD : D ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))
  have ho : ∀ i, ∃ o : O, ι o = D * f' i := by
    intro i
    obtain ⟨o, ho⟩ := hcint i (Finset.mem_univ i)
    exact ⟨o, by rw [ho, Algebra.smul_def]⟩
  choose o hoD using ho
  let I : Ideal O :=
    { carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs}
      add_mem' := by
        intro a a' ha ha' s
        have e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s := by
          rw [map_add]; ring
        rw [e, map_add]; exact Zs.add_mem (ha s) (ha' s)
      zero_mem' := by
        intro s; simp only [map_zero, mul_zero, zero_mul]; exact Zs.zero_mem
      smul_mem' := by
        intro r a ha s
        have e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s) := by
          rw [smul_eq_mul, map_mul, map_mul]; ring
        rw [e]; exact ha (r * s) }
  have hoI : ∀ i, o i ∈ I := by
    intro i s
    show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs
    rw [hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    exact hf'M i s
  let g := Submodule.IsPrincipal.generator I
  have hgI : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha : ∀ i, ∃ a : O, a * g = o i := by
    intro i
    have h := hoI i
    rw [← Submodule.IsPrincipal.span_singleton_generator I] at h
    exact Ideal.mem_span_singleton'.1 h
  choose a hag using ha
  let δ := D⁻¹ * ι g
  let lam : LL →ₗ[ℚ_[l]] ℚ_[l] := Tr.comp (LinearMap.mulLeft ℚ_[l] δ)
  have hlam : ∀ y, lam y = Tr (δ * y) := fun y => rfl
  have hδa : ∀ i, δ * ι (a i) = f' i := by
    intro i
    show D⁻¹ * ι g * ι (a i) = f' i
    rw [mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  have he : ∀ i, ∃ e : O, ι e = b i := fun i => (hmem (b i)).2 (hbint i)
  choose e he using he
  refine ⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩
  · have hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem
        (algebraMap ℚ_[l] LL (z : ℚ_[l])) := RingHom.isIntegralElem_map _
    exact (hmem _).2 hz
  · have h := hgI y
    rw [hZ] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [hlam]; exact hz⟩
  · conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam, ← mul_assoc, hδa, hcoef, he]
end GlobalTheory.IntDual
