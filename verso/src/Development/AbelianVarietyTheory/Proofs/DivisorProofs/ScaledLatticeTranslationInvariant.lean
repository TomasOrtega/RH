import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicTemperedDistPoissonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.LatUniq

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.
-/
theorem coe_mem_ints_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ v.valuation F k ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Rewrite using `[GlobalTheory.EvAdm.mem_scaledInt]`. Establish `key : ∀ (i : κ) (v : HeightOneSpectrum (𝓞 F)), (algebraMap F (v.adicCompletion F) a)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = ((a⁻¹ * ξ i : F) : v.adicCompletion F)`. Introduce `i v`. Establish `h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i)` using `rfl`. Rewrite using `[h1, ← map_inv₀, ← map_mul]`.

Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Establish `hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1` using `fun v => by`. Use `h i v` as an intermediate fact.

Rewrite `this` using `[key]`. Conclude with `(coe_mem_ints_iff v _).mp this`. Take `⟨z, hz⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hz' : ((z : 𝓞 F) : F) = a⁻¹ * ξ i` using `hz`.

Rewrite using `[hz', ← mul_assoc, mul_inv_cancel₀ ha, one_mul]`. Introduce `h i v`. Take `⟨z, hz⟩` from `h i`. Rewrite using `[key, hz, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]`. Conclude with `(coe_mem_ints_iff v _).mpr (HeightOneSpectrum.valuation_le_one v z)`.
-/
theorem mem_scaledInt_iff {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0) (ξ : κ → F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a ↔
      ∀ i, ∃ z : 𝓞 F, ξ i = a * (z : F) := by
  rw [GlobalTheory.EvAdm.mem_scaledInt]
  have key : ∀ (i : κ) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v =
        ((a⁻¹ * ξ i : F) : v.adicCompletion F) := by
    intro i v
    have h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [h1, ← map_inv₀, ← map_mul]
    rfl
  constructor
  · intro h i
    have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
      have := h i v
      rw [key] at this
      exact (coe_mem_ints_iff v _).mp this
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
    refine ⟨z, ?_⟩
    have hz' : ((z : 𝓞 F) : F) = a⁻¹ * ξ i := hz
    rw [hz', ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro h i v
    obtain ⟨z, hz⟩ := h i
    rw [key, hz, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    exact (coe_mem_ints_iff v _).mpr (HeightOneSpectrum.valuation_le_one v z)

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

/- English proof (translation)
Set `Φ : (Fin n → ℝ) ≃L[ℝ] E` to `B.equivFun.symm.toContinuousLinearEquiv`. Establish `hΦ : ∀ t, Φ t = ∑ l, t l • B l` using `fun t => B.equivFun_symm_apply t`. Establish `hΦs : ∀ y l, Φ.symm y l = B.repr y l` using `fun y l => rfl`. Set `C : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ.symm`. Establish `hC : ∀ g y, C g y = g (Φ.symm y)` using `fun g y => rfl`.

Establish `t1 : ∀ k : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, g' x = g (x + fun i => (k i : ℝ))) → (T.comp C) g' = (T.comp C) g`. Introduce `k g g' hg`. Use `show T (C g') = T (C g)`. Apply `h1 k` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[hC, hC, hg]`. Use `congr 1`. Rewrite using `[ContinuousLinearEquiv.map_add, ← hΦ]`. Simplify using the standard rewrite rules. Establish `t2 : ∀ m : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, g' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * g x) → (T.comp C) g' = (T.comp C) g`.

Introduce `m g g' hg`. Use `show T (C g') = T (C g)`. Apply `h2 m` to reduce the goal to its premises. Introduce `y`. Rewrite using `[hC, hC, hg]`.

Simplify using `only [hΦs]`. Take `⟨c, hc⟩` from `GlobalTheory.T.periodic_tempered_dist_poisson n (T.comp C) t1 t2`. Use `⟨c, fun f => ?_⟩` and prove the remaining obligations. Establish `hf : C (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f) = f`. Use extensionality with `y`.

Rewrite using `[hC]`. Simplify using the standard rewrite rules. Use `hc (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f)` as an intermediate fact. Rewrite `this` using `[ContinuousLinearMap.comp_apply, hf]`. Rewrite using `[this]`.

Use `congr 1`. Use `tsum_congr fun k => ?_` and prove the remaining obligations. Simplify using `[hΦ]`.
-/
theorem transfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : Module.Basis (Fin n) ℝ E) (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    (h1 : ∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap E ℂ,
      (∀ x, f' x = f (x + ∑ l, (k l : ℝ) • B l)) → T f' = T f)
    (h2 : ∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap E ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ l, (m l : ℝ) * B.repr x l : ℝ) : ℂ)) * f x) →
        T f' = T f) :
    ∃ c : ℂ, ∀ f : SchwartzMap E ℂ, T f = c * ∑' k : Fin n → ℤ, f (∑ l, (k l : ℝ) • B l) := by
  let Φ : (Fin n → ℝ) ≃L[ℝ] E := B.equivFun.symm.toContinuousLinearEquiv
  have hΦ : ∀ t, Φ t = ∑ l, t l • B l := fun t => B.equivFun_symm_apply t
  have hΦs : ∀ y l, Φ.symm y l = B.repr y l := fun y l => rfl
  let C : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ.symm
  have hC : ∀ g y, C g y = g (Φ.symm y) := fun g y => rfl
  have t1 : ∀ k : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, g' x = g (x + fun i => (k i : ℝ))) → (T.comp C) g' = (T.comp C) g := by
    intro k g g' hg
    show T (C g') = T (C g)
    apply h1 k
    intro y
    rw [hC, hC, hg]
    congr 1
    rw [ContinuousLinearEquiv.map_add, ← hΦ]
    simp
  have t2 : ∀ m : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, g' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * g x) →
        (T.comp C) g' = (T.comp C) g := by
    intro m g g' hg
    show T (C g') = T (C g)
    apply h2 m
    intro y
    rw [hC, hC, hg]
    simp only [hΦs]
  obtain ⟨c, hc⟩ := GlobalTheory.T.periodic_tempered_dist_poisson n (T.comp C) t1 t2
  refine ⟨c, fun f => ?_⟩
  have hf : C (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f) = f := by
    ext y; rw [hC]; simp
  have := hc (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f)
  rw [ContinuousLinearMap.comp_apply, hf] at this
  rw [this]
  congr 1
  refine tsum_congr fun k => ?_
  simp [hΦ]

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

variable {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ]

abbrev Idx (F : Type) [Field F] [NumberField F] := Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)

abbrev nn (F : Type) [Field F] [NumberField F] : ℕ := Fintype.card (Idx κ F)

def mulA (a : F) (ha : a ≠ 0) : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] mixedEmbedding.mixedSpace F where
  toFun x := mixedEmbedding F a * x
  invFun x := mixedEmbedding F a⁻¹ * x
  map_add' x y := mul_add _ x y
  map_smul' r x := mul_smul_comm r _ x
  left_inv x := by simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  right_inv x := by simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

def intBasis (F : Type) [Field F] [NumberField F] : Module.Basis (Fin (nn κ F)) ℤ (κ → 𝓞 F) :=
  (Pi.basis fun _ : κ => RingOfIntegers.basis F).reindex (Fintype.equivFin (Idx κ F))

def realBasis (a : F) (ha : a ≠ 0) : Module.Basis (Fin (nn κ F)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Pi.basis fun _ : κ => (mixedEmbedding.latticeBasis F).map (mulA a ha)).reindex (Fintype.equivFin (Idx κ F))

/- English proof (translation)
Take `⟨p, rfl⟩` from `(Fintype.equivFin (Idx κ F)).surjective l`. Simplify using `only [realBasis, intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply, Module.Basis.map_apply]`. Distinguish the cases in `h : i = p.1`. Substitute `h` using the available equality. Simplify using `[mulA, mixedEmbedding.latticeBasis_apply, integralBasis_apply]`.

Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem realBasis_apply (a : F) (ha : a ≠ 0) (l : Fin (nn κ F)) (i : κ) :
    realBasis κ a ha l i = mixedEmbedding F (a * ((intBasis κ F l i : 𝓞 F) : F)) := by
  obtain ⟨p, rfl⟩ := (Fintype.equivFin (Idx κ F)).surjective l
  simp only [realBasis, intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply,
    Module.Basis.map_apply]
  by_cases h : i = p.1
  · subst h
    simp [mulA, mixedEmbedding.latticeBasis_apply, integralBasis_apply]
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, realBasis_apply, Finset.mul_sum, mul_smul_comm, Int.cast_smul_eq_zsmul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Conclude with `mul_left_comm _ _ _`.
-/
theorem sum_realBasis (a : F) (ha : a ≠ 0) (k : Fin (nn κ F) → ℤ) :
    ∑ l, (k l : ℝ) • realBasis κ a ha l =
      fun i => mixedEmbedding F (a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F)) := by
  funext i
  simp [Finset.sum_apply, realBasis_apply, Finset.mul_sum, mul_smul_comm, Int.cast_smul_eq_zsmul]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact mul_left_comm _ _ _

def dualVec (a : F) (m : Fin (nn κ F) → ℤ) : κ → F := fun i =>
  a⁻¹ * ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i, j⟩)) : ℚ) •
    (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j

/- English proof (translation)
Take `⟨⟨i₀, j₀⟩, rfl⟩` from `(Fintype.equivFin (Idx κ F)).surjective l`. Establish `hZ : ∀ i, intBasis κ F (Fintype.equivFin (Idx κ F) ⟨i₀, j₀⟩) i = Pi.single (M` using `fun _ : κ => 𝓞 F) i₀ (RingOfIntegers.basis F j₀) i := by`. Introduce `i`. Simplify using `only [intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply]`. Rewrite using `[Finset.sum_eq_single i₀]`.

Rewrite using `[hZ, Pi.single_eq_same]`. Simplify using `only [dualVec]`. Establish `e1 : a * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F) * (a⁻¹ * ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) • (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j) = ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) • ((Algebra.traceForm ℚ F). …`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_sum]`. Establish `hd : ∀ j, Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F)) = if j₀ = j then 1 else 0`. Introduce `j`.

Use `(Algebra.traceForm ℚ F).apply_dualBasis_left (traceForm_nondegenerate ℚ F) (integralBasis F) j j₀` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply, integralBasis_apply]`. Conclude with `this`. Simplify using `only [map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Introduce `i _ hi`.

Rewrite using `[hZ, Pi.single_eq_of_ne hi]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem trace_dualVec (a : F) (ha : a ≠ 0) (m : Fin (nn κ F) → ℤ) (l : Fin (nn κ F)) :
    Algebra.trace ℚ F (∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i) = -(m l : ℚ) := by
  obtain ⟨⟨i₀, j₀⟩, rfl⟩ := (Fintype.equivFin (Idx κ F)).surjective l
  have hZ : ∀ i, intBasis κ F (Fintype.equivFin (Idx κ F) ⟨i₀, j₀⟩) i =
      Pi.single (M := fun _ : κ => 𝓞 F) i₀ (RingOfIntegers.basis F j₀) i := by
    intro i
    simp only [intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single i₀]
  · rw [hZ, Pi.single_eq_same]
    simp only [dualVec]
    have e1 : a * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F) * (a⁻¹ * ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) •
        (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j) =
        ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) •
        ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j *
          ((RingOfIntegers.basis F j₀ : 𝓞 F) : F)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def]
      field_simp
    rw [e1, map_sum]
    have hd : ∀ j, Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F)
        (integralBasis F) j * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F)) = if j₀ = j then 1 else 0 := by
      intro j
      have := (Algebra.traceForm ℚ F).apply_dualBasis_left (traceForm_nondegenerate ℚ F) (integralBasis F) j j₀
      rw [Algebra.traceForm_apply, integralBasis_apply] at this
      exact this
    simp only [map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro i _ hi
    rw [hZ, Pi.single_eq_of_ne hi]
    simp
  · simp

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

variable {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ]

/- English proof (translation)
Establish `hl : ∀ l, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i)) = -(m l : ℝ)`. Introduce `l`. Establish `e : ∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i) = mixedEmbedding F (∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i)`. Simplify using `only [realBasis_apply, map_sum, map_mul]`. Rewrite using `[e, GlobalTheory.PsiNontriv.trace_mixedEmbedding, trace_dualVec κ a ha m l]`.

Use `push_cast`. Both sides reduce to the same expression. Use `conv_rhs => rw [← (realBasis κ a ha).sum_repr x]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Finset.sum_mul, smul_mul_assoc]`. Rewrite using `[Finset.sum_comm, map_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, map_smul, smul_eq_mul, hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_identity (a : F) (ha : a ≠ 0) (m : Fin (nn κ F) → ℤ) (x : κ → mixedEmbedding.mixedSpace F) :
    ∑ l, (m l : ℝ) * (realBasis κ a ha).repr x l =
      -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (dualVec κ a m i)) := by
  have hl : ∀ l, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i)) = -(m l : ℝ) := by
    intro l
    have e : ∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i) =
        mixedEmbedding F (∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i) := by
      simp only [realBasis_apply, map_sum, map_mul]
    rw [e, GlobalTheory.PsiNontriv.trace_mixedEmbedding, trace_dualVec κ a ha m l]
    push_cast
    rfl
  conv_rhs => rw [← (realBasis κ a ha).sum_repr x]
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_comm, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.smul_sum, map_smul, smul_eq_mul, hl]
  ring

/- English proof (translation)
Introduce `F _ _ κ _ a ha T hT hC`. Establish `h1 : ∀ k : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (∀ x, f' x = f (x + ∑ l, (k l : ℝ) • realBasis κ a ha l)) → T f' = T f`. Introduce `k f f' hf`. Use `hT (fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F)) ((mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩) f f' fun x => ?_` and prove the remaining obligations. Rewrite using `[hf, sum_realBasis]`.

Establish `h2 : ∀ m : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ l, (m l : ℝ) * (realBasis κ a ha).repr x l : ℝ) : ℂ)) * f x) → T f' = T f`. Introduce `m f f' hf`. Use `hC (dualVec κ a m) ?_ f f' fun x => ?_` and prove the remaining obligations. Introduce `ξ hξ choose z hz using (mem_scaledInt_iff ha ξ).mp hξ`. Use `⟨∑ l, (intBasis κ F).repr z l * (-(m l)), ?_⟩` and prove the remaining obligations.

Establish `hzs` using `(intBasis κ F).sum_repr z`. Establish `hξ' : ξ = fun i => a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F)`. Use function extensionality and compare the values at `i`. Rewrite using `[hzs, hz i]`. Rewrite using `[hξ']`.

Establish `e : ∑ i, a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F) * dualVec κ a m i = ∑ l, (intBasis κ F).repr z l • ∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc]`.

Rewrite using `[e, map_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, trace_dualVec κ a ha m l, zsmul_eq_mul]`. Rewrite using `[hf, char_identity]`.

Use `congr 1`. Use `push_cast`. Put the polynomial expressions in normal form. Take `⟨c, hc⟩` from `transfer (realBasis κ a ha) T h1 h2`. Use `⟨c, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[hc f]`. Use `congr 1`. Rewrite using `[← tsum_subtype]`. Set `S : Set (κ → F)` to `{ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a}`. Set `θ : (Fin (nn κ F) → ℤ) → S` to `fun k => ⟨fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F), (mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩⟩`.

Establish `hsum : ∀ k : Fin (nn κ F) → ℤ, ∑ l, k l • intBasis κ F l = (intBasis κ F).equivFun.symm k` using `fun k => ((intBasis κ F).equivFun_symm_apply k).symm`. Establish `hθ : Function.Bijective θ`. Prove the components needed by the constructor for the conclusion. Introduce `k k' hkk`. Establish `h0 : ∀ i, a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F) = a * (((∑ l, k' l • intBasis κ F l) i : 𝓞 F) : F)` using `fun i => congrFun (congrArg Subtype.val hkk) i`.

Establish `h3 : ∑ l, k l • intBasis κ F l = ∑ l, k' l • intBasis κ F l`. Use function extensionality and compare the values at `i`. Conclude with `RingOfIntegers.coe_injective (mul_left_cancel₀ ha (h0 i))`. Rewrite `h3` using `[hsum, hsum]`. Conclude with `(intBasis κ F).equivFun.symm.injective h3`.

Introduce and unpack `⟨ξ, hξ⟩ choose z hz using (mem_scaledInt_iff ha ξ).mp hξ`. Use `⟨(intBasis κ F).equivFun z, Subtype.ext ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show a * (((∑ l, _ • intBasis κ F l) i : 𝓞 F) : F) = ξ i`. Rewrite using `[hsum, LinearEquiv.symm_apply_apply, hz i]`.

Rewrite using `[← (Equiv.ofBijective θ hθ).tsum_eq]`. Use `tsum_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[sum_realBasis]`. Both sides reduce to the same expression.
-/
theorem main_lat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))) → T f' = T f) →
    (∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
        T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      T f = c * ∑' ξ : κ → F, {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun ξ => f (fun i => mixedEmbedding F (ξ i))) ξ := by
  intro F _ _ κ _ a ha T hT hC
  have h1 : ∀ k : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = f (x + ∑ l, (k l : ℝ) • realBasis κ a ha l)) → T f' = T f := by
    intro k f f' hf
    refine hT (fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F))
      ((mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩) f f' fun x => ?_
    rw [hf, sum_realBasis]
  have h2 : ∀ m : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I *
        ((∑ l, (m l : ℝ) * (realBasis κ a ha).repr x l : ℝ) : ℂ)) * f x) → T f' = T f := by
    intro m f f' hf
    refine hC (dualVec κ a m) ?_ f f' fun x => ?_
    · intro ξ hξ
      choose z hz using (mem_scaledInt_iff ha ξ).mp hξ
      refine ⟨∑ l, (intBasis κ F).repr z l * (-(m l)), ?_⟩
      have hzs := (intBasis κ F).sum_repr z
      have hξ' : ξ = fun i => a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F) := by
        funext i; rw [hzs, hz i]
      rw [hξ']
      have e : ∑ i, a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F) * dualVec κ a m i =
          ∑ l, (intBasis κ F).repr z l • ∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i := by
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.mul_sum, Finset.sum_mul,
          Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, smul_mul_assoc]
      rw [e, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_zsmul, trace_dualVec κ a ha m l, zsmul_eq_mul]
    · rw [hf, char_identity]
      congr 1
      push_cast
      ring_nf
  obtain ⟨c, hc⟩ := transfer (realBasis κ a ha) T h1 h2
  refine ⟨c, fun f => ?_⟩
  rw [hc f]
  congr 1
  rw [← tsum_subtype]
  let S : Set (κ → F) := {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}
  let θ : (Fin (nn κ F) → ℤ) → S := fun k =>
    ⟨fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F), (mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩⟩
  have hsum : ∀ k : Fin (nn κ F) → ℤ, ∑ l, k l • intBasis κ F l = (intBasis κ F).equivFun.symm k := fun k =>
    ((intBasis κ F).equivFun_symm_apply k).symm
  have hθ : Function.Bijective θ := by
    constructor
    · intro k k' hkk
      have h0 : ∀ i, a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F) =
          a * (((∑ l, k' l • intBasis κ F l) i : 𝓞 F) : F) := fun i => congrFun (congrArg Subtype.val hkk) i
      have h3 : ∑ l, k l • intBasis κ F l = ∑ l, k' l • intBasis κ F l := by
        funext i
        exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha (h0 i))
      rw [hsum, hsum] at h3
      exact (intBasis κ F).equivFun.symm.injective h3
    · rintro ⟨ξ, hξ⟩
      choose z hz using (mem_scaledInt_iff ha ξ).mp hξ
      refine ⟨(intBasis κ F).equivFun z, Subtype.ext ?_⟩
      funext i
      show a * (((∑ l, _ • intBasis κ F l) i : 𝓞 F) : F) = ξ i
      rw [hsum, LinearEquiv.symm_apply_apply, hz i]
  rw [← (Equiv.ofBijective θ hθ).tsum_eq]
  refine tsum_congr fun k => ?_
  rw [sum_realBasis]
  rfl

end GlobalTheory.LatUniq
