import Mathlib
import Formalism.PeriodIntegrals.KerLat

noncomputable section
open NumberField ComplexConjugate
open scoped nonZeroDivisors

namespace PI.KerLat.PerPairProof

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`.

Simplify using `only [Complex.real_smul] at hst`. Establish `h2` using `congrArg Complex.im (congrArg (fun z => conj a * z) hst)`. Simplify using `only [mul_zero, Complex.zero_im] at h2`. Establish `e1 : (conj a * ((s : ℂ) * a)).im = 0`. Rewrite using `[mul_left_comm, mul_comm (conj a) a, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]`.

Establish `e2 : (conj a * ((t : ℂ) * b)).im = t * (conj a * b).im`. Rewrite using `[mul_left_comm, Complex.im_ofReal_mul]`. Rewrite `h2` using `[mul_add, Complex.add_im, e1, e2, zero_add]`. Establish `ht : t = 0` using `(mul_eq_zero.1 h2).resolve_right h`. Use `⟨?_, ht⟩` and prove the remaining obligations.

Rewrite `hst` using `[ht, Complex.ofReal_zero, zero_mul, add_zero]`. Conclude with `(mul_eq_zero.1 hst).resolve_right ha |> Complex.ofReal_eq_zero.1`.
-/
theorem indep_of_im_ne {a b : ℂ} (h : (conj a * b).im ≠ 0) : LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
  simp only [Complex.real_smul] at hst
  have h2 := congrArg Complex.im (congrArg (fun z => conj a * z) hst)
  simp only [mul_zero, Complex.zero_im] at h2
  have e1 : (conj a * ((s : ℂ) * a)).im = 0 := by
    rw [mul_left_comm, mul_comm (conj a) a, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  have e2 : (conj a * ((t : ℂ) * b)).im = t * (conj a * b).im := by
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [mul_add, Complex.add_im, e1, e2, zero_add] at h2
  have ht : t = 0 := (mul_eq_zero.1 h2).resolve_right h
  refine ⟨?_, ht⟩
  rw [ht, Complex.ofReal_zero, zero_mul, add_zero] at hst
  exact (mul_eq_zero.1 hst).resolve_right ha |> Complex.ofReal_eq_zero.1

def imMul {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (a : ℂ) : K →ₗ[ℚ] ℝ where
  toFun k := (conj a * φ k).im
  map_add' x y := by simp [mul_add]
  map_smul' q x := by
    simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
    rw [mul_left_comm, ← Complex.ofReal_ratCast, Complex.im_ofReal_mul]

/- English proof (translation)
Introduce `h0`. Take `⟨k, hk⟩` from `hφ`. Establish `hB0 : φ (B 0) ≠ 0` using `(map_ne_zero φ).2 (B.ne_zero 0)`. Establish `hs : ∀ (q : ℚ) (v : K), (conj (φ (B 0)) * φ (q • v)).im = (q : ℝ) * (conj (φ (B 0)) * φ v).im`. Introduce `q v`.

Rewrite using `[Rat.smul_def, map_mul, map_ratCast, mul_left_comm, ← Complex.ofReal_ratCast, Complex.im_ofReal_mul]`. Establish `e0 : (conj (φ (B 0)) * φ (B 0)).im = 0`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.ofReal_im]`. Establish `key : ∀ x : K, (conj (φ (B 0)) * φ x).im = 0`. Introduce `x`.

Rewrite using `[← B.sum_repr x, map_sum, Finset.mul_sum, Complex.im_sum, Fin.sum_univ_two, hs, hs, e0, h0]`. Simplify using the standard rewrite rules. Establish `h1` using `key 1`. Rewrite `h1` using `[map_one, mul_one, Complex.conj_im, neg_eq_zero]`. Establish `h2` using `key k`.

Rewrite `h2` using `[Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, neg_zero, zero_mul, add_zero]`. Establish `hre : (φ (B 0)).re ≠ 0` using `fun hr => hB0 (Complex.ext hr h1)`. Conclude with `hk ((mul_eq_zero.1 h2).resolve_left hre)`.
-/
theorem im_ne {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (hφ : ∃ k : K, (φ k).im ≠ 0)
    (B : Module.Basis (Fin 2) ℚ K) : (conj (φ (B 0)) * φ (B 1)).im ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := hφ
  have hB0 : φ (B 0) ≠ 0 := (map_ne_zero φ).2 (B.ne_zero 0)
  have hs : ∀ (q : ℚ) (v : K),
      (conj (φ (B 0)) * φ (q • v)).im = (q : ℝ) * (conj (φ (B 0)) * φ v).im := by
    intro q v
    rw [Rat.smul_def, map_mul, map_ratCast, mul_left_comm, ← Complex.ofReal_ratCast,
      Complex.im_ofReal_mul]
  have e0 : (conj (φ (B 0)) * φ (B 0)).im = 0 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_im]
  have key : ∀ x : K, (conj (φ (B 0)) * φ x).im = 0 := by
    intro x
    rw [← B.sum_repr x, map_sum, Finset.mul_sum, Complex.im_sum, Fin.sum_univ_two, hs, hs, e0, h0]
    simp
  have h1 := key 1
  rw [map_one, mul_one, Complex.conj_im, neg_eq_zero] at h1
  have h2 := key k
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, neg_zero, zero_mul, add_zero] at h2
  have hre : (φ (B 0)).re ≠ 0 := fun hr => hB0 (Complex.ext hr h1)
  exact hk ((mul_eq_zero.1 h2).resolve_left hre)

/- English proof (translation)
Introduce `K _ _ φ cc δ hK hφ hcc hδ`. Set `b0` to `NumberField.RingOfIntegers.basis K`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]`. Set `e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2` to `Fintype.equivFinOfCardEq hcard`.

Set `bI : Module.Basis (Fin 2) ℤ cc` to `(Ideal.selfBasis b0 cc hcc).reindex e`. Set `f : cc →+ ℂ` to `{ toFun := fun c => δ * φ ((c : 𝓞 K) : K) map_zero' := by simp map_add' := fun x y => by simp [mul_add] }`. Set `ω : Fin 2 → ℂ` to `fun i => f (bI i)`. Set `g : cc →ₗ[ℤ] K` to `((algebraMap (𝓞 K) K).toAddMonoidHom.comp cc.subtype.toAddMonoidHom).toIntLinearMap`. Establish `hg : LinearMap.ker g = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`. Conclude with `Subtype.ext (IsFractionRing.injective (𝓞 K) K hxy)`. Establish `hliZ : LinearIndependent ℤ (fun i => ((bI i : 𝓞 K) : K))` using `bI.linearIndependent.map' g hg`. Establish `hli : LinearIndependent ℚ (fun i => ((bI i : 𝓞 K) : K))` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hliZ`.

Set `B : Module.Basis (Fin 2) ℚ K` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])`. Establish `hBi : ∀ i, B i = ((bI i : 𝓞 K) : K)` using `fun i => by`. Simplify using `[B, coe_basisOfLinearIndependentOfCardEqFinrank]`. Establish `hω : (conj (ω 0) * ω 1).im ≠ 0`. Establish `hB` using `im_ne φ hφ B`.

Rewrite `hB` using `[hBi, hBi]`. Establish `eq : conj (ω 0) * ω 1 = (Complex.normSq δ : ℂ) * (conj (φ ((bI 0 : 𝓞 K) : K)) * φ ((bI 1 : 𝓞 K) : K))`. Simplify using `only [ω, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Rewrite using `[Complex.normSq_eq_conj_mul_self, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eq, Complex.im_ofReal_mul]`. Conclude with `mul_ne_zero (Complex.normSq_pos.2 hδ).ne' hB`. Use `⟨⟨ω 0, ω 1, indep_of_im_ne hω⟩, ?_⟩` and prove the remaining obligations. Use `show (Submodule.span ℤ {ω 0, ω 1}).toAddSubgroup = _`. Rewrite using `[← AddSubgroup.toIntSubmodule_closure]`.

Use `first`. Consider the case `rw [AddSubgroup.toIntSubmodule_toAddSubgroup]`. Consider the case `change AddSubgroup.closure {ω 0, ω 1} = _`. Apply `le_antisymm` to reduce the goal to its premises. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations.

Introduce and unpack `w (rfl | rfl)`. Conclude with `⟨bI 0, (bI 0).2, rfl⟩`. Conclude with `⟨bI 1, (bI 1).2, rfl⟩`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `w ⟨c, hc, rfl⟩`.

Establish `hfc : δ * φ (c : K) = f ⟨c, hc⟩` using `rfl`. Rewrite using `[hfc, ← bI.sum_repr ⟨c, hc⟩, map_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Use `AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _` and prove the remaining obligations.

Use `fin_cases i`. Conclude with `Set.mem_insert _ _`. Conclude with `Set.mem_insert_of_mem _ rfl`.
-/
theorem perPair : PI.KerLat.PerPair := by
  intro K _ _ φ cc δ hK hφ hcc hδ
  classical
  let b0 := NumberField.RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let bI : Module.Basis (Fin 2) ℤ cc := (Ideal.selfBasis b0 cc hcc).reindex e
  let f : cc →+ ℂ :=
    { toFun := fun c => δ * φ ((c : 𝓞 K) : K)
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  let ω : Fin 2 → ℂ := fun i => f (bI i)
  let g : cc →ₗ[ℤ] K :=
    ((algebraMap (𝓞 K) K).toAddMonoidHom.comp cc.subtype.toAddMonoidHom).toIntLinearMap
  have hg : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext (IsFractionRing.injective (𝓞 K) K hxy)
  have hliZ : LinearIndependent ℤ (fun i => ((bI i : 𝓞 K) : K)) :=
    bI.linearIndependent.map' g hg
  have hli : LinearIndependent ℚ (fun i => ((bI i : 𝓞 K) : K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 hliZ
  let B : Module.Basis (Fin 2) ℚ K :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hBi : ∀ i, B i = ((bI i : 𝓞 K) : K) := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hω : (conj (ω 0) * ω 1).im ≠ 0 := by
    have hB := im_ne φ hφ B
    rw [hBi, hBi] at hB
    have eq : conj (ω 0) * ω 1 =
        (Complex.normSq δ : ℂ) * (conj (φ ((bI 0 : 𝓞 K) : K)) * φ ((bI 1 : 𝓞 K) : K)) := by
      simp only [ω, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Complex.normSq_eq_conj_mul_self, map_mul]
      ring
    rw [eq, Complex.im_ofReal_mul]
    exact mul_ne_zero (Complex.normSq_pos.2 hδ).ne' hB
  refine ⟨⟨ω 0, ω 1, indep_of_im_ne hω⟩, ?_⟩
  show (Submodule.span ℤ {ω 0, ω 1}).toAddSubgroup = _
  rw [← AddSubgroup.toIntSubmodule_closure]
  first
  | rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
  | change AddSubgroup.closure {ω 0, ω 1} = _
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro w (rfl | rfl)
    · exact ⟨bI 0, (bI 0).2, rfl⟩
    · exact ⟨bI 1, (bI 1).2, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    have hfc : δ * φ (c : K) = f ⟨c, hc⟩ := rfl
    rw [hfc, ← bI.sum_repr ⟨c, hc⟩, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

end PI.KerLat.PerPairProof
