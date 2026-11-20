import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltKernelSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt.Kernel

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Simplify using `[SubSystem.secs, Submodule.mem_iInf]`.
-/
theorem mem_secs_iff' {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

def ratioPow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (j : Fin (N + 1)) (b : ℕ) :
    chartRing S x I :=
  ⟨x j ^ b / x i ^ b, X j ^ b, X i ^ b, b, pow_mem (X_mem_monos hi) b, isHomogeneous_X_pow _ _,
    isHomogeneous_X_pow _ _, by simp⟩

/- English proof (translation)
Establish `h : (aeval (fun l => x l / x i) : Poly S N →ₐ[S] Ω).range ≤ chartRing S x I`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X _ _, isHomogeneous_X _ _, by simp⟩`. Conclude with `h ⟨f, rfl⟩`.
-/
theorem aeval_div_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (f : Poly S N) :
    aeval (fun l => x l / x i) f ∈ chartRing S x I := by
  have h : (aeval (fun l => x l / x i) : Poly S N →ₐ[S] Ω).range ≤ chartRing S x I := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X _ _, isHomogeneous_X _ _, by simp⟩
  exact h ⟨f, rfl⟩

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}`. Set `K : Ideal (Poly S N)` to `{ carrier := {f | aeval (fun l => x l / x i) f ∈ M} add_mem' := fun {f g} hf hg => by`. Simplify using `only [Set.mem_ofPred_eq, map_add] at *`. Conclude with `M.add_mem hf hg`.

Use the proof step `zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem`. Use the proof step `smul_mem' := fun r f hf => by`. Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *`. Conclude with `M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }`. Establish `hK : primeOf (S` using `S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by`.

Use `sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval (fun l => x l / x i) f ∈ M`. Rewrite using `[← sum_homogeneousComponent f, map_sum]`. Use `M.zero_mem` and compare the differences between its conclusion and the goal. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i, (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp (homogeneousComponent_mem_primeOf x hf d), zero_div]`. Introduce and unpack `g ⟨c, hg, hz⟩`. Establish `hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I`. Express the relevant statement in the definitionally equal form `x i ^ b ∈ twistMod S x (b : ℤ) I`. Rewrite using `[twistMod_eq_span _ I hi, zpow_natCast]`.

Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨o, ho, he⟩` from `hz I _ hδ`. Rewrite `ho` using `[twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `ho`. Express the relevant statement in the definitionally equal form `aeval (fun l => x l / x i) g ∈ M`.

Rewrite using `[aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite `he`, the goal using `[chartRing_smul_def]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-he`.

Rewrite using `[idealMod, Submodule.span_le]`. Introduce and unpack `_ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Establish `hm : aeval (fun l => x l / x i) f ∈ M` using `hK hf`. Rewrite `hm` using `[aeval_div_of_isHomogeneous hfe i]`.

Establish `h` using `M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse, by simp⟩ : chartRing S x I) hm`. Rewrite `h` using `[chartRing_smul_def]`. Rewrite using `[SetLike.mem_coe]`. Use `h using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = x i ^ e / aeval x s * (aeval x f / x i ^ e)`.

Establish `: x i ^ e ≠ 0` using `pow_ne_zero _ hxi`. Clear the denominators using the available nonvanishing facts.
-/
theorem idealMod_le (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}
  let K : Ideal (Poly S N) :=
    { carrier := {f | aeval (fun l => x l / x i) f ∈ M}
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact M.add_mem hf hg
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem
      smul_mem' := fun r f hf => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }
  have hK : primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by
    refine sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)
    · change aeval (fun l => x l / x i) f ∈ M
      rw [← sum_homogeneousComponent f, map_sum]
      convert M.zero_mem
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i,
        (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
          (homogeneousComponent_mem_primeOf x hf d), zero_div]
    · rintro g ⟨c, hg, hz⟩
      have hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I := by
        change x i ^ b ∈ twistMod S x (b : ℤ) I
        rw [twistMod_eq_span _ I hi, zpow_natCast]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨o, ho, he⟩ := hz I _ hδ
      rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at ho
      obtain ⟨a, rfl⟩ := ho
      change aeval (fun l => x l / x i) g ∈ M
      rw [aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [chartRing_smul_def] at he ⊢
      field_simp
      linear_combination -he
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hm : aeval (fun l => x l / x i) f ∈ M := hK hf
  rw [aeval_div_of_isHomogeneous hfe i] at hm
  have h := M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse,
    by simp⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at h
  rw [SetLike.mem_coe]
  convert h using 1
  change _ = x i ^ e / aeval x s * (aeval x f / x i ^ e)
  have : x i ^ e ≠ 0 := pow_ne_zero _ hxi
  field_simp

/- English proof (translation)
Introduce `S _ Ω _ _ N x j b F hj`. Establish `hjb : x j ^ b ≠ 0` using `pow_ne_zero _ hj`. Prove the components needed by the constructor for the conclusion. Introduce `t ht`. Use `mem_secs_iff'.mpr fun I => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Establish `hI` using `mem_secs_iff'.mp ht I`. Rewrite `hI` using `[SubSystem.twist_sub_eq_mul_of_line]`. Use `Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `q ∈ twistMod S x (-(b : ℤ)) I at hq`. Rewrite `hq` using `[twistMod_eq_span _ I hi, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hq`. Establish `h` using `(F.sub I).smul_mem (a * ratioPow I hi j b) hy`. Rewrite `h`, the goal using `[chartRing_smul_def]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_add]`. Conclude with `(F.sub I).add_mem hu hv`.

Introduce `s hs`. Use `⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Establish `hI` using `mem_secs_iff'.mp hs I`.

Rewrite `hI` using `[SubSystem.twist_sub_eq_mul_of_line]`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line]`. Use `Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)`. Establish `hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I`.

Express the relevant statement in the definitionally equal form `_ ∈ twistMod S x (-(b : ℤ)) I`. Rewrite using `[twistMod_eq_span _ I hi]`. Conclude with `Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)`. Use `Submodule.mul_mem_mul hq' hy using 1` and compare the differences between its conclusion and the goal. Rewrite using `[chartRing_smul_def]`.

Simplify using `only [zpow_neg, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_add]`. Conclude with `add_mem hu hv`.
-/
theorem proof : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by
  intro S _ Ω _ _ N x j b F hj
  have hjb : x j ^ b ≠ 0 := pow_ne_zero _ hj
  constructor
  · intro t ht
    refine mem_secs_iff'.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp ht I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · change q ∈ twistMod S x (-(b : ℤ)) I at hq
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      have h := (F.sub I).smul_mem (a * ratioPow I hi j b) hy
      rw [chartRing_smul_def] at h ⊢
      convert h using 1
      simp only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact (F.sub I).add_mem hu hv
  · intro s hs
    refine ⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp hs I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    rw [SubSystem.twist_sub_eq_mul_of_line]
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)
      have hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I := by
        change _ ∈ twistMod S x (-(b : ℤ)) I
        rw [twistMod_eq_span _ I hi]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
      convert Submodule.mul_mem_mul hq' hy using 1
      rw [chartRing_smul_def]
      simp only [zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact add_mem hu hv

end SectionCount.Drop.Filt.Kernel

end

end GroundTheory.Heights₂.Heights.Kleiman
