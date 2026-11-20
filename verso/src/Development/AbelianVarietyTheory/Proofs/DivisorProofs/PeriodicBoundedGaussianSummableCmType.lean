import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeLat

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hlt : ∀ w : InfinitePlace K, w (α : K) < 1`. Introduce `w`. Take `⟨i, hi, -⟩` from `hφ w.embedding`.

Rewrite using `[← InfinitePlace.norm_embedding_eq]`. Break down `hi with hi | hi` into its components or cases. Rewrite using `[hi]`. Conclude with `h i`. Rewrite using `[hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]`.

Conclude with `h i`. Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Conclude with `absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))`.
-/
theorem exists_one_le_norm {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))

/- English proof (translation)
Establish `h0 : α ≠ 0`. Introduce and unpack `rfl`. Apply `hα` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `[GlobalTheory.HeckeTheta.emb]`.

Take `⟨i, hi⟩` from `exists_one_le_norm hφ h0`. Conclude with `hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)`.
-/
theorem one_le_norm_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)

def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h0`. Take `⟨i, hi⟩` from `exists_one_le_norm hφ h0`. Establish `: φ i (a : K) = 0` using `congrFun ha i`.

Rewrite `hi` using `[this, norm_zero]`. Conclude with `absurd hi (by norm_num)`.
-/
theorem embHom_injective {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : Function.Injective (embHom φ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  have : φ i (a : K) = 0 := congrFun ha i
  rw [this, norm_zero] at hi
  exact absurd hi (by norm_num)

omit [Fintype I] in

/- English proof (translation)
Use `set k := Module.finrank ℤ L + 1 with hk`. Establish `h` using `(ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left ((k.factorial : ℝ) / a ^ k)`. Use `.of_norm_bounded_eventually h ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_cofinite_ne 0] with x h0`. Establish `hn : 0 < ‖(x : E)‖` using `norm_pos_iff.2 (by simpa using h0)`.

Establish `h1` using `Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k`. Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]`. Use `(inv_anti₀ (by positivity) h1).trans_eq ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)`. Rewrite using `[mul_pow, ← pow_mul, inv_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap

/- English proof (translation)
Use `DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `x.2`. Take `⟨b, hb⟩` from `y.2`. Rewrite using `[Subtype.dist_eq, dist_eq_norm]`. Establish `hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K)`.

Rewrite using `[← ha, ← hb]`. Use function extensionality and compare the values at `i`. Simplify using `[embHom, GlobalTheory.HeckeTheta.emb]`. Rewrite using `[hsub]`. Apply `one_le_norm_emb hφ` to reduce the goal to its premises.

Rewrite using `[← hsub, sub_ne_zero]`. Conclude with `fun h => hxy (Subtype.ext h)`.
-/
theorem discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)

/- English proof (translation)
Use `haveI := discrete_embLat hφ`. Establish `hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2)` using `summable_exp_neg_mul_norm_sq (embLat φ) hε`. Establish `hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ` using `fun α => LinearMap.mem_range_self _ α`. Set `j : 𝓞 K → embLat φ` to `fun α => ⟨embHom φ α, hmem α⟩`. Establish `hj : Function.Injective j` using `fun a b h => embHom_injective hφ (congrArg Subtype.val h)`.

Establish `h2` using `hs.comp_injective hj`. Use `h2.congr fun α => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, j]`. Both sides reduce to the same expression.
-/
theorem summable_exp_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl

/- English proof (translation)
Use `haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM`. Use `haveI := Fintype.ofFinite (𝓞 K ⧸ M)`. Use `⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩` and prove the remaining obligations. Establish `hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M`. Rewrite using `[← Ideal.Quotient.eq, Ideal.Quotient.mk_out]`.

Establish `hα : F α = F (Quotient.out (Ideal.Quotient.mk M α))`. Use `hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[hα]`. Conclude with `Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)`.
-/
theorem bounded_of_periodic {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

/- English proof (translation)
Introduce `K _ _ _ I _ φ hφ M F hM hF`. Take `⟨C, hC⟩` from `bounded_of_periodic F hM hF`. Use `⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩` and prove the remaining obligations. Use `((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le`.
-/
theorem periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le

end GlobalTheory.HeckeLat
