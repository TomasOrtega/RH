import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LineDegreeBundleStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors

noncomputable section

/- English proof (translation)
Establish `hle : (Submodule.span R {a • x}).toAddSubgroup ≤ (Submodule.span R {x}).toAddSubgroup` using `Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)))`. Rewrite using `[← AddSubgroup.relIndex_mul_index hle]`. Use `congr 1`. Establish `hg : Function.Injective (LinearMap.toSpanSingleton R N x)` using `fun r s h ↦ smul_left_injective R hx h`. Establish `h1 : Submodule.span R {a • x} = Submodule.map (LinearMap.toSpanSingleton R N x) (Ideal.span {a} : Submodule R R)`.

Rewrite using `[Submodule.map_span, Set.image_singleton, LinearMap.toSpanSingleton_apply]`. Establish `h2 : Submodule.span R {x} = Submodule.map (LinearMap.toSpanSingleton R N x) (⊤ : Submodule R R)`. Rewrite using `[Submodule.map_top, LinearMap.span_singleton_eq_range]`. Rewrite using `[h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hg, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]`. Both sides reduce to the same expression.
-/
theorem LineDegreeBundle.index_span_smul {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [IsDomain R] [Module.IsTorsionFree R N] {x : N} (hx : x ≠ 0) (a : R) :
    (Submodule.span R {a • x}).toAddSubgroup.index =
      Submodule.cardQuot (Ideal.span {a} : Ideal R) * (Submodule.span R {x}).toAddSubgroup.index := by
  have hle : (Submodule.span R {a • x}).toAddSubgroup ≤ (Submodule.span R {x}).toAddSubgroup :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)))
  rw [← AddSubgroup.relIndex_mul_index hle]
  congr 1
  have hg : Function.Injective (LinearMap.toSpanSingleton R N x) :=
    fun r s h ↦ smul_left_injective R hx h
  have h1 : Submodule.span R {a • x} = Submodule.map (LinearMap.toSpanSingleton R N x) (Ideal.span {a} : Submodule R R) := by
    rw [Submodule.map_span, Set.image_singleton, LinearMap.toSpanSingleton_apply]
  have h2 : Submodule.span R {x} = Submodule.map (LinearMap.toSpanSingleton R N x) (⊤ : Submodule R R) := by
    rw [Submodule.map_top, LinearMap.span_singleton_eq_range]
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hg, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right]
  rfl

/- English proof (translation)
Rewrite using `[← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, ← Rat.cast_intCast, Algebra.coe_norm_int]`.
-/
theorem LineDegreeBundle.cardQuot_span_singleton {L : Type*} [Field L] [NumberField L] (a : 𝓞 L) :
    (Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 L)) : ℝ) = |(Algebra.norm ℚ (a : L) : ℝ)| := by
  rw [← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Rat.cast_intCast, Algebra.coe_norm_int]

/- English proof (translation)
Rewrite using `[← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]`. Use `congr 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ ↦ ‖φ x‖) (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem LineDegreeBundle.sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ ↦ ‖φ x‖)
    (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

/- English proof (translation)
Simplify using `only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LineDegreeBundle.quad_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (u : Fin n → ℂ) :
    star (z • u) ⬝ᵥ (H *ᵥ (z • u)) = (star z * z) * (star u ⬝ᵥ (H *ᵥ u)) := by
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `h` using `hH.dotProduct_mulVec_pos hu`. Take `⟨hre, him⟩` from `Complex.lt_def.mp h`. Establish `hQ : star u ⬝ᵥ (H *ᵥ u) = ((star u ⬝ᵥ (H *ᵥ u)).re : ℂ)` using `Complex.ext rfl (by simp only [Complex.ofReal_im]; rw [← him]; rfl)`. Use `⟨?_, by simpa using hre⟩` and prove the remaining obligations. Use `conv_lhs => rw [hQ]`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]`.
-/
theorem LineDegreeBundle.quad_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {u : Fin n → ℂ}
    (hu : u ≠ 0) :
    ‖star u ⬝ᵥ (H *ᵥ u)‖ = (star u ⬝ᵥ (H *ᵥ u)).re ∧ 0 < (star u ⬝ᵥ (H *ᵥ u)).re := by
  have h := hH.dotProduct_mulVec_pos hu
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  have hQ : star u ⬝ᵥ (H *ᵥ u) = ((star u ⬝ᵥ (H *ᵥ u)).re : ℂ) :=
    Complex.ext rfl (by simp only [Complex.ofReal_im]; rw [← him]; rfl)
  refine ⟨?_, by simpa using hre⟩
  conv_lhs => rw [hQ]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]

/- English proof (translation)
Introduce `K _ _ n F hF K' _ _ _ E φ hE v hv`. Use `set M : Submodule (𝓞 K') E.carrier := (satLine v).comap φ.toLinearMap with hM`. Use `set v' : Fin n → K' := fun j ↦ (v j : K') with hv'`. Set `ψ : E.carrier →ₗ[𝓞 K'] (Fin n → K')` to `intoField K' n ∘ₗ φ.toLinearMap`. Establish `hψ_apply : ∀ x j, ψ x j = (φ x j : K')` using `fun _ _ ↦ rfl`.

Establish `hψ : Function.Injective ψ`. Introduce `x y h`. Apply `φ.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Conclude with `RingOfIntegers.ext (congrFun h j)`.

Establish `: Module.IsTorsionFree (𝓞 K') E.carrier`. Use `Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `Or.inr (φ.injective ?_)` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Establish `h'` using `congrFun (congrArg φ h) j`. Rewrite `h'` using `[map_smul, map_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]`. Rewrite using `[map_zero, Pi.zero_apply]`. Conclude with `(mul_eq_zero.mp h').resolve_left hr`.

Establish `: Module.IsTorsionFree (𝓞 K') M` using `Function.Injective.moduleIsTorsionFree M.subtype Subtype.val_injective (fun _ _ ↦ rfl)`. Establish `hmem : ∀ x : E.carrier, x ∈ M ↔ ∃ c : K', ∀ j, (φ x j : K') = c * v j` using `fun x ↦ Iff.rfl`. Establish `hmM : φ.symm v ∈ M` using `(hmem _).2 ⟨1, fun j ↦ by simp⟩`. Use `set m : M := ⟨φ.symm v, hmM⟩ with hm`. Establish `hψm : ψ m = v'` using `by funext j; simp [hψ_apply, m, hv']`.

Establish `hm0 : m ≠ 0`. Introduce `h`. Apply `hv` to reduce the goal to its premises. Establish `h' : ψ m = ψ 0` using `congrArg (fun y : M ↦ ψ (y : E.carrier)) h`. Rewrite `h'` using `[hψm, map_zero]`.

Use function extensionality and compare the values at `j`. Conclude with `RingOfIntegers.ext (by simpa [hv'] using congrFun h' j)`. Establish `hrel : ∀ x : M, ∃ (c : K') (a b : 𝓞 K'), b ≠ 0 ∧ ψ x = c • v' ∧ c * (b : K') = a ∧ b • x = a • m`. Introduce `x`. Take `⟨c, hc⟩` from `(hmem x).1 x.2`.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (𝓞 K')⁰ c`. Simplify using `only at hab`. Establish `h1 : ψ x = c • v'` using `by funext j; rw [hψ_apply, hc j]; rfl`. Use `⟨c, a, b, nonZeroDivisors.coe_ne_zero b, h1, hab, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hψ` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, map_smul, map_smul, h1, hψm]`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, ← hab]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hrank : E.rank M = 1`. Unfold `HermitianBundle.rank`. Apply `le_antisymm` to reduce the goal to its premises. Assume the negation of the conclusion as `h push Not at h`.

Take `⟨g, hg⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 K') (M := M) (n := 2) (by omega)`. Establish `hg2 : LinearIndependent (𝓞 K') ![g 0, g 1]`. Use `hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.

Take `⟨-, a₁, b₁, hb₁, -, -, h₁⟩` from `hrel (g 0)`. Take `⟨-, a₂, b₂, hb₂, -, -, h₂⟩` from `hrel (g 1)`. Establish `h0` using `LinearIndependent.pair_iff.mp hg2 (a₂ * b₁) (-(a₁ * b₂)) (by`. Rewrite using `[mul_smul, h₁, neg_smul, mul_smul, h₂, smul_smul, smul_smul, mul_comm a₂ a₁, add_neg_cancel])`. Establish `ha₁ : a₁ = 0` using `(mul_eq_zero.mp (neg_eq_zero.mp h0.2)).resolve_right hb₂`.

Rewrite `h₁` using `[ha₁, zero_smul]`. Conclude with `hg.ne_zero 0 ((smul_eq_zero.mp h₁).resolve_left hb₁)`. Use `(linearIndependent_unique_iff (v := fun _ : Fin 1 ↦ m) (R := 𝓞 K')).mpr hm0` as an intermediate fact. Simplify using `using this.fintype_card_le_finrank`. Establish `hIm : (Submodule.span (𝓞 K') {m}).toAddSubgroup.index ≠ 0`.

Take `⟨j₀, hj₀⟩` from `Function.ne_iff.mp hv`. Establish `hd : v j₀ ≠ 0` using `hj₀`. Establish `hfin : Finite (𝓞 K' ⧸ Ideal.span {v j₀})`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]`.

Conclude with `Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd)`. Set `g : M →ₗ[𝓞 K'] 𝓞 K' ⧸ Ideal.span {v j₀}` to `(Ideal.span {v j₀}).mkQ ∘ₗ LinearMap.proj j₀ ∘ₗ φ.toLinearMap ∘ₗ M.subtype`. Establish `hker : (LinearMap.ker g).toAddSubgroup ≤ (Submodule.span (𝓞 K') {m}).toAddSubgroup`. Introduce `x hx`. Establish `hx' : g x = 0` using `hx`.

Establish `h1 : φ x j₀ ∈ Ideal.span {v j₀}` using `(Submodule.Quotient.mk_eq_zero _).mp hx'`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp h1`. Take `⟨c, hc⟩` from `(hmem x).1 x.2`. Establish `hct : c = t`. Establish `h2` using `hc j₀`.

Rewrite `h2` using `[← ht]`. Move the coercions through the operations in `at h2`. Conclude with `(mul_right_cancel₀ (by exact_mod_cast hd) h2).symm`. Express the relevant statement in the definitionally equal form `x ∈ Submodule.span (𝓞 K') {m}`. Rewrite using `[Submodule.mem_span_singleton]`.

Use `⟨t, Subtype.ext (hψ ?_)⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, map_smul, hψm]`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, hψ_apply, hc j, hct, Algebra.smul_def]`. Establish `h2 : (LinearMap.ker g).toAddSubgroup.index ≠ 0`.

Establish `: (LinearMap.ker g).toAddSubgroup = (g.toAddMonoidHom).ker` using `AddSubgroup.ext fun _ ↦ Iff.rfl`. Rewrite using `[this, AddSubgroup.index_ker]`. Conclude with `Nat.card_pos.ne'`. Conclude with `ne_zero_of_dvd_ne_zero h2 (AddSubgroup.index_dvd_of_le hker)`. Set `Q : (K' →+* ℂ) → ℂ` to `fun σ' ↦ star (embVec σ' v') ⬝ᵥ (F.metric (σ'.comp (algebraMap K K')) *ᵥ embVec σ' v')`.

Establish `hQ : ∀ σ' : K' →+* ℂ, ‖Q σ'‖ = (Q σ').re ∧ 0 < (Q σ').re`. Introduce `σ'`. Apply `LineDegreeBundle.quad_pos (F.posDef _)` to reduce the goal to its premises. Take `⟨j₀, hj₀⟩` from `Function.ne_iff.mp hv`. Introduce `h`.

Establish `h3` using `congrFun h j₀`. Simplify using `only [embVec, Pi.zero_apply, map_eq_zero_iff _ σ'.injective, hv'] at h3`. Conclude with `hj₀ (RingOfIntegers.ext (by simpa using h3))`. Establish `hdeg : ∀ (r : ℕ) (f : Fin r → M), r = 1 → LinearIndependent (𝓞 K') f → HermitianBundle.degreeWith E M f = Real.log ((Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℝ) - 1 / 2 * ∑ σ' : K' →+* ℂ, Real.log (Q σ').re`. Introduce and unpack `r f rfl hf`.

Establish `hx : f 0 ≠ 0` using `hf.ne_zero 0`. Take `⟨c, a, b, hb, hxc, hab, hba⟩` from `hrel (f 0)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hxc` using `[zero_smul]`.

Conclude with `hx (Subtype.ext (hψ (by rw [hxc, Submodule.coe_zero, map_zero])))`. Establish `hxj : ∀ j, (φ (f 0 : E.carrier) j : K') = c * v' j` using `fun j ↦ congrFun hxc j`. Establish `hidx : ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) = (Submodule.span (𝓞 K') {m}).toAddSubgroup.index * |(Algebra.norm ℚ c : ℝ)|`. Establish `e1` using `LineDegreeBundle.index_span_smul hx b`. Establish `e2` using `LineDegreeBundle.index_span_smul hm0 a`.

Rewrite `e1` using `[hba, e2]`. Establish `e3 : ((Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 K')) * (Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℕ) : ℝ) = ((Submodule.cardQuot (Ideal.span {b} : Ideal (𝓞 K')) * (Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℕ) : ℝ)` using `by rw [e1]`. Move the coercions through the operations in `at e3`. Rewrite `e3` using `[LineDegreeBundle.cardQuot_span_singleton, LineDegreeBundle.cardQuot_span_singleton, ← hab, map_mul, Rat.cast_mul, abs_mul]`. Establish `hbn : |(Algebra.norm ℚ (b : K') : ℝ)| ≠ 0`.

Rewrite using `[abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]`. Conclude with `hb` after adjusting the coercions. Apply `mul_right_cancel₀ hbn` to reduce the goal to its premises. Take the linear combination `-e3`. Establish `hgram : ∀ σ' : K' →+* ℂ, Real.log ‖HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier))‖ = 2 * Real.log ‖σ' c‖ + Real.log (Q σ').re`.

Introduce `σ'`. Establish `hv1 : (fun j ↦ σ' (φ (f 0 : E.carrier) j : K')) = σ' c • embVec σ' v'`. Use function extensionality and compare the values at `j`. Rewrite using `[hxj j, map_mul]`. Both sides reduce to the same expression.

Establish `: HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier)) = (star (σ' c) * σ' c) * Q σ'`. Unfold `HermitianBundle.gramDet`. Rewrite using `[Matrix.det_unique, Matrix.of_apply]`. Rewrite using `[show (default : Fin 1) = 0 from rfl, hE σ', hv1, LineDegreeBundle.quad_smul]`. Rewrite using `[this, norm_mul, norm_mul, norm_star, (hQ σ').1, Real.log_mul, Real.log_mul, ← two_mul]`.

Conclude with `norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)`. Conclude with `norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)`. Conclude with `mul_ne_zero (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)) (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0))`. Conclude with `(hQ σ').2.ne'`. Unfold `HermitianBundle.degreeWith`.

Rewrite using `[Set.range_unique, show (default : Fin 1) = 0 from rfl, ← Submodule.cardQuot_apply]`. Express the relevant statement in the definitionally equal form `Real.log ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) - _ = _`. Simplify using `only [hgram]`. Rewrite using `[hidx, Finset.sum_add_distrib, ← Finset.mul_sum, LineDegreeBundle.sum_log_norm hc0, Real.log_mul (by exact_mod_cast hIm) (by simpa [abs_ne_zero, Algebra.norm_ne_zero_iff] using hc0)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinj : Function.Injective (ψ ∘ₗ M.subtype)` using `hψ.comp Subtype.val_injective`. Establish `hA : (satLine v).map (intoField K' n) = (⊤ : Submodule (𝓞 K') M).map (ψ ∘ₗ M.subtype)`. Rewrite using `[Submodule.map_comp, Submodule.map_subtype_top, hM, Submodule.map_comp, Submodule.map_comap_eq_of_surjective φ.surjective]`. Establish `hB : Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v') = (Submodule.span (𝓞 K') {m}).map (ψ ∘ₗ M.subtype)`. Rewrite using `[Submodule.map_span, Set.image_singleton, Set.range_const]`.

Simplify using `[hψm]`. Establish `hgen : genIndex ((satLine v).map (intoField K' n)).toAddSubgroup (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v')).toAddSubgroup = (Submodule.span (𝓞 K') {m}).toAddSubgroup.index`. Unfold `genIndex`. Rewrite using `[hA, hB, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_eq_one.mpr le_top]`. Simplify using the standard rewrite rules.

Unfold `HermitianBundle.normDegree HermitianBundle.degree HermLattice.lineDegree normalise subDegree`. Rewrite using `[hdeg _ _ hrank (HermitianBundle.exists_linearIndependent_rank E M).choose_spec, hF, ← satLine_map_eq v, hgen]`. Use `congr 3`. Use `Finset.sum_congr rfl fun σ' _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_unique]`.

Both sides reduce to the same expression.
-/
theorem LineDegreeBundle.proof : LineDegreeBundle.Statement := by
  intro K _ _ n F hF K' _ _ _ E φ hE v hv
  classical
  set M : Submodule (𝓞 K') E.carrier := (satLine v).comap φ.toLinearMap with hM
  set v' : Fin n → K' := fun j ↦ (v j : K') with hv'
  let ψ : E.carrier →ₗ[𝓞 K'] (Fin n → K') := intoField K' n ∘ₗ φ.toLinearMap
  have hψ_apply : ∀ x j, ψ x j = (φ x j : K') := fun _ _ ↦ rfl
  have hψ : Function.Injective ψ := by
    intro x y h
    apply φ.injective
    funext j
    exact RingOfIntegers.ext (congrFun h j)
  have : Module.IsTorsionFree (𝓞 K') E.carrier := by
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h ↦ ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (φ.injective ?_)
    funext j
    have h' := congrFun (congrArg φ h) j
    rw [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h'
    rw [map_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp h').resolve_left hr
  have : Module.IsTorsionFree (𝓞 K') M :=
    Function.Injective.moduleIsTorsionFree M.subtype Subtype.val_injective (fun _ _ ↦ rfl)
  have hmem : ∀ x : E.carrier, x ∈ M ↔ ∃ c : K', ∀ j, (φ x j : K') = c * v j := fun x ↦ Iff.rfl
  have hmM : φ.symm v ∈ M := (hmem _).2 ⟨1, fun j ↦ by simp⟩
  set m : M := ⟨φ.symm v, hmM⟩ with hm
  have hψm : ψ m = v' := by funext j; simp [hψ_apply, m, hv']
  have hm0 : m ≠ 0 := by
    intro h
    apply hv
    have h' : ψ m = ψ 0 := congrArg (fun y : M ↦ ψ (y : E.carrier)) h
    rw [hψm, map_zero] at h'
    funext j
    exact RingOfIntegers.ext (by simpa [hv'] using congrFun h' j)

  have hrel : ∀ x : M, ∃ (c : K') (a b : 𝓞 K'), b ≠ 0 ∧ ψ x = c • v' ∧ c * (b : K') = a ∧
      b • x = a • m := by
    intro x
    obtain ⟨c, hc⟩ := (hmem x).1 x.2
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (𝓞 K')⁰ c
    dsimp only at hab
    have h1 : ψ x = c • v' := by funext j; rw [hψ_apply, hc j]; rfl
    refine ⟨c, a, b, nonZeroDivisors.coe_ne_zero b, h1, hab, ?_⟩
    apply Subtype.ext
    apply hψ
    rw [Submodule.coe_smul, Submodule.coe_smul, map_smul, map_smul, h1, hψm]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def, Algebra.smul_def, ← hab]
    ring

  have hrank : E.rank M = 1 := by
    unfold HermitianBundle.rank
    apply le_antisymm
    · by_contra h
      push Not at h
      obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K') (M := M) (n := 2) (by omega)
      have hg2 : LinearIndependent (𝓞 K') ![g 0, g 1] := by
        convert hg using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨-, a₁, b₁, hb₁, -, -, h₁⟩ := hrel (g 0)
      obtain ⟨-, a₂, b₂, hb₂, -, -, h₂⟩ := hrel (g 1)
      have h0 := LinearIndependent.pair_iff.mp hg2 (a₂ * b₁) (-(a₁ * b₂)) (by
        rw [mul_smul, h₁, neg_smul, mul_smul, h₂, smul_smul, smul_smul, mul_comm a₂ a₁, add_neg_cancel])
      have ha₁ : a₁ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h0.2)).resolve_right hb₂
      rw [ha₁, zero_smul] at h₁
      exact hg.ne_zero 0 ((smul_eq_zero.mp h₁).resolve_left hb₁)
    · have := (linearIndependent_unique_iff (v := fun _ : Fin 1 ↦ m) (R := 𝓞 K')).mpr hm0
      simpa using this.fintype_card_le_finrank

  have hIm : (Submodule.span (𝓞 K') {m}).toAddSubgroup.index ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
    have hd : v j₀ ≠ 0 := hj₀
    have hfin : Finite (𝓞 K' ⧸ Ideal.span {v j₀}) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
      exact Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd)
    let g : M →ₗ[𝓞 K'] 𝓞 K' ⧸ Ideal.span {v j₀} :=
      (Ideal.span {v j₀}).mkQ ∘ₗ LinearMap.proj j₀ ∘ₗ φ.toLinearMap ∘ₗ M.subtype
    have hker : (LinearMap.ker g).toAddSubgroup ≤ (Submodule.span (𝓞 K') {m}).toAddSubgroup := by
      intro x hx
      have hx' : g x = 0 := hx
      have h1 : φ x j₀ ∈ Ideal.span {v j₀} := (Submodule.Quotient.mk_eq_zero _).mp hx'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h1
      obtain ⟨c, hc⟩ := (hmem x).1 x.2
      have hct : c = t := by
        have h2 := hc j₀
        rw [← ht] at h2
        push_cast at h2
        exact (mul_right_cancel₀ (by exact_mod_cast hd) h2).symm
      change x ∈ Submodule.span (𝓞 K') {m}
      rw [Submodule.mem_span_singleton]
      refine ⟨t, Subtype.ext (hψ ?_)⟩
      rw [Submodule.coe_smul, map_smul, hψm]
      funext j
      rw [Pi.smul_apply, hψ_apply, hc j, hct, Algebra.smul_def]
    have h2 : (LinearMap.ker g).toAddSubgroup.index ≠ 0 := by
      have : (LinearMap.ker g).toAddSubgroup = (g.toAddMonoidHom).ker := AddSubgroup.ext fun _ ↦ Iff.rfl
      rw [this, AddSubgroup.index_ker]
      exact Nat.card_pos.ne'
    exact ne_zero_of_dvd_ne_zero h2 (AddSubgroup.index_dvd_of_le hker)

  let Q : (K' →+* ℂ) → ℂ := fun σ' ↦
    star (embVec σ' v') ⬝ᵥ (F.metric (σ'.comp (algebraMap K K')) *ᵥ embVec σ' v')
  have hQ : ∀ σ' : K' →+* ℂ, ‖Q σ'‖ = (Q σ').re ∧ 0 < (Q σ').re := by
    intro σ'
    apply LineDegreeBundle.quad_pos (F.posDef _)
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
    intro h
    have h3 := congrFun h j₀
    simp only [embVec, Pi.zero_apply, map_eq_zero_iff _ σ'.injective, hv'] at h3
    exact hj₀ (RingOfIntegers.ext (by simpa using h3))

  have hdeg : ∀ (r : ℕ) (f : Fin r → M), r = 1 → LinearIndependent (𝓞 K') f →
      HermitianBundle.degreeWith E M f =
        Real.log ((Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℝ) -
          1 / 2 * ∑ σ' : K' →+* ℂ, Real.log (Q σ').re := by
    rintro r f rfl hf
    have hx : f 0 ≠ 0 := hf.ne_zero 0
    obtain ⟨c, a, b, hb, hxc, hab, hba⟩ := hrel (f 0)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hxc
      exact hx (Subtype.ext (hψ (by rw [hxc, Submodule.coe_zero, map_zero])))
    have hxj : ∀ j, (φ (f 0 : E.carrier) j : K') = c * v' j := fun j ↦ congrFun hxc j

    have hidx : ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) =
        (Submodule.span (𝓞 K') {m}).toAddSubgroup.index * |(Algebra.norm ℚ c : ℝ)| := by
      have e1 := LineDegreeBundle.index_span_smul hx b
      have e2 := LineDegreeBundle.index_span_smul hm0 a
      rw [hba, e2] at e1
      have e3 : ((Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 K')) *
          (Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℕ) : ℝ) =
          ((Submodule.cardQuot (Ideal.span {b} : Ideal (𝓞 K')) *
          (Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℕ) : ℝ) := by rw [e1]
      push_cast at e3
      rw [LineDegreeBundle.cardQuot_span_singleton, LineDegreeBundle.cardQuot_span_singleton, ← hab,
        map_mul, Rat.cast_mul, abs_mul] at e3
      have hbn : |(Algebra.norm ℚ (b : K') : ℝ)| ≠ 0 := by
        rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
        exact_mod_cast hb
      apply mul_right_cancel₀ hbn
      linear_combination -e3

    have hgram : ∀ σ' : K' →+* ℂ,
        Real.log ‖HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier))‖ =
          2 * Real.log ‖σ' c‖ + Real.log (Q σ').re := by
      intro σ'
      have hv1 : (fun j ↦ σ' (φ (f 0 : E.carrier) j : K')) = σ' c • embVec σ' v' := by
        funext j
        rw [hxj j, map_mul]
        rfl
      have : HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier)) = (star (σ' c) * σ' c) * Q σ' := by
        unfold HermitianBundle.gramDet
        rw [Matrix.det_unique, Matrix.of_apply]
        rw [show (default : Fin 1) = 0 from rfl, hE σ', hv1, LineDegreeBundle.quad_smul]
      rw [this, norm_mul, norm_mul, norm_star, (hQ σ').1, Real.log_mul, Real.log_mul, ← two_mul]
      · exact norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)
      · exact norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)
      · exact mul_ne_zero (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0))
          (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0))
      · exact (hQ σ').2.ne'
    unfold HermitianBundle.degreeWith
    rw [Set.range_unique, show (default : Fin 1) = 0 from rfl, ← Submodule.cardQuot_apply]
    change Real.log ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) - _ = _
    simp only [hgram]
    rw [hidx, Finset.sum_add_distrib, ← Finset.mul_sum, LineDegreeBundle.sum_log_norm hc0,
      Real.log_mul (by exact_mod_cast hIm) (by simpa [abs_ne_zero, Algebra.norm_ne_zero_iff] using hc0)]
    ring

  have hinj : Function.Injective (ψ ∘ₗ M.subtype) := hψ.comp Subtype.val_injective
  have hA : (satLine v).map (intoField K' n) = (⊤ : Submodule (𝓞 K') M).map (ψ ∘ₗ M.subtype) := by
    rw [Submodule.map_comp, Submodule.map_subtype_top, hM, Submodule.map_comp,
      Submodule.map_comap_eq_of_surjective φ.surjective]
  have hB : Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v') =
      (Submodule.span (𝓞 K') {m}).map (ψ ∘ₗ M.subtype) := by
    rw [Submodule.map_span, Set.image_singleton, Set.range_const]
    simp [hψm]
  have hgen : genIndex ((satLine v).map (intoField K' n)).toAddSubgroup
      (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v')).toAddSubgroup =
      (Submodule.span (𝓞 K') {m}).toAddSubgroup.index := by
    unfold genIndex
    rw [hA, hB, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_eq_one.mpr le_top]
    simp
  unfold HermitianBundle.normDegree HermitianBundle.degree HermLattice.lineDegree normalise subDegree
  rw [hdeg _ _ hrank (HermitianBundle.exists_linearIndependent_rank E M).choose_spec, hF,
    ← satLine_map_eq v, hgen]
  congr 3
  refine Finset.sum_congr rfl fun σ' _ ↦ ?_
  rw [Matrix.det_unique]
  rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
