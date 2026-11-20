import Mathlib
import GroundTheory.AutomorphicForms.ReductionHeight
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.IdeleGroups.Restricted
import GroundTheory.GlobalFields.IdeleGroups.UnitBound

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Establish `h` using `RestrictedProduct.isOpen_forall_imp_mem (R := fun v : HeightOneSpectrum (𝓞 K) => GL (Fin n) (v.adicCompletion K)) (A := fun v => (GLnLocal.integralGL (v.adicCompletion K) n : Set _)) (fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n) (p := fun v => v ∉ S)`. Conclude with `(h.preimage continuous_snd).preimage (AdelicGLn.restrictedProductEquiv K n).continuous`.
-/
theorem isOpen_setOf_forall_not_mem_imp (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => GL (Fin n) (v.adicCompletion K))
    (A := fun v => (GLnLocal.integralGL (v.adicCompletion K) n : Set _))
    (fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n) (p := fun v => v ∉ S)
  exact (h.preimage continuous_snd).preimage (AdelicGLn.restrictedProductEquiv K n).continuous

/- English proof (translation)
Take `⟨T, hT⟩` from `hC.elim_finite_subcover (fun S : Finset (HeightOneSpectrum (𝓞 K)) => {g : AdelicGLn.AdelicGL K n | ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n}) (fun S => isOpen_setOf_forall_not_mem_imp S) (fun g _ => by`. Establish `hfin` using `Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n g)`. Use `mem_iUnion.2 ⟨hfin.toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hv (hfin.mem_toFinset.2 h))`.

Use `⟨T.sup id, fun g hg v hv => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hgS⟩` from `mem_iUnion₂.1 (hT hg)`. Conclude with `hgS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)`.
-/
theorem exists_finite_forall_mem_integralGL {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ g ∈ C, ∀ v, v ∉ S →
      finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 K)) => {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n})
    (fun S => isOpen_setOf_forall_not_mem_imp S) (fun g _ => by
      have hfin := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n g)
      refine mem_iUnion.2 ⟨hfin.toFinset, fun v hv => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 h))
  refine ⟨T.sup id, fun g hg v hv => ?_⟩
  obtain ⟨S, hS, hgS⟩ := mem_iUnion₂.1 (hT hg)
  exact hgS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

/- English proof (translation)
Rewrite using `[finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset) (fun a ha => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 ha))), finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset) (fun a ha => Finset.mem_coe.2 (Finset.mem_union_right …`. Conclude with `Finset.prod_le_prod (fun a _ => h0 a) fun a _ => h a`.
-/
theorem finprod_le_finprod_of_nonneg {α : Type*} {f g : α → ℝ}
    (hf : (Function.mulSupport f).Finite) (hg : (Function.mulSupport g).Finite)
    (h0 : ∀ a, 0 ≤ f a) (h : ∀ a, f a ≤ g a) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 ha))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_right _ (hg.mem_toFinset.2 ha)))]
  exact Finset.prod_le_prod (fun a _ => h0 a) fun a _ => h a

/- English proof (translation)
Establish `hbS : (Function.mulSupport b).Finite` using `S.finite_toSet.subset fun v hv => by`. Assume the negation of the conclusion as `h`. Conclude with `hv (hb1 v h)`. Establish `hprod : ∏ᶠ v, b v = ∏ v ∈ S, b v` using `finprod_eq_prod_of_mulSupport_subset b fun v hv => by`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hb1 v h)`. Rewrite using `[adelicNorm, adelicNorm]`. Establish `hinf' : ∏ w, euclidNorm (infComp w y) ^ w.mult ≤ (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => by`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _`. Establish `hfin' : ∏ᶠ v, ‖finComp v y‖ ≤ (∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖`. Rewrite using `[← hprod, ← finprod_mul_distrib hbS hy'.finite_mulSupport]`. Use `finprod_le_finprod_of_nonneg hy.finite_mulSupport ?_ (fun _ => norm_nonneg _) hfin` and prove the remaining obligations.

Conclude with `(hbS.union hy'.finite_mulSupport).subset (Function.mulSupport_mul _ _)`. Establish `h1 : 0 ≤ ∏ᶠ v, ‖finComp v y‖` using `finprod_nonneg fun _ => norm_nonneg _`. Establish `h2 : 0 ≤ (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult` using `le_trans (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) hinf'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem adelicNorm_le_of_local {y y' : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hy' : HasFiniteContent y') (a : InfinitePlace K → ℝ) (b : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hinf : ∀ w, euclidNorm (infComp w y) ≤ a w * euclidNorm (infComp w y'))
    (hb1 : ∀ v, v ∉ S → b v = 1)
    (hfin : ∀ v, ‖finComp v y‖ ≤ b v * ‖finComp v y'‖) :
    adelicNorm y ≤ (∏ w, a w ^ w.mult) * (∏ v ∈ S, b v) * adelicNorm y' := by
  have hbS : (Function.mulSupport b).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  have hprod : ∏ᶠ v, b v = ∏ v ∈ S, b v :=
    finprod_eq_prod_of_mulSupport_subset b fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  rw [adelicNorm, adelicNorm]
  have hinf' : ∏ w, euclidNorm (infComp w y) ^ w.mult ≤
      (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _
  have hfin' : ∏ᶠ v, ‖finComp v y‖ ≤ (∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖ := by
    rw [← hprod, ← finprod_mul_distrib hbS hy'.finite_mulSupport]
    refine finprod_le_finprod_of_nonneg hy.finite_mulSupport ?_ (fun _ => norm_nonneg _) hfin
    exact (hbS.union hy'.finite_mulSupport).subset (Function.mulSupport_mul _ _)
  have h1 : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult :=
    le_trans (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) hinf'
  calc (∏ w, euclidNorm (infComp w y) ^ w.mult) * ∏ᶠ v, ‖finComp v y‖
      ≤ ((∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult) *
          ((∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖) := mul_le_mul hinf' hfin' h1 h2
    _ = _ := by ring

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (mul_nonneg hm (norm_nonneg z))).2 fun j => ?_` and prove the remaining obligations. Simplify using `only [vecMul, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hm (norm_nonneg z)) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, mul_comm]`. Conclude with `mul_le_mul (hM i j) (norm_le_pi_norm z i) (norm_nonneg _) hm`.
-/
theorem norm_vecMul_le_of_norm_le (v : HeightOneSpectrum (𝓞 K))
    {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → v.adicCompletion K) : ‖z ᵥ* M‖ ≤ m * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hm (norm_nonneg z))).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hm (norm_nonneg z))
    fun i _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (hM i j) (norm_le_pi_norm z i) (norm_nonneg _) hm

/- English proof (translation)
Use `(euclidNorm_le_sqrt_mul _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (by positivity [euclidNorm_nonneg z])).2 fun j => ?_` and prove the remaining obligations. Simplify using `only [vecMul, dotProduct]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, mul_comm]`. Conclude with `mul_le_mul (hM i j) (norm_le_euclidNorm z i) (norm_nonneg _) hm`. Use `_ = n * m * euclidNorm z := by simp [mul_assoc]`.
-/
theorem euclidNorm_vecMul_le {E : Type*} [NormedField E] {M : Matrix (Fin n) (Fin n) E} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → E) :
    euclidNorm (z ᵥ* M) ≤ √n * (n * m) * euclidNorm z := by
  refine (euclidNorm_le_sqrt_mul _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity [euclidNorm_nonneg z])).2 fun j => ?_
  simp only [vecMul, dotProduct]
  calc ‖∑ i, z i * M i j‖ ≤ ∑ i, ‖z i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, m * euclidNorm z := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul (hM i j) (norm_le_euclidNorm z i) (norm_nonneg _) hm
    _ = n * m * euclidNorm z := by simp [mul_assoc]

/- English proof (translation)
Take `⟨m, hm⟩` from `hC.exists_bound_of_continuousOn hf.continuousOn`. Conclude with `⟨max m 1, le_max_right _ _, fun x hx => (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hm x hx).trans (le_max_left _ _))⟩`.
-/
theorem exists_one_le_bound {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    {f : X → ℝ} (hf : Continuous f) : ∃ m : ℝ, 1 ≤ m ∧ ∀ x ∈ C, f x ≤ m := by
  obtain ⟨m, hm⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max m 1, le_max_right _ _, fun x hx =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hm x hx).trans (le_max_left _ _))⟩

/- English proof (translation)
The claim follows from `(continuous_apply w).comp (continuous_fst.comp (AdelicGLn.restrictedProductEquiv K n).continuous)`.
-/
theorem continuous_infAt (w : InfinitePlace K) :
    Continuous (infAt (n := n) w : AdelicGLn.AdelicGL K n → GL (Fin n) w.Completion) :=
  (continuous_apply w).comp (continuous_fst.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

/- English proof (translation)
The claim follows from `(RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)`.
-/
theorem continuous_finAt (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finAt (n := n) v : AdelicGLn.AdelicGL K n → GL (Fin n) (v.adicCompletion K)) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

/- English proof (translation)
The claim follows from `(continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin n) (Fin n) R))`.
-/
theorem continuous_GL_apply {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (i j : Fin n) : Continuous fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j :=
  (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin n) (Fin n) R))

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨1, one_pos, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩`. Take `⟨S, hS⟩` from `exists_finite_forall_mem_integralGL hC`. Establish `hinf : ∀ w : InfinitePlace K, ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖ ≤ m` using `fun w => by`. Take `⟨m, hm1, hm⟩` from `exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n => ∑ i, ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖) (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ((continuous_GL_apply i j).comp ((continuous_infAt w).inv)).norm)`.

Use `⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩` and prove the remaining obligations. Conclude with `(Finset.single_le_sum (f := fun j => ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_non …`. Establish `hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖ ≤ m` using `fun v => by`. Take `⟨m, hm1, hm⟩` from `exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n => ∑ i, ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖) (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ((continuous_GL_apply i j).comp ((continuous_finAt v).inv)).norm)`. Use `⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩` and prove the remaining obligations.

Conclude with `(Finset.single_le_sum (f := fun j => ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖) (fun _ _ => Finset.sum_nonneg fun …`. Use `choose a ha1 ha using hinf`. Use `choose b hb1 hb using hfin`. Use `set b' : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then b v else 1 with hb'`. Use `set P : ℝ := (∏ w, (√n * (n * a w)) ^ w.mult) * ∏ v ∈ S, b' v with hP`.

Establish `hPpos : 0 < P`. Use `mul_pos (Finset.prod_pos fun w _ => pow_pos ?_ _) (Finset.prod_pos fun v _ => ?_)` and prove the remaining obligations. Establish `: (0 : ℝ) < n` using `Nat.cast_pos.2 hn`. Conclude with `mul_pos (Real.sqrt_pos.2 this) (mul_pos this (lt_of_lt_of_le one_pos (ha1 w)))`. Rewrite using `[hb'] dsimp only split_ifs`.

Conclude with `lt_of_lt_of_le one_pos (hb1 v)`. Use `⟨P⁻¹, inv_pos.2 hPpos, fun g hg x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[inv_le_iff_one_le_mul₀' hPpos]`. Use `set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy`. Establish `hxy : ratVec x = y ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])`.

Rewrite using `[hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]`. Use `(one_le_adelicNorm_ratVec hx).trans ?_` and prove the remaining obligations. Rewrite using `[hxy]`. Use `(adelicNorm_le_of_local ((hasFiniteContent_height g hx).vecMul g⁻¹) (hasFiniteContent_height g hx) (fun w => √n * (n * a w)) b' S (fun w => ?_) (fun v hv => by rw [hb']; dsimp only; rw [if_neg hv]) (fun v => ?_)).trans (le_of_eq rfl)` and prove the remaining obligations. Rewrite using `[infComp_vecMul_GL, show infAt w g⁻¹ = (infAt w g)⁻¹ by simp [infAt, map_inv]]`.

Conclude with `euclidNorm_vecMul_le (zero_le_one.trans (ha1 w)) (ha w g hg) _`. Rewrite using `[finComp_vecMul_GL, show finAt v g⁻¹ = (finAt v g)⁻¹ by`. Simplify using `[finAt, map_inv, RestrictedProduct.inv_apply]]`. Rewrite using `[hb']`. Simplify using `only`.

Use `split_ifs with hv`. Conclude with `norm_vecMul_le_of_norm_le v (zero_le_one.trans (hb1 v)) (hb v g hg) _`. Rewrite using `[norm_vecMul_integralGL v (inv_mem (hS g hg v hv)), one_mul]`.
-/
theorem exists_pos_le_height {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩
  obtain ⟨S, hS⟩ := exists_finite_forall_mem_integralGL hC

  have hinf : ∀ w : InfinitePlace K, ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖ ≤ m := fun w => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_infAt w).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖ ≤ m := fun v => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_finAt v).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  choose a ha1 ha using hinf
  choose b hb1 hb using hfin
  set b' : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  set P : ℝ := (∏ w, (√n * (n * a w)) ^ w.mult) * ∏ v ∈ S, b' v with hP
  have hPpos : 0 < P := by
    refine mul_pos (Finset.prod_pos fun w _ => pow_pos ?_ _) (Finset.prod_pos fun v _ => ?_)
    · have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      exact mul_pos (Real.sqrt_pos.2 this) (mul_pos this (lt_of_lt_of_le one_pos (ha1 w)))
    · rw [hb']
      dsimp only
      split_ifs
      exact lt_of_lt_of_le one_pos (hb1 v)
  refine ⟨P⁻¹, inv_pos.2 hPpos, fun g hg x hx => ?_⟩
  rw [inv_le_iff_one_le_mul₀' hPpos]
  set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  have hxy : ratVec x = y ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  refine (one_le_adelicNorm_ratVec hx).trans ?_
  rw [hxy]
  refine (adelicNorm_le_of_local ((hasFiniteContent_height g hx).vecMul g⁻¹)
    (hasFiniteContent_height g hx) (fun w => √n * (n * a w)) b' S (fun w => ?_)
    (fun v hv => by rw [hb']; dsimp only; rw [if_neg hv]) (fun v => ?_)).trans (le_of_eq rfl)
  · rw [infComp_vecMul_GL, show infAt w g⁻¹ = (infAt w g)⁻¹ by simp [infAt, map_inv]]
    exact euclidNorm_vecMul_le (zero_le_one.trans (ha1 w)) (ha w g hg) _
  · rw [finComp_vecMul_GL, show finAt v g⁻¹ = (finAt v g)⁻¹ by
      simp [finAt, map_inv, RestrictedProduct.inv_apply]]
    rw [hb']
    dsimp only
    split_ifs with hv
    · exact norm_vecMul_le_of_norm_le v (zero_le_one.trans (hb1 v)) (hb v g hg) _
    · rw [norm_vecMul_integralGL v (inv_mem (hS g hg v hv)), one_mul]

/- English proof (translation)
Use `discreteTopology_principalSubgroup K` as an intermediate fact. Establish `hc : IsCompact ((Subtype.val : AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' D)` using `(isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD`. Set `f : K → AdeleRing.principalSubgroup (𝓞 K) K` to `fun k => ⟨algebraMap K 𝔸[K] k, k, rfl⟩`. Establish `hf : Function.Injective f` using `fun a b h => AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h)`. Conclude with `(hc.finite_of_discrete.preimage hf.injOn).subset fun k hk => hk`.
-/
theorem finite_setOf_algebraMap_mem {D : Set 𝔸[K]} (hD : IsCompact D) :
    {k : K | algebraMap K 𝔸[K] k ∈ D}.Finite := by
  have := discreteTopology_principalSubgroup K
  have hc : IsCompact ((Subtype.val : AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' D) :=
    (isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K := fun k => ⟨algebraMap K 𝔸[K] k, k, rfl⟩
  have hf : Function.Injective f := fun a b h =>
    AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h)
  exact (hc.finite_of_discrete.preimage hf.injOn).subset fun k hk => hk

/- English proof (translation)
Use `(Set.Finite.pi (t := fun i => {k : K | algebraMap K 𝔸[K] k ∈ (fun y => y i) '' D}) fun i => finite_setOf_algebraMap_mem (hD.image (continuous_apply i))).subset ?_` and prove the remaining obligations. Introduce `x hx i _`. Conclude with `⟨ratVec x, hx, rfl⟩`.
-/
theorem finite_setOf_ratVec_mem {D : Set (Fin n → 𝔸[K])} (hD : IsCompact D) :
    {x : Fin n → K | ratVec x ∈ D}.Finite := by
  refine (Set.Finite.pi (t := fun i => {k : K | algebraMap K 𝔸[K] k ∈ (fun y => y i) '' D})
    fun i => finite_setOf_algebraMap_mem (hD.image (continuous_apply i))).subset ?_
  intro x hx i _
  exact ⟨ratVec x, hx, rfl⟩

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).2 ((Valued.toNormedField.norm_le_one_iff).1 hx)`.
-/
theorem mem_of_norm_le_one (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K} (hx : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers K :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).2
    ((Valued.toNormedField.norm_le_one_iff).1 hx)

def mkIdele (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) : IdeleGroup K :=
  (prodRestrictedEquiv K).symm
    (MulEquiv.piUnits.symm fun w => Units.mk0 (a w) (ha w),
     ⟨fun v => Units.mk0 (b v) (hb v), by
        filter_upwards [hb1] with v hv
        rw [SetLike.mem_coe, Submonoid.mem_units_iff]
        refine ⟨mem_of_norm_le_one v hv.le, mem_of_norm_le_one v ?_⟩
        rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hv, inv_one]⟩)

/- English proof (translation)
Rewrite using `[← prodRestrictedEquiv_apply_fst, mkIdele, ContinuousMulEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem mkIdele_fst (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (w : InfinitePlace K) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).1 w = a w := by
  rw [← prodRestrictedEquiv_apply_fst, mkIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Rewrite using `[← prodRestrictedEquiv_apply_snd, mkIdele, ContinuousMulEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem mkIdele_snd (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (v : HeightOneSpectrum (𝓞 K)) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).2 v = b v := by
  rw [← prodRestrictedEquiv_apply_snd, mkIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Establish `: Nonempty (Fin n)`. Assume the negation of the conclusion as `h`. Conclude with `hz (funext fun i => (h ⟨i⟩).elim)`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty`. Conclude with `⟨i, le_antisymm (norm_le_pi_norm z i) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j))⟩`.
-/
theorem exists_norm_eq_norm {E : Type*} [SeminormedAddCommGroup E] {z : Fin n → E} (hz : z ≠ 0) :
    ∃ i, ‖z i‖ = ‖z‖ := by
  have : Nonempty (Fin n) := by
    by_contra h
    exact hz (funext fun i => (h ⟨i⟩).elim)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty
  exact ⟨i, le_antisymm (norm_le_pi_norm z i)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j))⟩

/- English proof (translation)
Use `choose i hi using fun w => exists_norm_eq_norm (hinf w)`. Use `choose j hj using fun v => exists_norm_eq_norm (hfin v)`. Establish `ha : ∀ w, infComp w y (i w) ≠ 0` using `fun w h => hinf w (norm_eq_zero.1 (by rw [← hi w, h, norm_zero]))`. Establish `hb0 : ∀ v, finComp v y (j v) ≠ 0` using `fun v h => hfin v (norm_eq_zero.1 (by rw [← hj v, h, norm_zero]))`. Use `set b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v => if ‖finComp v y‖ = 1 then 1 else finComp v y (j v) with hbdef`.

Establish `hb : ∀ v, b v ≠ 0` using `fun v => by`. Rewrite using `[hbdef]`. Simplify using `only`. Use `split_ifs`. Conclude with `one_ne_zero`.

Conclude with `hb0 v`. Establish `hbn : ∀ v, ‖b v‖ = ‖finComp v y‖` using `fun v => by`. Rewrite using `[hbdef]`. Simplify using `only`. Use `split_ifs with h`.

Rewrite using `[h, norm_one]`. Conclude with `hj v`. Establish `hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1` using `by filter_upwards [hy] with v hv`. Rewrite using `[hbn, hv]`. Conclude with `⟨mkIdele (fun w => infComp w y (i w)) b ha hb hb1, fun w => by rw [mkIdele_fst, hi], fun v => by rw [mkIdele_snd, hbn]⟩`.
-/
theorem exists_idele_norm_eq {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hinf : ∀ w, infComp w y ≠ 0) (hfin : ∀ v, finComp v y ≠ 0) :
    ∃ s : IdeleGroup K, (∀ w, ‖(s : 𝔸[K]).1 w‖ = ‖infComp w y‖) ∧
      ∀ v, ‖(s : 𝔸[K]).2 v‖ = ‖finComp v y‖ := by
  classical
  choose i hi using fun w => exists_norm_eq_norm (hinf w)
  choose j hj using fun v => exists_norm_eq_norm (hfin v)
  have ha : ∀ w, infComp w y (i w) ≠ 0 := fun w h => hinf w (norm_eq_zero.1 (by rw [← hi w, h, norm_zero]))
  have hb0 : ∀ v, finComp v y (j v) ≠ 0 := fun v h =>
    hfin v (norm_eq_zero.1 (by rw [← hj v, h, norm_zero]))
  set b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K :=
    fun v => if ‖finComp v y‖ = 1 then 1 else finComp v y (j v) with hbdef
  have hb : ∀ v, b v ≠ 0 := fun v => by
    rw [hbdef]; dsimp only; split_ifs
    · exact one_ne_zero
    · exact hb0 v
  have hbn : ∀ v, ‖b v‖ = ‖finComp v y‖ := fun v => by
    rw [hbdef]; dsimp only; split_ifs with h
    · rw [h, norm_one]
    · exact hj v
  have hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1 := by
    filter_upwards [hy] with v hv
    rw [hbn, hv]
  exact ⟨mkIdele (fun w => infComp w y (i w)) b ha hb hb1,
    fun w => by rw [mkIdele_fst, hi], fun v => by rw [mkIdele_snd, hbn]⟩

/- English proof (translation)
Introduce `h0`. Apply `h.ne'` to reduce the goal to its premises. Establish `h1 : euclidNorm (infComp w y) = 0` using `by rw [h0]; simp [euclidNorm]`. Rewrite using `[adelicNorm, Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h1, zero_pow InfinitePlace.mult_ne_zero]), zero_mul]`.
-/
theorem infComp_ne_zero_of_adelicNorm_pos {y : Fin n → 𝔸[K]} (h : 0 < adelicNorm y)
    (w : InfinitePlace K) : infComp w y ≠ 0 := by
  intro h0
  apply h.ne'
  have h1 : euclidNorm (infComp w y) = 0 := by rw [h0]; simp [euclidNorm]
  rw [adelicNorm, Finset.prod_eq_zero (Finset.mem_univ w)
    (by rw [h1, zero_pow InfinitePlace.mult_ne_zero]), zero_mul]

/- English proof (translation)
Introduce `h0`. Apply `h.ne'` to reduce the goal to its premises. Establish `hv : v ∈ hy.finite_mulSupport.toFinset`. Rewrite using `[Set.Finite.mem_toFinset, Function.mem_mulSupport, h0, norm_zero]`. Conclude with `zero_ne_one`.

Rewrite using `[adelicNorm, finprod_eq_prod_of_mulSupport_subset _ (s := hy.finite_mulSupport.toFinset) (fun u hu => hy.finite_mulSupport.mem_toFinset.2 hu), Finset.prod_eq_zero hv (by rw [h0, norm_zero]), mul_zero]`.
-/
theorem finComp_ne_zero_of_adelicNorm_pos {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (h : 0 < adelicNorm y) (v : HeightOneSpectrum (𝓞 K)) : finComp v y ≠ 0 := by
  intro h0
  apply h.ne'
  have hv : v ∈ hy.finite_mulSupport.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, h0, norm_zero]
    exact zero_ne_one
  rw [adelicNorm, finprod_eq_prod_of_mulSupport_subset _
    (s := hy.finite_mulSupport.toFinset) (fun u hu => hy.finite_mulSupport.mem_toFinset.2 hu),
    Finset.prod_eq_zero hv (by rw [h0, norm_zero]), mul_zero]

/- English proof (translation)
Establish `ha : ‖a‖ * ‖a'‖ = 1` using `by rw [← norm_mul, h, norm_one]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_mul_le_one_of_mul_eq_one {E : Type*} [NormedField E] {a a' b : E} (h : a * a' = 1)
    (hb : ‖b‖ ≤ ‖a‖) : ‖a' * b‖ ≤ 1 := by
  have ha : ‖a‖ * ‖a'‖ = 1 := by rw [← norm_mul, h, norm_one]
  rw [norm_mul]
  calc ‖a'‖ * ‖b‖ ≤ ‖a'‖ * ‖a‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 1 := by rw [mul_comm, ha]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨∅, Set.finite_empty, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩`. Take `⟨ε, hε, hεC⟩` from `exists_pos_le_height hC`. Use `set P₀ : ℝ := ∏ w : InfinitePlace K, √(n : ℝ) ^ w.mult with hP₀`. Establish `hn' : (0 : ℝ) < n` using `Nat.cast_pos.2 hn`.

Establish `hP₀pos : 0 < P₀` using `Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 hn') _`. Take `⟨S, hS, hSmem⟩` from `exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) (div_pos hε hP₀pos) B`. Use `set U₁ : Set 𝔸[K] := {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) with hU₁def`. Establish `hU₁ : IsCompact U₁`. Use `IsCompact.prod ?_ (isCompact_integralFiniteAdeles K)` and prove the remaining obligations.

Establish `: {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} = Set.pi univ (fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) 1)`. Use extensionality with `a`. Conclude with `⟨fun h w _ => mem_closedBall_zero_iff.2 (h w), fun h w => mem_closedBall_zero_iff.1 (h w (mem_univ w))⟩`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun w => isCompact_closedBall 0 1`.

Use `set U : Set (Fin n → 𝔸[K]) := Set.pi univ fun _ => U₁ with hUdef`. Establish `hU : IsCompact U` using `isCompact_univ_pi fun _ => hU₁`. Use `set D := (fun p : IdeleGroup K × (Fin n → 𝔸[K]) => ((p.1 : 𝔸[K]) • p.2)) '' (S ×ˢ U) with hDdef`. Establish `hD : IsCompact D` using `(hS.prod hU).image ((Units.continuous_val.comp continuous_fst).smul continuous_snd)`. Use `set D' := (fun p : (Fin n → 𝔸[K]) × AdelicGLn.AdelicGL K n => p.1 ᵥ* ((p.2⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (D ×ˢ C) with hD'def`.

Establish `hD' : IsCompact D'` using `(hD.prod hC).image (Continuous.matrix_vecMul continuous_fst ((Units.continuous_val (M := Matrix (Fin n) (Fin n) 𝔸[K])).comp (continuous_inv.comp continuous_snd)))`. Use `⟨{x | ratVec x ∈ D'}, finite_setOf_ratVec_mem hD', fun g hg x hx hxB => ?_⟩` and prove the remaining obligations. Use `set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy`. Establish `hyc : HasFiniteContent y` using `hasFiniteContent_height g hx`. Establish `hypos : 0 < adelicNorm y` using `lt_of_lt_of_le hε (hεC g hg x hx)`.

Take `⟨s, hsw, hsv⟩` from `exists_idele_norm_eq hyc (infComp_ne_zero_of_adelicNorm_pos hypos) (finComp_ne_zero_of_adelicNorm_pos hyc hypos)`. Establish `hmod : (ideleModule K s : ℝ) = (∏ w, ‖infComp w y‖ ^ w.mult) * ∏ᶠ v, ‖finComp v y‖`. Rewrite using `[ideleModule_eq]`. Repeatedly rewrite using `[hsw, hsv]`. Establish `hfp : 0 ≤ ∏ᶠ v, ‖finComp v y‖` using `finprod_nonneg fun _ => norm_nonneg _`.

Establish `hup : (ideleModule K s : ℝ) ≤ B`. Use `le_trans ?_ hxB` and prove the remaining obligations. Rewrite using `[hmod, height, ← hy, adelicNorm]`. Conclude with `mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_euclidNorm_pi _) _) hfp`. Establish `hlow : ε / P₀ ≤ (ideleModule K s : ℝ)`.

Rewrite using `[div_le_iff₀ hP₀pos]`. Use `(hεC g hg x hx).trans ?_` and prove the remaining obligations. Rewrite using `[hmod, height, ← hy, adelicNorm, mul_comm _ P₀, ← mul_assoc, hP₀, ← Finset.prod_mul_distrib]`. Use `mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => ?_) hfp` and prove the remaining obligations. Rewrite using `[← mul_pow]`.

Conclude with `pow_le_pow_left₀ (euclidNorm_nonneg _) (euclidNorm_le_sqrt_mul _) _`. Take `⟨c, hc⟩` from `hSmem s hlow hup`. Use `⟨(c : K), c.ne_zero, ?_⟩` and prove the remaining obligations. Establish `hsinv : ((s : 𝔸[K]) * ((s⁻¹ : IdeleGroup K) : 𝔸[K])) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hz : ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y ∈ U`. Introduce `i _`. Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Use `show ‖(((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).1 w‖ ≤ 1`. Rewrite using `[adele_fst_mul_apply]`.

Conclude with `norm_mul_le_one_of_mul_eq_one (infinite_mul_inv s w) ((norm_le_pi_norm (infComp w y) i).trans (hsw w).ge)`. Use `show (((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).2 ∈ integralFiniteAdeles (𝓞 K) K`. Rewrite using `[mem_integralFiniteAdeles]`. Introduce `v`. Rewrite using `[adele_snd_mul_apply]`.

Conclude with `mem_of_norm_le_one v (norm_mul_le_one_of_mul_eq_one (finite_mul_inv s v) ((norm_le_pi_norm (finComp v y) i).trans (hsv v).ge))`. Use `⟨(algebraMap K 𝔸[K] (c : K) • y, g), ⟨⟨(diagonal K c * s, ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y), ⟨hc, hz⟩, ?_⟩, hg⟩, ?_⟩` and prove the remaining obligations. Use `show ((diagonal K c * s : IdeleGroup K) : 𝔸[K]) • (((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y) = algebraMap K 𝔸[K] (c : K) • y`. Rewrite using `[smul_smul, Units.val_mul, mul_assoc, hsinv, mul_one, coe_diagonal]`. Use `show (algebraMap K 𝔸[K] (c : K) • y) ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = ratVec ((c : K) • x)`.

Rewrite using `[smul_vecMul, hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, ratVec_smul]`.
-/
theorem exists_finite_smul_mem_of_height_le {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C)
    (B : ℝ) : ∃ F : Set (Fin n → K), F.Finite ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 →
      height g x ≤ B → ∃ c : K, c ≠ 0 ∧ c • x ∈ F := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, Set.finite_empty, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩
  obtain ⟨ε, hε, hεC⟩ := exists_pos_le_height hC
  set P₀ : ℝ := ∏ w : InfinitePlace K, √(n : ℝ) ^ w.mult with hP₀
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hP₀pos : 0 < P₀ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 hn') _
  obtain ⟨S, hS, hSmem⟩ :=
    exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) (div_pos hε hP₀pos) B
  set U₁ : Set 𝔸[K] := {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} ×ˢ
    (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) with hU₁def
  have hU₁ : IsCompact U₁ := by
    refine IsCompact.prod ?_ (isCompact_integralFiniteAdeles K)
    have : {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} =
        Set.pi univ (fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) 1) := by
      ext a
      exact ⟨fun h w _ => mem_closedBall_zero_iff.2 (h w),
        fun h w => mem_closedBall_zero_iff.1 (h w (mem_univ w))⟩
    rw [this]
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  set U : Set (Fin n → 𝔸[K]) := Set.pi univ fun _ => U₁ with hUdef
  have hU : IsCompact U := isCompact_univ_pi fun _ => hU₁
  set D := (fun p : IdeleGroup K × (Fin n → 𝔸[K]) => ((p.1 : 𝔸[K]) • p.2)) '' (S ×ˢ U) with hDdef
  have hD : IsCompact D := (hS.prod hU).image
    ((Units.continuous_val.comp continuous_fst).smul continuous_snd)
  set D' := (fun p : (Fin n → 𝔸[K]) × AdelicGLn.AdelicGL K n =>
    p.1 ᵥ* ((p.2⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (D ×ˢ C) with hD'def
  have hD' : IsCompact D' := (hD.prod hC).image (Continuous.matrix_vecMul continuous_fst
    ((Units.continuous_val (M := Matrix (Fin n) (Fin n) 𝔸[K])).comp (continuous_inv.comp continuous_snd)))
  refine ⟨{x | ratVec x ∈ D'}, finite_setOf_ratVec_mem hD', fun g hg x hx hxB => ?_⟩
  set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  have hyc : HasFiniteContent y := hasFiniteContent_height g hx
  have hypos : 0 < adelicNorm y := lt_of_lt_of_le hε (hεC g hg x hx)
  obtain ⟨s, hsw, hsv⟩ := exists_idele_norm_eq hyc (infComp_ne_zero_of_adelicNorm_pos hypos)
    (finComp_ne_zero_of_adelicNorm_pos hyc hypos)
  have hmod : (ideleModule K s : ℝ) =
      (∏ w, ‖infComp w y‖ ^ w.mult) * ∏ᶠ v, ‖finComp v y‖ := by
    rw [ideleModule_eq]
    simp_rw [hsw, hsv]
  have hfp : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  have hup : (ideleModule K s : ℝ) ≤ B := by
    refine le_trans ?_ hxB
    rw [hmod, height, ← hy, adelicNorm]
    exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_euclidNorm_pi _) _) hfp
  have hlow : ε / P₀ ≤ (ideleModule K s : ℝ) := by
    rw [div_le_iff₀ hP₀pos]
    refine (hεC g hg x hx).trans ?_
    rw [hmod, height, ← hy, adelicNorm, mul_comm _ P₀, ← mul_assoc, hP₀, ← Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => ?_) hfp
    rw [← mul_pow]
    exact pow_le_pow_left₀ (euclidNorm_nonneg _) (euclidNorm_le_sqrt_mul _) _
  obtain ⟨c, hc⟩ := hSmem s hlow hup
  refine ⟨(c : K), c.ne_zero, ?_⟩
  have hsinv : ((s : 𝔸[K]) * ((s⁻¹ : IdeleGroup K) : 𝔸[K])) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y ∈ U := by
    intro i _
    refine ⟨fun w => ?_, ?_⟩
    · show ‖(((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).1 w‖ ≤ 1
      rw [adele_fst_mul_apply]
      exact norm_mul_le_one_of_mul_eq_one (infinite_mul_inv s w)
        ((norm_le_pi_norm (infComp w y) i).trans (hsw w).ge)
    · show (((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).2 ∈ integralFiniteAdeles (𝓞 K) K
      rw [mem_integralFiniteAdeles]
      intro v
      rw [adele_snd_mul_apply]
      exact mem_of_norm_le_one v (norm_mul_le_one_of_mul_eq_one (finite_mul_inv s v)
        ((norm_le_pi_norm (finComp v y) i).trans (hsv v).ge))
  refine ⟨(algebraMap K 𝔸[K] (c : K) • y, g), ⟨⟨(diagonal K c * s, ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y),
    ⟨hc, hz⟩, ?_⟩, hg⟩, ?_⟩
  · show ((diagonal K c * s : IdeleGroup K) : 𝔸[K]) • (((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y) =
      algebraMap K 𝔸[K] (c : K) • y
    rw [smul_smul, Units.val_mul, mul_assoc, hsinv, mul_one, coe_diagonal]
  · show (algebraMap K 𝔸[K] (c : K) • y) ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratVec ((c : K) • x)
    rw [smul_vecMul, hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      ratVec_smul]

/- English proof (translation)
Use `set e : Fin n → K := Pi.single ⟨0, hn⟩ 1 with he`. Establish `he0 : e ≠ 0` using `fun h => by`. Use `congrFun h ⟨0, hn⟩` as an intermediate fact. Simplify using `[he] at this`. Take `⟨F, hF, hFmem⟩` from `exists_finite_smul_mem_of_height_le (isCompact_singleton (x := g)) (height g e)`.

Use `set T := {x ∈ F | x ≠ 0} with hT`. Take `⟨c₀, hc₀, hc₀F⟩` from `hFmem g rfl e he0 le_rfl`. Establish `hTne : T.Nonempty` using `⟨c₀ • e, hc₀F, smul_ne_zero hc₀ he0⟩`. Take `⟨x₀, hx₀T, hx₀⟩` from `Set.exists_min_image T (height g) (hF.subset fun x hx => hx.1) hTne`. Use `⟨x₀, hx₀T.2, fun y hy => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hyB : height g y ≤ height g e`. Take `⟨c, hc, hcF⟩` from `hFmem g rfl y hy hyB`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_height_min (hn : 0 < n) (g : AdelicGLn.AdelicGL K n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ y : Fin n → K, y ≠ 0 → height g x ≤ height g y := by
  classical
  set e : Fin n → K := Pi.single ⟨0, hn⟩ 1 with he
  have he0 : e ≠ 0 := fun h => by
    have := congrFun h ⟨0, hn⟩
    simp [he] at this
  obtain ⟨F, hF, hFmem⟩ := exists_finite_smul_mem_of_height_le (isCompact_singleton (x := g))
    (height g e)
  set T := {x ∈ F | x ≠ 0} with hT
  obtain ⟨c₀, hc₀, hc₀F⟩ := hFmem g rfl e he0 le_rfl
  have hTne : T.Nonempty := ⟨c₀ • e, hc₀F, smul_ne_zero hc₀ he0⟩
  obtain ⟨x₀, hx₀T, hx₀⟩ := Set.exists_min_image T (height g) (hF.subset fun x hx => hx.1) hTne
  refine ⟨x₀, hx₀T.2, fun y hy => ?_⟩
  by_cases hyB : height g y ≤ height g e
  · obtain ⟨c, hc, hcF⟩ := hFmem g rfl y hy hyB
    calc height g x₀ ≤ height g (c • y) := hx₀ _ ⟨hcF, smul_ne_zero hc hy⟩
      _ = height g y := height_smul g hy hc
  · calc height g x₀ ≤ height g (c₀ • e) := hx₀ _ ⟨hc₀F, smul_ne_zero hc₀ he0⟩
      _ = height g e := height_smul g he0 hc₀
      _ ≤ height g y := (not_le.1 hyB).le

end Reduction

end

end GroundTheory.Automorphic
