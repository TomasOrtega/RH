import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialKFiniteBothMembers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.CoverContr

/- English proof (translation)
Set `L : H →ₗᵢ[ℂ] H` to `⟨A.toLinearMap, hA⟩`. Conclude with `L.inner_map_map x y`.
-/
theorem inner_map_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (x y : H) : inner ℂ (A x) (A y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨A.toLinearMap, hA⟩
  exact L.inner_map_map x y

/- English proof (translation)
Establish `h1 : U g (U g⁻¹ w) = w`. Establish `h` using `congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)`. Simplify using `using h.symm`. Use `conv_lhs => rw [← h1]`. Conclude with `inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)`.
-/
private theorem inner_unitary_apply_eq_inner_inv {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* E →L[ℂ] E) (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) (v w : E) :
    inner ℂ (U g v) w = inner ℂ v (U g⁻¹ w) := by
  have h1 : U g (U g⁻¹ w) = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)
    simpa using h.symm
  conv_lhs => rw [← h1]
  exact inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)

/- English proof (translation)
Introduce `p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq`. Establish `hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖`. Introduce `x y`. Establish `h` using `hTm x x y y`. Simplify using `only [inner_self_eq_norm_sq_to_K] at h`.

Establish `h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2`. Rewrite using `[mul_pow]`. Conclude with `h` after adjusting the coercions. Conclude with `(pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2`. Establish `hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖` using `fun y => ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by`.

Rewrite using `[ContinuousLinearMap.flip_apply, hnorm, mul_comm]`. Establish `hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H), R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) = ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v)`. Introduce `g y v`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]`. Establish `e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y)`. Rewrite using `[hEq]`. Simplify using the standard rewrite rules. Establish `e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v` using `rfl`.

Establish `e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y)`. Establish `: ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹` using `by simp`. Use `show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _`. Rewrite using `[this, map_inv]`. Rewrite using `[e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]`.

Establish `htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H), ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v = ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v)`. Introduce `h y v`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `x`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]`.

Establish `e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y)`. Rewrite using `[hEq]`. Simplify using the standard rewrite rules. Establish `e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v` using `rfl`. Establish `e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y)`.

Establish `: ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹` using `by simp`. Use `show F.Om (F.emb (1, h)) (Tm x y) = _`. Rewrite using `[this, map_inv]`. Rewrite using `[e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]`. Set `B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H` to `{ toFun := fun P => { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) map_add' := fun y y' => by simp map_smul' := fun c y => by`.

Rewrite using `[map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }`. Use the proof step `map_add' := fun P P' => by ext y; simp`. Use the proof step `map_smul' := fun c P => by ext y; simp }`. Establish `hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)` using `fun _ _ => rfl`. Use `⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `P`. Use `⟨‖F.ι P‖, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hB]`. Combine the equalities or inequalities in the displayed calculation. Introduce `P y`.

Rewrite using `[R₁.ι_range, hB]`. Unfold `KFin`. Establish `hk` using `(GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1`. Unfold `KFin at hk`. Use `haveI := hk`.

Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.map (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩`. Introduce `y hy`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI := R₁.nontriv`. Take `⟨x, hx⟩` from `exists_ne (0 : R₁.U.H)`. Establish `hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0`.

Use `Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨P, rfl⟩`. Establish `h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0` using `by rw [← hB]; exact hcon P`. Use `ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)` as an intermediate fact. Rewrite `this` using `[h0, inner_zero_left, ContinuousLinearMap.flip_apply]`.

Conclude with `this.symm`. Establish `h1 : Tm x y = 0` using `inner_self_eq_zero.1 (congrFun hz (Tm x y))`. Establish `h2` using `hnorm x y`. Rewrite `h2` using `[h1, norm_zero]`. Conclude with `mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm`.

Introduce `Z hZ P y`. Establish `hd` using `(GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.1 Z hZ P`. Establish `hc` using `((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Establish `e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) = (ContinuousLinearMap.adjoint (Tm.flip y)) ∘ (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P))`. Use function extensionality and compare the values at `t`.

Rewrite using `[hB, Function.comp_apply, hsrc]`. Rewrite using `[e, hB]`. Conclude with `hc`. Introduce `Z hZ P y`. Establish `hone : T₂.expt ((0 : ℝ) • Z) = 1`.

Establish `h` using `T₂.expt_add Z hZ 0 0`. Rewrite `h` using `[add_zero]`. Establish `h'` using `congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h`. Simplify `h'.symm` using `[mul_assoc]`. Establish `hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z)`.

Introduce `t`. Establish `h` using `T₂.expt_add Z hZ (-t) t`. Rewrite `h` using `[neg_add_cancel, hone]`. Conclude with `(eq_inv_of_mul_eq_one_left h.symm).symm`. Establish `hd` using `(GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.2 Z hZ P`.

Establish `hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ))` using `by rw [neg_zero]; exact hd`. Establish `hn` using `hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))`. Establish `hc` using `((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn`. Establish `e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) = (ContinuousLinearMap.adjoint (Tm.flip y)) ∘ ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t)`. Use function extensionality and compare the values at `t`.

Rewrite using `[hB, htgt, hinv]`. Both sides reduce to the same expression. Establish `hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ) ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) = -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P))`. Rewrite using `[neg_one_smul, map_neg]`. Both sides reduce to the same expression.

Rewrite using `[e, hB, ← hval]`. Conclude with `hc`.
-/
theorem exists_isCoverIt : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  intro p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq

  have hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hTm x x y y
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2
  have hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖ := fun y =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by
      rw [ContinuousLinearMap.flip_apply, hnorm, mul_comm]

  have hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H),
      R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v) := by
    intro g y v
    apply ext_inner_right ℂ
    intro x
    rw [inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.flip_apply]
    have e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v := rfl
    have e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y) := by
      have : ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹ := by simp
      show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]

  have htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H),
      ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v) := by
    intro h y v
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    have e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v := rfl
    have e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y) := by
      have : ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹ := by simp
      show F.Om (F.emb (1, h)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]
  let B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H :=
    { toFun := fun P =>
        { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)
          map_add' := fun y y' => by simp
          map_smul' := fun c y => by
            rw [map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }
      map_add' := fun P P' => by ext y; simp
      map_smul' := fun c P => by ext y; simp }
  have hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) := fun _ _ => rfl
  refine ⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P
    refine ⟨‖F.ι P‖, fun y => ?_⟩
    rw [hB]
    calc ‖ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)‖
        ≤ ‖ContinuousLinearMap.adjoint (Tm.flip y)‖ * ‖F.ι P‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tm.flip y‖ * ‖F.ι P‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖y‖ * ‖F.ι P‖ := by gcongr; exact hflip y
      _ = ‖F.ι P‖ * ‖y‖ := mul_comm _ _
  · intro P y
    rw [R₁.ι_range, hB]
    unfold KFin
    have hk := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1
    unfold KFin at hk
    haveI := hk
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap
      (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩
  · intro y hy
    by_contra hcon
    push_neg at hcon
    haveI := R₁.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R₁.U.H)
    have hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0 := by
      refine Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_
      rintro _ ⟨P, rfl⟩
      have h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0 := by rw [← hB]; exact hcon P
      have := ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)
      rw [h0, inner_zero_left, ContinuousLinearMap.flip_apply] at this
      exact this.symm
    have h1 : Tm x y = 0 := inner_self_eq_zero.1 (congrFun hz (Tm x y))
    have h2 := hnorm x y
    rw [h1, norm_zero] at h2
    exact mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm
  · intro Z hZ P y
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.1 Z hZ P
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P)) := by
      funext t
      rw [hB, Function.comp_apply, hsrc]
    rw [e, hB]
    exact hc
  · intro Z hZ P y
    have hone : T₂.expt ((0 : ℝ) • Z) = 1 := by
      have h := T₂.expt_add Z hZ 0 0
      rw [add_zero] at h
      have h' := congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h
      simpa [mul_assoc] using h'.symm
    have hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z) := by
      intro t
      have h := T₂.expt_add Z hZ (-t) t
      rw [neg_add_cancel, hone] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.2 Z hZ P
    have hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P))
        (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ)) := by rw [neg_zero]; exact hd
    have hn := hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn
    have e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t) := by
      funext t
      rw [hB, htgt, hinv]
      rfl
    have hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ)
        ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) =
        -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P)) := by
      rw [neg_one_smul, map_neg]
      rfl
    rw [e, hB, ← hval]
    exact hc

end GlobalTheory.Chain.CoverContr

end
