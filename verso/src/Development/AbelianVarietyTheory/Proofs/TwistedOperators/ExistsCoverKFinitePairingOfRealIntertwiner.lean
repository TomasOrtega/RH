import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine.CoverFromLocal

section General

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/- English proof (translation)
Establish `h1` using `hw 1 (fun _ => X) (fun _ => hX)`. Establish `hc : ContDiff ℝ 1 (fun t : ℝ => (fun _ : Fin 1 => t))` using `contDiff_pi.2 (fun _ => contDiff_id)`. Apply the tactic sequence `have h2 := (h1.of_le (by first | simp | exact_mod_cast le_top)).comp hc`. Establish `h3` using `((h2.differentiable one_ne_zero) 0).hasDerivAt`. Establish `e : ((fun t : Fin 1 → ℝ => σ (List.ofFn fun i => NormedSpace.exp (t i • X)).prod w) ∘ fun t : ℝ => (fun _ : Fin 1 => t)) = fun t : ℝ => σ (NormedSpace.exp (t • X)) w`.

Use function extensionality and compare the values at `t`. Simplify using `[List.ofFn_succ]`. Rewrite `h3` using `[e]`. Conclude with `h3`.
-/
private theorem hasDerivAt_exp_smul_of_smoothVec {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H}
    (hw : SmoothVec Lie σ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have hc : ContDiff ℝ 1 (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 (fun _ => contDiff_id)
  have h2 := (h1.of_le (by first | simp | exact_mod_cast le_top)).comp hc
  have h3 := ((h2.differentiable one_ne_zero) 0).hasDerivAt
  have e : ((fun t : Fin 1 → ℝ => σ (List.ofFn fun i => NormedSpace.exp (t i • X)).prod w) ∘
      fun t : ℝ => (fun _ : Fin 1 => t)) = fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    funext t
    simp [List.ofFn_succ]
  rw [e] at h3
  exact h3

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[barMat]`.
-/
private theorem barMat_map_conj_eq_reindex {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) :
    (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by
  ext i j
  simp [barMat]

/- English proof (translation)
Rewrite using `[Matrix.trace, Matrix.trace, map_sum]`. Both sides reduce to the same expression.
-/
private theorem trace_map_conj' {p q : ℕ} (Z : Mat p q) :
    (Z.map (starRingEnd ℂ)).trace = (starRingEnd ℂ) Z.trace := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

/- English proof (translation)
Establish `hU : U y - Complex.I • U x = U (y + Complex.I • x)`. Rewrite using `[map_add, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]`. Establish `hv : x - Complex.I • y = (-Complex.I) • (y + Complex.I • x)`. Rewrite using `[smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hU, U.norm_map, hv, norm_smul, norm_neg, Complex.norm_I, one_mul]`.
-/
private theorem norm_apply_sub_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y - Complex.I • U x‖ = ‖x - Complex.I • y‖ := by
  have hU : U y - Complex.I • U x = U (y + Complex.I • x) := by
    rw [map_add, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hv : x - Complex.I • y = (-Complex.I) • (y + Complex.I • x) := by
    rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  rw [hU, U.norm_map, hv, norm_smul, norm_neg, Complex.norm_I, one_mul]

/- English proof (translation)
Establish `hU : U y + Complex.I • U x = U (y - Complex.I • x)`. Rewrite using `[map_sub, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]`. Establish `hv : x + Complex.I • y = Complex.I • (y - Complex.I • x)`. Rewrite using `[smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hU, U.norm_map, hv, norm_smul, Complex.norm_I, one_mul]`.
-/
private theorem norm_apply_add_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y + Complex.I • U x‖ = ‖x + Complex.I • y‖ := by
  have hU : U y + Complex.I • U x = U (y - Complex.I • x) := by
    rw [map_sub, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hv : x + Complex.I • y = Complex.I • (y - Complex.I • x) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
    abel
  rw [hU, U.norm_map, hv, norm_smul, Complex.norm_I, one_mul]

/- English proof (translation)
Establish `h1 : ‖U y + U x‖ = ‖x + y‖` using `by rw [← map_add, U.norm_map, add_comm]`. Establish `h2 : ‖U y - U x‖ = ‖x - y‖` using `by rw [← map_sub, U.norm_map, norm_sub_rev]`. Rewrite using `[inner_eq_sum_norm_sq_div_four (U y) (U x), inner_eq_sum_norm_sq_div_four x y]`. Simplify using `only [RCLike.I_to_complex]`. Rewrite using `[h1, h2, norm_apply_sub_I_smul_apply, norm_apply_add_I_smul_apply]`.
-/
theorem inner_conjIso (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U y, U x⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : ‖U y + U x‖ = ‖x + y‖ := by rw [← map_add, U.norm_map, add_comm]
  have h2 : ‖U y - U x‖ = ‖x - y‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  rw [inner_eq_sum_norm_sq_div_four (U y) (U x), inner_eq_sum_norm_sq_div_four x y]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, norm_apply_sub_I_smul_apply, norm_apply_add_I_smul_apply]

def realOf (U : E ≃ₗᵢ⋆[ℂ] F) : E →L[ℝ] F where
  toFun := U
  map_add' := map_add U
  map_smul' r x := by
    rw [← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
    rfl
  cont := U.continuous

end General

/- English proof (translation)
Introduce `D V W S S' M M' τ p q r s T₁ T₂ R₁ R₂ e e' m m' aS aT U U' κ A hm hm' h₁ h₂ hκ hA`. Establish `hinj₁ : Function.Injective R₁.ι` using `R₁.ι_inj`. Establish `hsm : ∀ x : R₂.HK.V, U'.symm (R₂.ι x) ∈ M'.sm τ` using `fun x => Submodule.subset_span (h₂.smooth _ (by`. Rewrite using `[LinearIsometryEquiv.apply_symm_apply]`. Conclude with `Set.mem_range_self _))`.

Set `w : R₂.HK.V → M'.sm τ` to `fun x => ⟨U'.symm (R₂.ι x), hsm x⟩`. Establish `hUw : ∀ x, U' (w x : M'.H τ) = R₂.ι x` using `fun x => U'.apply_symm_apply _`. Establish `hw_add : ∀ x x', w (x + x') = w x + w x'`. Introduce `x x'`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show U'.symm (R₂.ι (x + x')) = U'.symm (R₂.ι x) + U'.symm (R₂.ι x')`. Rewrite using `[map_add, map_add]`. Establish `hw_smul : ∀ (c : ℂ) x, w (c • x) = (starRingEnd ℂ) c • w x`. Introduce `c x`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show U'.symm (R₂.ι (c • x)) = (starRingEnd ℂ) c • U'.symm (R₂.ι x)`. Rewrite using `[map_smul, LinearIsometryEquiv.map_smulₛₗ]`. Establish `hex : ∀ (P : LPol W.rank V.rank) (y : M'.sm τ), ∃ v, R₁.ι v = U (A P y)` using `fun P y => (h₁.kfin _).1 (hA.kS P y)`. Use `choose g hg using hex`. Set `Bf : Pol p q r s → R₂.HK.V → R₁.HK.V` to `fun P x => g (κ.symm P) (w x)`.

Establish `key : ∀ P x, R₁.ι (Bf P x) = U (A (κ.symm P) (w x))` using `fun P x => hg _ _`. Set `Bi : Pol p q r s → (R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V)` to `fun P => { toFun := Bf P map_add' := by`. Introduce `x x'`. Apply `hinj₁` to reduce the goal to its premises. Use `show R₁.ι (Bf P (x + x')) = R₁.ι (Bf P x + Bf P x')`.

Rewrite using `[map_add, key, key, key, hw_add, map_add, map_add]`. Use the proof step `map_smul' := by`. Introduce `c x`. Apply `hinj₁` to reduce the goal to its premises. Use `show R₁.ι (Bf P (c • x)) = R₁.ι ((starRingEnd ℂ) c • Bf P x)`.

Rewrite using `[map_smul, key, key, hw_smul, map_smul, map_smul] }`. Set `B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V` to `{ toFun := Bi map_add' := by`. Introduce `P P'`. Use extensionality with `x`. Apply `hinj₁` to reduce the goal to its premises.

Use `show R₁.ι (Bf (P + P') x) = R₁.ι (Bf P x + Bf P' x)`. Rewrite using `[map_add, key, key, key, map_add, map_add, LinearMap.add_apply, map_add]`. Use the proof step `map_smul' := by`. Introduce `c P`. Use extensionality with `x`.

Apply `hinj₁` to reduce the goal to its premises. Use `show R₁.ι (Bf (c • P) x) = R₁.ι (c • Bf P x)`. Rewrite using `[map_smul, key, key, map_smul, map_smul, LinearMap.smul_apply, map_smul] }`. Establish `hB : ∀ P x, R₁.ι (B P x) = U (A (κ.symm P) (w x))` using `key`. Use `⟨B, { adj := ?_, src := ?_, tgt := ?_ }, ?_⟩` and prove the remaining obligations.

Introduce `P x`. Take `⟨b0, hb0K, hb0⟩` from `hA.kT (κ.symm P) (U.symm (R₁.ι x))`. Take `⟨b, hb⟩` from `(h₂.kfin b0).1 hb0K`. Use `⟨b, fun y => ?_⟩` and prove the remaining obligations. Establish `e2 : R₁.ι x = U (U.symm (R₁.ι x))` using `(U.apply_symm_apply _).symm`.

Rewrite using `[hB, hb, ← hUw y, inner_conjIso, ← hb0]`. Use `conv_lhs => rw [e2]`. Conclude with `LinearIsometryEquiv.inner_map_map U _ _`. Introduce `Z hZ P y`. Apply `hinj₁` to reduce the goal to its premises.

Establish `hloc : κ.symm (fockAct1 p q r s Z P) = locS (M.ε τ) (M'.ε τ) (Matrix.reindex e e Z) (κ.symm P)`. Rewrite using `[LinearEquiv.symm_apply_eq, hκ.1, LinearEquiv.apply_symm_apply]`. Establish `hX : toFrame M τ (barMat e Z) ∈ lieAt V τ`. Rewrite using `[← h₁.lie]`. Conclude with `⟨Z, hZ, rfl⟩`.

Establish `hsx : SmoothVec (lieAt V τ) (M.rep τ) (A (κ.symm P) (w y))` using `h₁.smooth _ ⟨_, hB P y⟩`. Establish `hd1` using `hasDerivAt_exp_smul_of_smoothVec hsx hX`. Establish `hdr : dRep (M.rep τ) (toFrame M τ (barMat e Z)) (A (κ.symm P) (w y)) = A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * toFrame M τ (barMat e Z) * (M.fr τ)⁻¹).map (starRingEnd ℂ)) (κ.symm P) - ((aT : ℂ) * (toFrame M τ (barMat e Z)).trace) • κ.symm P) (w y)`. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `u`.

Establish `hd2` using `hA.src _ hX (κ.symm P) (w y) u`. Establish `hd3` using `(hasDerivAt_const (0 : ℝ) u).inner ℂ hd1`. Simplify using `only [inner_zero_left, add_zero] at hd3`. Conclude with `hd3.unique hd2`. Establish `htr : (toFrame M τ (barMat e Z)).trace = -Z.trace`.

Rewrite using `[trace_toFrame, barMat, trace_reindex', trace_map_conj', trace_conj hZ]`. Rewrite `hdr` using `[fr_toFrame, barMat_map_conj_eq_reindex, htr]`. Establish `hder` using `h₁.der Z hZ (B P y) _ (hB P y).symm`. Rewrite `hder` using `[hdr]`. Establish `hc : ((m : ℂ) / 2 * Z.trace) = (aT : ℂ) * Z.trace`.

Establish `h2 : (m : ℂ) = 2 * (aT : ℂ)` using `by exact_mod_cast hm`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_add, hc, hB] at hder`. Rewrite using `[hB, hloc]`.

Rewrite `hder` using `[mul_neg, neg_smul, sub_neg_eq_add]`. Conclude with `add_right_cancel hder`. Introduce `Z hZ P y`. Apply `hinj₁` to reduce the goal to its premises. Rewrite using `[map_add, map_zero, hB, hB]`.

Establish `hp : plainMat e' Z = Matrix.reindex e' e' Z` using `rfl`. Establish `hloc : κ.symm (fockAct2 p q r s Z P) = locT (M.ε τ) (M'.ε τ) (plainMat e' Z) (κ.symm P)`. Rewrite using `[hp, LinearEquiv.symm_apply_eq, hκ.2, LinearEquiv.apply_symm_apply]`. Establish `hY : toFrame M' τ (plainMat e' Z) ∈ lieAt W τ`. Rewrite using `[← h₂.lie]`.

Conclude with `⟨Z, hZ, rfl⟩`. Establish `hsw : SmoothVec (lieAt W τ) (M'.rep τ) (w y : M'.H τ)` using `h₂.smooth _ (by rw [hUw]; exact Set.mem_range_self _)`. Establish `hd` using `hasDerivAt_exp_smul_of_smoothVec hsw hY`. Establish `hder` using `h₂.der Z hZ y (w y) (hUw y)`. Establish `hsm' : dRep (M'.rep τ) (toFrame M' τ (plainMat e' Z)) (w y : M'.H τ) ∈ M'.sm τ` using `Submodule.subset_span (h₂.smooth _ (by rw [hder]; exact Set.mem_range_self _))`.

Establish `ht` using `hA.tgt _ hY (κ.symm P) (w y) ⟨_, hsm'⟩ hd`. Establish `htr : (toFrame M' τ (plainMat e' Z)).trace = Z.trace`. Rewrite using `[trace_toFrame, plainMat, trace_reindex']`. Rewrite `ht` using `[htr, fr_toFrame]`. Establish `hcs : ((m' : ℂ) / 2 * Z.trace) + (starRingEnd ℂ) ((aS : ℂ) * Z.trace) = 0`.

Establish `h2 : (m' : ℂ) = 2 * (aS : ℂ)` using `by exact_mod_cast hm'`. Rewrite using `[map_mul, trace_conj hZ, map_ratCast, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw2 : w (R₂.HK.act Z y) = ⟨_, hsm'⟩ + ((aS : ℂ) * Z.trace) • w y`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `U'.injective` to reduce the goal to its premises. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, map_add, LinearIsometryEquiv.map_smulₛₗ, hder, hUw, hUw, map_add, map_smul, add_assoc, ← add_smul, hcs, zero_smul, add_zero]`. Rewrite using `[hloc, hw2, map_add, map_smul, ← map_add, ← map_zero U]`. Use `congr 1`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht`.

Rewrite using `[← ht]`. Normalize the expressions using the abelian group laws. Introduce `P x y hy`. Establish `hwy : w x = y`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show U'.symm (R₂.ι x) = (y : M'.H τ)`. Rewrite using `[← hy, LinearIsometryEquiv.symm_apply_apply]`. Rewrite using `[hB, LinearEquiv.symm_apply_apply, hwy]`.
-/
theorem exists_coverW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → LocW M M' τ aS aT A → ∃ B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V, CoverW R₁ R₂ B ∧ ∀ (P : LPol W.rank V.rank) (x : R₂.HK.V) (y : M'.sm τ), U' (y : M'.H τ) = R₂.ι x → R₁.ι (B (κ P) x) = U (A P y) := by
  intro D V W S S' M M' τ p q r s T₁ T₂ R₁ R₂ e e' m m' aS aT U U' κ A hm hm' h₁ h₂ hκ hA
  have hinj₁ : Function.Injective R₁.ι := R₁.ι_inj

  have hsm : ∀ x : R₂.HK.V, U'.symm (R₂.ι x) ∈ M'.sm τ := fun x =>
    Submodule.subset_span (h₂.smooth _ (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact Set.mem_range_self _))
  let w : R₂.HK.V → M'.sm τ := fun x => ⟨U'.symm (R₂.ι x), hsm x⟩
  have hUw : ∀ x, U' (w x : M'.H τ) = R₂.ι x := fun x => U'.apply_symm_apply _
  have hw_add : ∀ x x', w (x + x') = w x + w x' := by
    intro x x'
    apply Subtype.ext
    show U'.symm (R₂.ι (x + x')) = U'.symm (R₂.ι x) + U'.symm (R₂.ι x')
    rw [map_add, map_add]
  have hw_smul : ∀ (c : ℂ) x, w (c • x) = (starRingEnd ℂ) c • w x := by
    intro c x
    apply Subtype.ext
    show U'.symm (R₂.ι (c • x)) = (starRingEnd ℂ) c • U'.symm (R₂.ι x)
    rw [map_smul, LinearIsometryEquiv.map_smulₛₗ]

  have hex : ∀ (P : LPol W.rank V.rank) (y : M'.sm τ), ∃ v, R₁.ι v = U (A P y) :=
    fun P y => (h₁.kfin _).1 (hA.kS P y)
  choose g hg using hex
  let Bf : Pol p q r s → R₂.HK.V → R₁.HK.V := fun P x => g (κ.symm P) (w x)
  have key : ∀ P x, R₁.ι (Bf P x) = U (A (κ.symm P) (w x)) := fun P x => hg _ _
  let Bi : Pol p q r s → (R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) := fun P =>
    { toFun := Bf P
      map_add' := by
        intro x x'
        apply hinj₁
        show R₁.ι (Bf P (x + x')) = R₁.ι (Bf P x + Bf P x')
        rw [map_add, key, key, key, hw_add, map_add, map_add]
      map_smul' := by
        intro c x
        apply hinj₁
        show R₁.ι (Bf P (c • x)) = R₁.ι ((starRingEnd ℂ) c • Bf P x)
        rw [map_smul, key, key, hw_smul, map_smul, map_smul] }
  let B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V :=
    { toFun := Bi
      map_add' := by
        intro P P'
        ext x
        apply hinj₁
        show R₁.ι (Bf (P + P') x) = R₁.ι (Bf P x + Bf P' x)
        rw [map_add, key, key, key, map_add, map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro c P
        ext x
        apply hinj₁
        show R₁.ι (Bf (c • P) x) = R₁.ι (c • Bf P x)
        rw [map_smul, key, key, map_smul, map_smul, LinearMap.smul_apply, map_smul] }
  have hB : ∀ P x, R₁.ι (B P x) = U (A (κ.symm P) (w x)) := key
  refine ⟨B, { adj := ?_, src := ?_, tgt := ?_ }, ?_⟩
  ·
    intro P x
    obtain ⟨b0, hb0K, hb0⟩ := hA.kT (κ.symm P) (U.symm (R₁.ι x))
    obtain ⟨b, hb⟩ := (h₂.kfin b0).1 hb0K
    refine ⟨b, fun y => ?_⟩
    have e2 : R₁.ι x = U (U.symm (R₁.ι x)) := (U.apply_symm_apply _).symm
    rw [hB, hb, ← hUw y, inner_conjIso, ← hb0]
    conv_lhs => rw [e2]
    exact LinearIsometryEquiv.inner_map_map U _ _
  ·
    intro Z hZ P y
    apply hinj₁
    have hloc : κ.symm (fockAct1 p q r s Z P) =
        locS (M.ε τ) (M'.ε τ) (Matrix.reindex e e Z) (κ.symm P) := by
      rw [LinearEquiv.symm_apply_eq, hκ.1, LinearEquiv.apply_symm_apply]
    have hX : toFrame M τ (barMat e Z) ∈ lieAt V τ := by
      rw [← h₁.lie]; exact ⟨Z, hZ, rfl⟩
    have hsx : SmoothVec (lieAt V τ) (M.rep τ) (A (κ.symm P) (w y)) :=
      h₁.smooth _ ⟨_, hB P y⟩
    have hd1 := hasDerivAt_exp_smul_of_smoothVec hsx hX
    have hdr : dRep (M.rep τ) (toFrame M τ (barMat e Z)) (A (κ.symm P) (w y)) =
        A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * toFrame M τ (barMat e Z) * (M.fr τ)⁻¹).map (starRingEnd ℂ))
          (κ.symm P) - ((aT : ℂ) * (toFrame M τ (barMat e Z)).trace) • κ.symm P) (w y) := by
      apply ext_inner_left ℂ
      intro u
      have hd2 := hA.src _ hX (κ.symm P) (w y) u
      have hd3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ hd1
      simp only [inner_zero_left, add_zero] at hd3
      exact hd3.unique hd2
    have htr : (toFrame M τ (barMat e Z)).trace = -Z.trace := by
      rw [trace_toFrame, barMat, trace_reindex', trace_map_conj', trace_conj hZ]
    rw [fr_toFrame, barMat_map_conj_eq_reindex, htr] at hdr
    have hder := h₁.der Z hZ (B P y) _ (hB P y).symm
    rw [hdr] at hder
    have hc : ((m : ℂ) / 2 * Z.trace) = (aT : ℂ) * Z.trace := by
      have h2 : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
      rw [h2]; ring
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_add, hc, hB] at hder
    rw [hB, hloc]
    rw [mul_neg, neg_smul, sub_neg_eq_add] at hder
    exact add_right_cancel hder
  ·
    intro Z hZ P y
    apply hinj₁
    rw [map_add, map_zero, hB, hB]
    have hp : plainMat e' Z = Matrix.reindex e' e' Z := rfl
    have hloc : κ.symm (fockAct2 p q r s Z P) =
        locT (M.ε τ) (M'.ε τ) (plainMat e' Z) (κ.symm P) := by
      rw [hp, LinearEquiv.symm_apply_eq, hκ.2, LinearEquiv.apply_symm_apply]
    have hY : toFrame M' τ (plainMat e' Z) ∈ lieAt W τ := by
      rw [← h₂.lie]; exact ⟨Z, hZ, rfl⟩
    have hsw : SmoothVec (lieAt W τ) (M'.rep τ) (w y : M'.H τ) :=
      h₂.smooth _ (by rw [hUw]; exact Set.mem_range_self _)
    have hd := hasDerivAt_exp_smul_of_smoothVec hsw hY
    have hder := h₂.der Z hZ y (w y) (hUw y)
    have hsm' : dRep (M'.rep τ) (toFrame M' τ (plainMat e' Z)) (w y : M'.H τ) ∈ M'.sm τ :=
      Submodule.subset_span (h₂.smooth _ (by rw [hder]; exact Set.mem_range_self _))
    have ht := hA.tgt _ hY (κ.symm P) (w y) ⟨_, hsm'⟩ hd
    have htr : (toFrame M' τ (plainMat e' Z)).trace = Z.trace := by
      rw [trace_toFrame, plainMat, trace_reindex']
    rw [htr, fr_toFrame] at ht
    have hcs : ((m' : ℂ) / 2 * Z.trace) + (starRingEnd ℂ) ((aS : ℂ) * Z.trace) = 0 := by
      have h2 : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
      rw [map_mul, trace_conj hZ, map_ratCast, h2]; ring
    have hw2 : w (R₂.HK.act Z y) = ⟨_, hsm'⟩ + ((aS : ℂ) * Z.trace) • w y := by
      apply Subtype.ext
      apply U'.injective
      rw [Submodule.coe_add, Submodule.coe_smul, map_add, LinearIsometryEquiv.map_smulₛₗ, hder, hUw, hUw,
        map_add, map_smul, add_assoc, ← add_smul, hcs, zero_smul, add_zero]
    rw [hloc, hw2, map_add, map_smul, ← map_add, ← map_zero U]
    congr 1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
    rw [← ht]
    abel
  ·
    intro P x y hy
    have hwy : w x = y := by
      apply Subtype.ext
      show U'.symm (R₂.ι x) = (y : M'.H τ)
      rw [← hy, LinearIsometryEquiv.symm_apply_apply]
    rw [hB, LinearEquiv.symm_apply_apply, hwy]

end GlobalTheory.Chain.RealLine.CoverFromLocal

end
