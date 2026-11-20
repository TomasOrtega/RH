import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne

noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace GlobalTheory.TypeSum.DerFamCont

/- English proof (translation)
Establish `: CompleteSpace E` using `FiniteDimensional.complete ℝ E`. Set `: NormedAlgebra ℚ E` to `NormedAlgebra.restrictScalars ℚ ℝ E`. Set `S : Submodule ℝ E` to `LinearMap.ker (σ + LinearMap.id)`. Establish `hS : ∀ X, X ∈ S ↔ σ X = -X` using `fun X => by simp [S, add_eq_zero_iff_eq_neg]`. Set `b` to `Module.finBasis ℝ S`.

Set `e : Fin (Module.finrank ℝ S) → E` to `fun i => b i`. Establish `hli : LinearIndependent ℝ e` using `b.linearIndependent.map' S.subtype S.ker_subtype`. Establish `he : ∀ i, σ (e i) = -e i` using `fun i => (hS _).1 (b i).2`. Establish `hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)` using `fun X hX => by`. Establish `h` using `congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)`.

Rewrite `h` using `[map_sum]`. Simplify using `only [map_smul, Submodule.subtype_apply] at h`. Rewrite using `[← h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a)` using `fun a => by`.

Establish `hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih => rw [pow_succ, hm, ih, pow_succ']`. Establish `h2` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional`.

Use `h2.unique ?_` and prove the remaining obligations. Use `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `[hp]`. Use `set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ`.

Establish `hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1` using `fun t => GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hu`. Rewrite using `[hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]`. Use the proof step `simp)`. Set `T : (Fin _ → ℝ) →L[ℝ] E` to `∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)`.

Establish `hT : ∀ t, T t = ∑ i, t i • e i` using `fun t => by simp [T]`. Take `⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0` from `GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i => ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i)) (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i …`. Take `⟨P, hP1, hP2, hP3⟩` from `GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp`. Establish `hΦ : HasStrictFDerivAt (fun t => P (Θ t)) ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) : (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0`. Use `(P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_` and prove the remaining obligations.

Use `ext1 t`. Simplify using `[hT, hP1]`. Establish `hP0 : P 1 = 0` using `hP2 _ h1`. Establish `hΦ0 : P (Θ 0) = 0` using `by rw [h0, hP0]`. Establish `p1` using `hΦ.localInverse_tendsto`.

Establish `p3` using `hΦ.eventually_right_inverse`. Simplify using `only [hΦ0] at p1 p3`. Use `set Ψ := hΦ.localInverse _ _ _`. Establish `hσc : Continuous σ` using `σ.continuous_of_finiteDimensional`. Establish `hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2`.

Establish `: ContinuousAt (fun m => ‖1 - σ m‖) 1` using `by fun_prop`. Conclude with `this.eventually_le_const (by simp [h1])`. Establish `hPt : Tendsto P (𝓝 1) (𝓝 0)` using `hP0 ▸ P.continuous.tendsto 1`. Establish `ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1)`. Use `hD.continuousAt.tendsto.comp p1` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this.comp hPt`. Use `⟨_, e, fun a => Ψ (P a), he, p1.comp hPt, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha`. Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E`.

Conclude with `GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2`.
-/
theorem exists_chart {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E)
    (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1) :
    ∃ (N : ℕ) (Y : Fin N → E) (Ψ : E → Fin N → ℝ), (∀ i, σ (Y i) = -Y i) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : E), σ a * a = 1 → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let S : Submodule ℝ E := LinearMap.ker (σ + LinearMap.id)
  have hS : ∀ X, X ∈ S ↔ σ X = -X := fun X => by simp [S, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ S
  let e : Fin (Module.finrank ℝ S) → E := fun i => b i
  have hli : LinearIndependent ℝ e := b.linearIndependent.map' S.subtype S.ker_subtype
  have he : ∀ i, σ (e i) = -e i := fun i => (hS _).1 (b i).2
  have hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e) := fun X hX => by
    have h := congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext n
    simp [hp]
  set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin _ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i =>
      ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i))
        (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i) 0).hasStrictFDerivAt)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin _ => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp
  have hΦ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) :
        (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΦ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΦ.localInverse_tendsto
  have p3 := hΦ.eventually_right_inverse
  simp only [hΦ0] at p1 p3
  set Ψ := hΦ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1) := by
    have := hD.continuousAt.tendsto.comp p1
    rw [h0] at this
    exact this.comp hPt
  refine ⟨_, e, fun a => Ψ (P a), he, p1.comp hPt, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Use `letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Mx n) := Matrix.linftyOpNormedAlgebra`. Establish `h2` using `Jm_mul_self ε`. Establish `hH : (Jm ε)ᴴ = Jm ε`. Establish `h : (Jm ε)ᴴ * Jm ε = 1` using `(maximal_compact_facts n ε).2.2.1.1.1`.

Rewrite using `[← Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv h2]`. Use `set J := Jm ε with hJdef`. Set `s : Mx n →ₗ[ℝ] Mx n` to `{ toFun := fun x => J * xᴴ * J map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul] map_smul' := fun c x => by simp [conjTranspose_smul] }`. Establish `hs : ∀ x, s x = J * xᴴ * J` using `fun _ => rfl`. Establish `hJJ : ∀ x : Mx n, J * (J * x) = x` using `fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]`.

Take `⟨N, Y, Ψ, hY, hΨ, hE⟩` from `exists_chart s (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2, Matrix.mul_one]) (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])`. Use `⟨N, Y, Ψ, fun i => ?_, hΨ, hE.mono fun g q hg => q ?_⟩` and prove the remaining obligations. Use `congrArg (J * ·) (hY i)` as an intermediate fact. Simplify using `only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this`. Use `show (Y i)ᴴ * J + J * Y i = 0`.

Rewrite using `[this, neg_add_cancel]`. Establish `hg' : gᴴ * J * g = J` using `hg`. Rewrite using `[hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]`.
-/
theorem exists_chart_UJ (ε : Fin n → Bool) :
    ∃ (N : ℕ) (Y : Fin N → Mx n) (Ψ : Mx n → Fin N → ℝ), (∀ i, Y i ∈ lieSet ε) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : Mx n), a ∈ UJset ε → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h2 := Jm_mul_self ε
  have hH : (Jm ε)ᴴ = Jm ε := by
    have h : (Jm ε)ᴴ * Jm ε = 1 := (maximal_compact_facts n ε).2.2.1.1.1
    rw [← Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv h2]
  set J := Jm ε with hJdef
  let s : Mx n →ₗ[ℝ] Mx n :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Mx n, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  refine ⟨N, Y, Ψ, fun i => ?_, hΨ, hE.mono fun g q hg => q ?_⟩
  · have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    show (Y i)ᴴ * J + J * Y i = 0
    rw [this, neg_add_cancel]
  · have hg' : gᴴ * J * g = J := hg
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]

/- English proof (translation)
Take `⟨B, hB⟩` from `(isCompact_closedBall (0 : ℝ) 1).bddAbove_image (f := fun u : ℝ => 1 + hs (NormedSpace.exp (u • X))) (continuous_const.add (continuous_hs.comp (continuous_exp_smul X))).continuousOn`. Use `⟨B, fun a ha s hs1 => ?_⟩` and prove the remaining obligations. Use `(convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t : ℝ => f (a * NormedSpace.exp (t • X))) (f' := fun t => f' (a * NormedSpace.exp (t • X))) (C := |C| * ((1 + hs a) * B) ^ N) (x := 0) (y := s) (fun t _ => ?_) (fun t ht => ?_) (Metric.mem_closedB …` as an intermediate fact. Simplify using `using this`. Establish `k` using `hd _ (mul_mem_UJ ha (exp_mem_UJ hX t))`.

Establish `k2` using `HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)`. Use `(k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).hasDerivWithinAt` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]`. Use `(hb _ (mul_mem_UJ ha (exp_mem_UJ hX t))).trans ?_` and prove the remaining obligations.

Establish `h0` using `hs_nonneg (a * NormedSpace.exp (t • X))`. Establish `h1` using `hs_nonneg a`. Use `mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)` and prove the remaining obligations. Conclude with `(one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB ⟨t, ht, rfl⟩) (by positivity))`.
-/
theorem exists_step_bound {f f' : Mx n → ℂ} {X : Mx n} (hX : X ∈ lieSet ε) {C : ℝ} {N : ℕ}
    (hd : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0)
    (hb : ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∃ B : ℝ, ∀ a ∈ UJset ε, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖f (a * NormedSpace.exp (s • X)) - f a‖ ≤ |C| * ((1 + hs a) * B) ^ N * ‖s‖ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image
    (f := fun u : ℝ => 1 + hs (NormedSpace.exp (u • X)))
    (continuous_const.add (continuous_hs.comp (continuous_exp_smul X))).continuousOn
  refine ⟨B, fun a ha s hs1 => ?_⟩
  have := (convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => f (a * NormedSpace.exp (t • X))) (f' := fun t => f' (a * NormedSpace.exp (t • X)))
    (C := |C| * ((1 + hs a) * B) ^ N) (x := 0) (y := s) (fun t _ => ?_) (fun t ht => ?_)
    (Metric.mem_closedBall_self zero_le_one) hs1
  · simpa using this
  · have k := hd _ (mul_mem_UJ ha (exp_mem_UJ hX t))
    have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).hasDerivWithinAt
    beta_reduce
    rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]
  · refine (hb _ (mul_mem_UJ ha (exp_mem_UJ hX t))).trans ?_
    have h0 := hs_nonneg (a * NormedSpace.exp (t • X))
    have h1 := hs_nonneg a
    refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)
    exact (one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB ⟨t, ht, rfl⟩) (by positivity))

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro Y t a _ _ _ _ h`. Simplify using `using h`. Consider the case `succ d ih`.

Introduce `Y t a hY ht ha hag hc`. Simplify using `only [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]`. Use `ih (fun i => Y i.succ) (fun p i => t p i.succ) (fun p => a p * NormedSpace.exp (t p 0 • Y 0)) (fun i => hY _) (fun i => ht _) (fun p => mul_mem_UJ (ha p) (exp_mem_UJ (hY 0) _)) ?_ ?_` and prove the remaining obligations. Use `hag.mul (((continuous_exp_smul (Y 0)).tendsto 0).comp (ht 0))` as an intermediate fact. Simplify using `using this`.

Take `⟨f', C, h1, h2⟩` from `hf _ (hY 0)`. Take `⟨B, hB⟩` from `exists_step_bound (hY 0) h1 h2`. Establish `h3 : Tendsto (fun p => f (a p * NormedSpace.exp (t p 0 • Y 0)) - f (a p)) L (𝓝 0)`. Use `squeeze_zero_norm' (a := fun p => |C| * ((1 + hs (a p)) * B) ^ N * ‖t p 0‖) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [(ht 0).eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with p hp`.

Conclude with `hB _ (ha p) _ hp`. Use `(((((continuous_hs.tendsto g₀).comp hag).const_add 1).mul_const B).pow N |>.const_mul |C|).mul (ht 0).norm` as an intermediate fact. Simplify using `using this`. Simplify using `using h3.add hc`.
-/
theorem tendsto_prod {f : Mx n → ℂ} {α : Type} {L : Filter α} {g₀ : Mx n} {c : ℂ} {N : ℕ}
    (hf : ∀ X ∈ lieSet ε, ∃ (f' : Mx n → ℂ) (C : ℝ),
      (∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0) ∧
      ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∀ (d : ℕ) (Y : Fin d → Mx n) (t : α → Fin d → ℝ) (a : α → Mx n), (∀ i, Y i ∈ lieSet ε) →
      (∀ i, Tendsto (fun p => t p i) L (𝓝 0)) → (∀ p, a p ∈ UJset ε) → Tendsto a L (𝓝 g₀) →
      Tendsto (fun p => f (a p)) L (𝓝 c) →
      Tendsto (fun p => f (a p * (List.ofFn fun i => NormedSpace.exp (t p i • Y i)).prod)) L (𝓝 c) := by
  intro d
  induction d with
  | zero => intro Y t a _ _ _ _ h; simpa using h
  | succ d ih =>
    intro Y t a hY ht ha hag hc
    simp only [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]
    refine ih (fun i => Y i.succ) (fun p i => t p i.succ) (fun p => a p * NormedSpace.exp (t p 0 • Y 0))
      (fun i => hY _) (fun i => ht _) (fun p => mul_mem_UJ (ha p) (exp_mem_UJ (hY 0) _)) ?_ ?_
    · have := hag.mul (((continuous_exp_smul (Y 0)).tendsto 0).comp (ht 0))
      simpa using this
    · obtain ⟨f', C, h1, h2⟩ := hf _ (hY 0)
      obtain ⟨B, hB⟩ := exists_step_bound (hY 0) h1 h2
      have h3 : Tendsto (fun p => f (a p * NormedSpace.exp (t p 0 • Y 0)) - f (a p)) L (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun p => |C| * ((1 + hs (a p)) * B) ^ N * ‖t p 0‖) ?_ ?_
        · filter_upwards [(ht 0).eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with p hp
          exact hB _ (ha p) _ hp
        · have := (((((continuous_hs.tendsto g₀).comp hag).const_add 1).mul_const B).pow N |>.const_mul |C|).mul
            (ht 0).norm
          simpa using this
      simpa using h3.add hc

/- English proof (translation)
Introduce `n ε N F hF hG l hl g₀ hg₀`. Take `⟨d, Y, Ψ, hY, hΨ, hE⟩` from `exists_chart_UJ ε`. Establish `ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝[UJset ε] g₀) (𝓝 1)`. Use `((continuous_const (y := g₀⁻¹)).matrix_mul continuous_id).tendsto g₀` as an intermediate fact. Rewrite `this` using `[id, inv_mul_UJ hg₀]`.

Conclude with `this.mono_left nhdsWithin_le_nhds`. Establish `key` using `tendsto_prod (ε := ε) (f := F l) (L := 𝓝[UJset ε] g₀) (g₀ := g₀) (c := F l g₀) (N := N) (fun X hX => by`. Take `⟨C, hC⟩` from `hG (X :: l) (List.forall_mem_cons.2 ⟨hX, hl⟩)`. Conclude with `⟨F (X :: l), C, hF l hl X hX, hC⟩)`. Use `d Y (fun g => Ψ (g₀⁻¹ * g)) (fun _ => g₀) hY (fun i => tendsto_pi_nhds.1 (hΨ.comp ht) i) (fun _ => hg₀)`.

Use `tendsto_const_nhds tendsto_const_nhds`. Use `key.congr' ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually hE, self_mem_nhdsWithin] with g q hg`. Rewrite using `[q (mul_mem_UJ (inv_mem_UJ hg₀) hg), ← Matrix.mul_assoc, mul_inv_UJ hg₀, Matrix.one_mul]`.
-/
theorem continuousOn_of_isDerFam : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ),
    IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  intro n ε N F hF hG l hl g₀ hg₀
  obtain ⟨d, Y, Ψ, hY, hΨ, hE⟩ := exists_chart_UJ ε
  have ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝[UJset ε] g₀) (𝓝 1) := by
    have := ((continuous_const (y := g₀⁻¹)).matrix_mul continuous_id).tendsto g₀
    rw [id, inv_mul_UJ hg₀] at this
    exact this.mono_left nhdsWithin_le_nhds
  have key := tendsto_prod (ε := ε) (f := F l) (L := 𝓝[UJset ε] g₀) (g₀ := g₀) (c := F l g₀) (N := N)
    (fun X hX => by
      obtain ⟨C, hC⟩ := hG (X :: l) (List.forall_mem_cons.2 ⟨hX, hl⟩)
      exact ⟨F (X :: l), C, hF l hl X hX, hC⟩)
    d Y (fun g => Ψ (g₀⁻¹ * g)) (fun _ => g₀) hY (fun i => tendsto_pi_nhds.1 (hΨ.comp ht) i) (fun _ => hg₀)
    tendsto_const_nhds tendsto_const_nhds
  refine key.congr' ?_
  filter_upwards [ht.eventually hE, self_mem_nhdsWithin] with g q hg
  rw [q (mul_mem_UJ (inv_mem_UJ hg₀) hg), ← Matrix.mul_assoc, mul_inv_UJ hg₀, Matrix.one_mul]

end GlobalTheory.TypeSum.DerFamCont

end
