import Mathlib

open MeasureTheory WeakDual

namespace UpperTheory.Reformulated.B.CharactersSeparatePoints

/- English proof (translation)
Apply the tactic sequence `have h1 : gelfandTransform ℂ A (U g * T) ≠ gelfandTransform ℂ A T := fun h => hg ((gelfandTransform_isometry A).injective h)`. Take `⟨φ, hφ⟩` from `DFunLike.ne_iff.1 h1`. Express the relevant statement in the definitionally equal form `φ (U g * T) ≠ φ T at hφ`. Establish `hT0 : φ T ≠ 0`. Introduce `h0`.

Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_mul, h0, mul_zero]`. Establish `hn : ∀ h, ‖φ (U h)‖ = 1`. Introduce `h`. Establish `: star (φ (U h)) * φ (U h) = 1`.

Rewrite using `[← map_star, ← map_mul, hU, ← map_mul, inv_mul_cancel, map_one, map_one]`. Establish `h2` using `congrArg norm this`. Rewrite `h2` using `[norm_mul, norm_star, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (φ (U h))]`. Establish `hc : Continuous fun h => φ (U h)`.

Establish `: (fun h => φ (U h)) = fun h => φ (U h * T) / φ T`. Use function extensionality and compare the values at `h`. Rewrite using `[map_mul, mul_div_cancel_right₀ _ hT0]`. Rewrite using `[this]`. Conclude with `((map_continuous φ).comp hT).div_const _`.

Use `⟨{ toFun := fun h => ⟨φ (U h), mem_sphere_zero_iff_norm.2 (hn h)⟩ map_one' := Circle.ext (by simp) map_mul' := fun a b => Circle.ext (by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (U (a * b)) = φ (U a) * φ (U b)`. Rewrite using `[map_mul, map_mul])`. Use `continuous_toFun := hc.subtype_mk _ }, ?_⟩`. Introduce `h`.

Apply `hφ` to reduce the goal to its premises. Establish `: φ (U g) = 1` using `congrArg (fun z : Circle => (z : ℂ)) h`. Rewrite using `[map_mul, this, one_mul]`.
-/
private theorem comm_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CommCStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A) (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have h1 : gelfandTransform ℂ A (U g * T) ≠ gelfandTransform ℂ A T :=
    fun h => hg ((gelfandTransform_isometry A).injective h)
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.1 h1
  change φ (U g * T) ≠ φ T at hφ
  have hT0 : φ T ≠ 0 := by
    intro h0
    apply hφ
    rw [map_mul, h0, mul_zero]
  have hn : ∀ h, ‖φ (U h)‖ = 1 := by
    intro h
    have : star (φ (U h)) * φ (U h) = 1 := by
      rw [← map_star, ← map_mul, hU, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := congrArg norm this
    rw [norm_mul, norm_star, norm_one] at h2
    nlinarith [norm_nonneg (φ (U h))]
  have hc : Continuous fun h => φ (U h) := by
    have : (fun h => φ (U h)) = fun h => φ (U h * T) / φ T := by
      funext h
      rw [map_mul, mul_div_cancel_right₀ _ hT0]
    rw [this]
    exact ((map_continuous φ).comp hT).div_const _
  refine ⟨{ toFun := fun h => ⟨φ (U h), mem_sphere_zero_iff_norm.2 (hn h)⟩
            map_one' := Circle.ext (by simp)
            map_mul' := fun a b => Circle.ext (by
              change φ (U (a * b)) = φ (U a) * φ (U b)
              rw [map_mul, map_mul])
            continuous_toFun := hc.subtype_mk _ }, ?_⟩
  intro h
  apply hφ
  have : φ (U g) = 1 := congrArg (fun z : Circle => (z : ℂ)) h
  rw [map_mul, this, one_mul]

/- English proof (translation)
Set `S' : StarSubalgebra ℂ A` to `StarSubalgebra.centralizer ℂ (Set.range U)`. Establish `mem' : ∀ B, B ∈ S' ↔ ∀ h, U h * B = B * U h`. Introduce `B`. Rewrite using `[StarSubalgebra.mem_centralizer_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `H h`. Conclude with `(H _ ⟨h, rfl⟩).1`. Introduce and unpack `H _ ⟨h, rfl⟩`. Conclude with `⟨H h, by rw [hU]; exact H _⟩`. Set `S : StarSubalgebra ℂ A` to `StarSubalgebra.centralizer ℂ (S' : Set A)`.

Establish `mem : ∀ B, B ∈ S ↔ ∀ D ∈ S', D * B = B * D`. Introduce `B`. Rewrite using `[StarSubalgebra.mem_centralizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `H D hD`.

Conclude with `(H _ hD).1`. Introduce `H D hD`. Conclude with `⟨H D hD, H _ (star_mem hD)⟩`. Establish `hUS' : ∀ h, U h ∈ S'` using `fun h => (mem' _).2 fun k => by`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Establish `hUS : ∀ h, U h ∈ S` using `fun h => (mem _).2 fun D hD => ((mem' D).1 hD h).symm`. Establish `hTS : T ∈ S` using `(mem _).2 fun D hD => hB D ((mem' D).1 hD)`. Establish `hSS : ∀ B ∈ S, B ∈ S'` using `fun B hB => (mem' _).2 fun h => (mem _).1 hB _ (hUS' h)`. Establish `hcl : IsClosed (S : Set A)`. Establish `: (S : Set A) = ⋂ D ∈ S', {B | D * B = B * D}`.

Use extensionality with `B`. Simplify using `only [SetLike.mem_coe, mem, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun D _ => isClosed_eq (by fun_prop) (by fun_prop)`. Set `_ : CommCStarAlgebra S` to `{ (inferInstance : CStarAlgebra S) with mul_comm := fun a b => Subtype.ext ((mem _).1 b.2 _ (hSS _ a.2)) }`.

Use `comm_case (A := S) (U.codRestrict S hUS) (fun h => Subtype.ext (hU h)) ⟨T, hTS⟩ (hT.subtype_mk _) (fun h => hg (congrArg Subtype.val h))` and prove the remaining obligations.
-/
private theorem alg_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A)
    (hB : ∀ B : A, (∀ h, U h * B = B * U h) → B * T = T * B)
    (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  let S' : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (Set.range U)
  have mem' : ∀ B, B ∈ S' ↔ ∀ h, U h * B = B * U h := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H h
      exact (H _ ⟨h, rfl⟩).1
    · rintro H _ ⟨h, rfl⟩
      exact ⟨H h, by rw [hU]; exact H _⟩
  let S : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (S' : Set A)
  have mem : ∀ B, B ∈ S ↔ ∀ D ∈ S', D * B = B * D := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H D hD
      exact (H _ hD).1
    · intro H D hD
      exact ⟨H D hD, H _ (star_mem hD)⟩
  have hUS' : ∀ h, U h ∈ S' := fun h => (mem' _).2 fun k => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hUS : ∀ h, U h ∈ S := fun h => (mem _).2 fun D hD => ((mem' D).1 hD h).symm
  have hTS : T ∈ S := (mem _).2 fun D hD => hB D ((mem' D).1 hD)
  have hSS : ∀ B ∈ S, B ∈ S' := fun B hB => (mem' _).2 fun h => (mem _).1 hB _ (hUS' h)
  have hcl : IsClosed (S : Set A) := by
    have : (S : Set A) = ⋂ D ∈ S', {B | D * B = B * D} := by
      ext B
      simp only [SetLike.mem_coe, mem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun D _ => isClosed_eq (by fun_prop) (by fun_prop)
  let _ : CommCStarAlgebra S :=
    { (inferInstance : CStarAlgebra S) with
      mul_comm := fun a b => Subtype.ext ((mem _).1 b.2 _ (hSS _ a.2)) }
  refine comm_case (A := S) (U.codRestrict S hUS) (fun h => Subtype.ext (hU h)) ⟨T, hTS⟩
    (hT.subtype_mk _) (fun h => hg (congrArg Subtype.val h))

/- English proof (translation)
Establish `happ : ∀ a b x, U a (U b x) = U (a * b) x`. Introduce `a b x`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hstar : ∀ h, star (U h) = U h⁻¹`.

Introduce `h`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`. Use `(LinearIsometry.mk (U h).toLinearMap (hn h)).inner_map_map (U h⁻¹ x) y` as an intermediate fact. Rewrite using `[← this]`.

Express the relevant statement in the definitionally equal form `inner ℂ (U h (U h⁻¹ x)) (U h y) = _`. Rewrite using `[happ, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hint : ∀ (f : C(C, ℂ)) (x : H), Integrable (fun h => f h • U h x) μ` using `fun f x => (f.continuous.smul (hc x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Set `T₀ : C(C, ℂ) →ₗ[ℂ] H →ₗ[ℂ] H` to `LinearMap.mk₂ ℂ (fun f x => ∫ h, f h • U h x ∂μ) (fun f f' x => by`.

Rewrite using `[← integral_add (hint f x) (hint f' x)]`. Simplify using `[add_smul])`. Use the proof step `(fun c f x => by`. Rewrite using `[← integral_smul]`. Simplify using `[mul_smul])`.

Use the proof step `(fun f x y => by`. Rewrite using `[← integral_add (hint f x) (hint f y)]`. Use the proof step `simp)`. Use the proof step `(fun c f x => by`. Rewrite using `[← integral_smul]`.

Simplify using `[smul_comm c])`. Set `T : C(C, ℂ) →L[ℂ] H →L[ℂ] H` to `T₀.mkContinuous₂ (μ.real Set.univ) (fun f x => by`. Establish `: ‖∫ h, f h • U h x ∂μ‖ ≤ (‖f‖ * ‖x‖) * μ.real Set.univ` using `norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun h => by`. Rewrite using `[norm_smul, hn]`. Conclude with `mul_le_mul_of_nonneg_right (f.norm_coe_le_norm h) (norm_nonneg _))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hT : ∀ f x, T f x = ∫ h, f h • U h x ∂μ` using `fun _ _ => rfl`. Establish `hB : ∀ f, ∀ B : H →L[ℂ] H, (∀ h, U h * B = B * U h) → B * T f = T f * B`. Introduce `f B hB`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `B (T f x) = T f (B x)`. Rewrite using `[hT, hT, ← B.integral_comp_comm (hint f x)]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[map_smul]`.

Use `congr 1`. Conclude with `(congrArg (fun L : H →L[ℂ] H => L x) (hB h)).symm`. Set `w : H` to `U g v - v`. Establish `hw : w ≠ 0` using `sub_ne_zero.2 hg`. Set `f : C(C, ℂ)` to `⟨fun h => inner ℂ (U h w) w, (hc w).inner continuous_const⟩`.

Set `F : C(C, C(C, ℂ))` to `(f.comp ⟨fun p : C × C => p.1⁻¹ * p.2, by fun_prop⟩).curry`. Establish `hF : ∀ k, U k * T f = T (F k)`. Introduce `k`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `U k (T f x) = T (F k) x`.

Rewrite using `[hT, hT, ← (U k).integral_comp_comm (hint f x), ← integral_mul_left_eq_self (fun h => F k h • U h x) k]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[map_smul, happ]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `f h = f (k⁻¹ * (k * h))`. Rewrite using `[inv_mul_cancel_left]`. Use `alg_case U hstar (T f) (hB f) ?_ ?_` and prove the remaining obligations. Repeatedly rewrite using `[hF]`. Conclude with `T.continuous.comp F.continuous`.

Introduce `h0`. Establish `h1 : T f w = 0`. Establish `h2` using `hB f (U g) (fun h => by rw [← map_mul, ← map_mul, mul_comm])`. Rewrite `h2` using `[h0]`. Establish `h3 : T f v = T f (U g v)` using `congrArg (fun L : H →L[ℂ] H => L v) h2`.

Rewrite using `[map_sub, ← h3, sub_self]`. Establish `h2 : ∫ h, ((‖f h‖ ^ 2 : ℝ) : ℂ) ∂μ = 0`. Use `integral_inner (𝕜 := ℂ) (hint f w) w` as an intermediate fact. Rewrite `this` using `[← hT, h1, inner_zero_right]`. Rewrite using `[← this]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[inner_smul_right, ← inner_conj_symm w (U h w)]`. Express the relevant statement in the definitionally equal form `_ = f h * (starRingEnd ℂ) (f h)`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Rewrite `h2` using `[integral_complex_ofReal, Complex.ofReal_eq_zero]`. Use `(Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1) (f := fun h => ‖f h‖ ^ 2) (by fun_prop) (HasCompactSupport.of_compactSpace _) (fun h => by positivity) ?_).ne' h2` and prove the remaining obligations. Establish `: f 1 = inner ℂ w w`. Express the relevant statement in the definitionally equal form `inner ℂ (U 1 w) w = _`. Rewrite using `[map_one]`.

Both sides reduce to the same expression. Simplify using `only [this]`. Conclude with `pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))`.
-/
private theorem hilbert_case {C H : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
    (μ : Measure C) [μ.IsHaarMeasure]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : C →* (H →L[ℂ] H)) (hn : ∀ h v, ‖U h v‖ = ‖v‖) (hc : ∀ v, Continuous fun h => U h v)
    {g : C} {v : H} (hg : U g v ≠ v) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have happ : ∀ a b x, U a (U b x) = U (a * b) x := by
    intro a b x
    rw [map_mul]
    rfl
  have hstar : ∀ h, star (U h) = U h⁻¹ := by
    intro h
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have := (LinearIsometry.mk (U h).toLinearMap (hn h)).inner_map_map (U h⁻¹ x) y
    rw [← this]
    change inner ℂ (U h (U h⁻¹ x)) (U h y) = _
    rw [happ, mul_inv_cancel, map_one]
    rfl
  have hint : ∀ (f : C(C, ℂ)) (x : H), Integrable (fun h => f h • U h x) μ := fun f x =>
    (f.continuous.smul (hc x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T₀ : C(C, ℂ) →ₗ[ℂ] H →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun f x => ∫ h, f h • U h x ∂μ)
    (fun f f' x => by
      rw [← integral_add (hint f x) (hint f' x)]
      simp [add_smul])
    (fun c f x => by
      rw [← integral_smul]
      simp [mul_smul])
    (fun f x y => by
      rw [← integral_add (hint f x) (hint f y)]
      simp)
    (fun c f x => by
      rw [← integral_smul]
      simp [smul_comm c])
  let T : C(C, ℂ) →L[ℂ] H →L[ℂ] H := T₀.mkContinuous₂ (μ.real Set.univ) (fun f x => by
    have : ‖∫ h, f h • U h x ∂μ‖ ≤ (‖f‖ * ‖x‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun h => by
        rw [norm_smul, hn]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm h) (norm_nonneg _))
    calc ‖T₀ f x‖ ≤ _ := this
      _ = _ := by ring)
  have hT : ∀ f x, T f x = ∫ h, f h • U h x ∂μ := fun _ _ => rfl
  have hB : ∀ f, ∀ B : H →L[ℂ] H, (∀ h, U h * B = B * U h) → B * T f = T f * B := by
    intro f B hB
    ext x
    change B (T f x) = T f (B x)
    rw [hT, hT, ← B.integral_comp_comm (hint f x)]
    congr 1
    funext h
    rw [map_smul]
    congr 1
    exact (congrArg (fun L : H →L[ℂ] H => L x) (hB h)).symm
  let w : H := U g v - v
  have hw : w ≠ 0 := sub_ne_zero.2 hg
  let f : C(C, ℂ) := ⟨fun h => inner ℂ (U h w) w, (hc w).inner continuous_const⟩
  let F : C(C, C(C, ℂ)) :=
    (f.comp ⟨fun p : C × C => p.1⁻¹ * p.2, by fun_prop⟩).curry
  have hF : ∀ k, U k * T f = T (F k) := by
    intro k
    ext x
    change U k (T f x) = T (F k) x
    rw [hT, hT, ← (U k).integral_comp_comm (hint f x),
      ← integral_mul_left_eq_self (fun h => F k h • U h x) k]
    congr 1
    funext h
    rw [map_smul, happ]
    congr 1
    change f h = f (k⁻¹ * (k * h))
    rw [inv_mul_cancel_left]
  refine alg_case U hstar (T f) (hB f) ?_ ?_
  · simp_rw [hF]
    exact T.continuous.comp F.continuous
  · intro h0
    have h1 : T f w = 0 := by
      have h2 := hB f (U g) (fun h => by rw [← map_mul, ← map_mul, mul_comm])
      rw [h0] at h2
      have h3 : T f v = T f (U g v) := congrArg (fun L : H →L[ℂ] H => L v) h2
      rw [map_sub, ← h3, sub_self]
    have h2 : ∫ h, ((‖f h‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      have := integral_inner (𝕜 := ℂ) (hint f w) w
      rw [← hT, h1, inner_zero_right] at this
      rw [← this]
      congr 1
      funext h
      rw [inner_smul_right, ← inner_conj_symm w (U h w)]
      change _ = f h * (starRingEnd ℂ) (f h)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1)
      (f := fun h => ‖f h‖ ^ 2) (by fun_prop) (HasCompactSupport.of_compactSpace _)
      (fun h => by positivity) ?_).ne' h2
    have : f 1 = inner ℂ w w := by
      change inner ℂ (U 1 w) w = _
      rw [map_one]
      rfl
    simp only [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))

end UpperTheory.Reformulated.B.CharactersSeparatePoints

/- English proof (translation)
Introduce `C _ _ _ _ _ g hg`. Use `borelize C`. Set `μ : Measure C` to `Measure.haar`. Set `m : C(C, C(C, C))` to `ContinuousMap.curry ⟨fun p : C × C => p.1 * p.2, by fun_prop⟩`. Establish `hm : ∀ h, MeasurePreserving (m h) μ μ` using `fun h => measurePreserving_mul_left μ h`.

Set `V : C → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ)` to `fun h => Lp.compMeasurePreservingₗᵢ ℂ (m h) (hm h)`. Establish `hV : ∀ h x, V h x = Lp.compMeasurePreserving (m h) (hm h) x` using `fun _ _ => rfl`. Set `U : C →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)` to `{ toFun := fun h => (V h).toContinuousLinearMap map_one' := by`. Use `ContinuousLinearMap.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Lp.compMeasurePreserving (m 1) (hm 1) x = x`.

Use `Lp.compMeasurePreserving_id_apply x` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Conclude with `one_mul a`. Use the proof step `map_mul' := fun a b => by`. Use `ContinuousLinearMap.ext fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Lp.compMeasurePreserving (m (a * b)) (hm _) x = Lp.compMeasurePreserving (m a) (hm a) (Lp.compMeasurePreserving (m b) (hm b) x)`. Rewrite using `[← Lp.compMeasurePreserving_comp_apply]`. Use `congr 2`. Use function extensionality and compare the values at `c`. Conclude with `(mul_left_comm b a c).trans (mul_assoc a b c).symm |>.symm }`.

Take `⟨F, hF0, hF1, -⟩` from `exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := g)) (isClosed_singleton (x := (1 : C))) (Set.disjoint_singleton.2 hg)`. Set `G : C(C, ℂ)` to `⟨fun a => (F a : ℂ), by fun_prop⟩`. Use `hilbert_case μ U (fun h x => (V h).norm_map x) (fun x => continuous_const.compMeasurePreservingLp m.continuous hm (by simp)) (v := ContinuousMap.toLp 2 μ ℂ G) ?_` and prove the remaining obligations. Introduce `h0`. Establish `h0' : Lp.compMeasurePreserving (m g) (hm g) (ContinuousMap.toLp 2 μ ℂ G) = ContinuousMap.toLp 2 μ ℂ G` using `h0`.

Establish `h1 : ContinuousMap.toLp 2 μ ℂ (G.comp (m g)) = ContinuousMap.toLp 2 μ ℂ G`. Use `Eq.trans (Lp.ext ?_) h0'` and prove the remaining obligations. Establish `e1` using `ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (G.comp (m g))`. Establish `e2` using `Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ G) (hm g)`. Establish `e3` using `(hm g).quasiMeasurePreserving.ae_eq_comp (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ G)`.

Conclude with `e1.trans (e2.trans e3).symm`. Establish `h2 : (F (g * 1) : ℂ) = F 1` using `congrArg (fun f : C(C, ℂ) => f 1) (ContinuousMap.toLp_injective μ h1)`. Rewrite `h2` using `[mul_one, hF0 rfl, hF1 rfl]`. Simplify using `at h2`.
-/
theorem UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one.{u_1} :
    ∀ {C : Type u_1} [inst : CommGroup C] [inst_1 : TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
      {g : C}, g ≠ (1 : C) → ∃ (χ : C →ₜ* Circle), (χ : C → Circle) g ≠ (1 : Circle) := by
  intro C _ _ _ _ _ g hg
  borelize C
  let μ : Measure C := Measure.haar
  let m : C(C, C(C, C)) := ContinuousMap.curry ⟨fun p : C × C => p.1 * p.2, by fun_prop⟩
  have hm : ∀ h, MeasurePreserving (m h) μ μ := fun h => measurePreserving_mul_left μ h
  let V : C → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ) := fun h => Lp.compMeasurePreservingₗᵢ ℂ (m h) (hm h)
  have hV : ∀ h x, V h x = Lp.compMeasurePreserving (m h) (hm h) x := fun _ _ => rfl
  let U : C →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun h => (V h).toContinuousLinearMap
      map_one' := by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m 1) (hm 1) x = x
        convert Lp.compMeasurePreserving_id_apply x
        funext a
        exact one_mul a
      map_mul' := fun a b => by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m (a * b)) (hm _) x =
          Lp.compMeasurePreserving (m a) (hm a) (Lp.compMeasurePreserving (m b) (hm b) x)
        rw [← Lp.compMeasurePreserving_comp_apply]
        congr 2
        funext c
        exact (mul_left_comm b a c).trans (mul_assoc a b c).symm |>.symm }
  obtain ⟨F, hF0, hF1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := g)) (isClosed_singleton (x := (1 : C)))
    (Set.disjoint_singleton.2 hg)
  let G : C(C, ℂ) := ⟨fun a => (F a : ℂ), by fun_prop⟩
  refine hilbert_case μ U (fun h x => (V h).norm_map x)
    (fun x => continuous_const.compMeasurePreservingLp m.continuous hm (by simp))
    (v := ContinuousMap.toLp 2 μ ℂ G) ?_
  intro h0
  have h0' : Lp.compMeasurePreserving (m g) (hm g) (ContinuousMap.toLp 2 μ ℂ G) =
      ContinuousMap.toLp 2 μ ℂ G := h0
  have h1 : ContinuousMap.toLp 2 μ ℂ (G.comp (m g)) = ContinuousMap.toLp 2 μ ℂ G := by
    refine Eq.trans (Lp.ext ?_) h0'
    have e1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (G.comp (m g))
    have e2 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ G) (hm g)
    have e3 := (hm g).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ G)
    exact e1.trans (e2.trans e3).symm
  have h2 : (F (g * 1) : ℂ) = F 1 :=
    congrArg (fun f : C(C, ℂ) => f 1) (ContinuousMap.toLp_injective μ h1)
  rw [mul_one, hF0 rfl, hF1 rfl] at h2
  simp at h2
