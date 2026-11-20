import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

/- English proof (translation)
Use `⟨fun h => ?_, fun h z => Reduction.euclidNorm_vecMul_unitary h z⟩` and prove the remaining obligations. Establish `hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z`. Introduce `z`. Use `h z` as an intermediate fact. Rewrite `this` using `[Reduction.euclidNorm, Reduction.euclidNorm, Real.sqrt_inj (by positivity) (by positivity)]`.

Simplify using `only [Real.norm_eq_abs, sq_abs] at this`. Simplify `this` using `only [dotProduct, sq]`. Establish `hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z`. Introduce `x z`. Establish `h1` using `hq (x + z)`.

Rewrite `h1` using `[add_vecMul]`. Simplify using `only [add_dotProduct, dotProduct_add, hq] at h1`. Rewrite `h1` using `[dotProduct_comm (z ᵥ* M), dotProduct_comm z x]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[mem_unitaryGroup_iff]`.

Use extensionality with `i j`. Use `hb (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[single_one_vecMul, single_one_vecMul, single_one_dotProduct]`. Rewrite using `[mul_apply, one_apply]`. Simplify using `only [star_apply, star_trivial]`.

Use `Eq.trans this ?_` and prove the remaining obligations. Simplify using `[Pi.single_apply]`.
-/
private theorem real_unitary_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M ∈ unitaryGroup (Fin n) ℝ := by
  refine ⟨fun h => ?_, fun h z => Reduction.euclidNorm_vecMul_unitary h z⟩
  have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
    intro z
    have := h z
    rw [Reduction.euclidNorm, Reduction.euclidNorm, Real.sqrt_inj (by positivity) (by positivity)] at this
    simp only [Real.norm_eq_abs, sq_abs] at this
    simpa only [dotProduct, sq] using this
  have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
    intro x z
    have h1 := hq (x + z)
    rw [add_vecMul] at h1
    simp only [add_dotProduct, dotProduct_add, hq] at h1
    rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
    linarith
  rw [mem_unitaryGroup_iff]
  ext i j
  have := hb (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at this
  rw [mul_apply, one_apply]
  simp only [star_apply, star_trivial]
  refine Eq.trans this ?_
  simp [Pi.single_apply]

/- English proof (translation)
Simplify using `only [mem_unitaryGroup_iff, ← Matrix.ext_iff, funext_iff, mul_apply, one_apply, star_apply, map_apply, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, ite_apply, Pi.one_apply, Pi.zero_apply]`. Conclude with `⟨fun h w i j => h i j w, fun h i j w => h w i j⟩`.
-/
private theorem pi_unitary_iff {ι : Type} {n : ℕ} (M : Matrix (Fin n) (Fin n) (ι → ℝ)) :
    M ∈ unitaryGroup (Fin n) (ι → ℝ) ↔ ∀ w, M.map (fun x => x w) ∈ unitaryGroup (Fin n) ℝ := by
  simp only [mem_unitaryGroup_iff, ← Matrix.ext_iff, funext_iff, mul_apply, one_apply, star_apply, map_apply,
    Finset.sum_apply, Pi.mul_apply, Pi.star_apply, ite_apply, Pi.one_apply, Pi.zero_apply]
  exact ⟨fun h w i j => h i j w, fun h i j w => h w i j⟩

/- English proof (translation)
Rewrite using `[infEmb_grpEq]`. Establish `h` using `congrArg (fun g : GL (Fin a) (TR.Rinf E) => TR.infEq E (g.val i j) w) (TR.pInf_infGL y)`. Use `Eq.trans ?_ h` and prove the remaining obligations. Conclude with `(congrFun ((TR.infEq E).apply_symm_apply ((TR.infGL E a y).val i j).1) w).symm`.
-/
private theorem infAt_grpEq {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (y : GL (Fin a) (TR.Rinf E)) (w : InfinitePlace E) (i j : Fin a) :
    (Reduction.infAt w (infEmb E a (grpEq E a y)) : Matrix (Fin a) (Fin a) w.Completion) i j =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y.val i j w) := by
  rw [infEmb_grpEq]
  have h := congrArg (fun g : GL (Fin a) (TR.Rinf E) => TR.infEq E (g.val i j) w) (TR.pInf_infGL y)
  refine Eq.trans ?_ h
  exact (congrFun ((TR.infEq E).apply_symm_apply ((TR.infGL E a y).val i j).1) w).symm

/- English proof (translation)
Introduce `E _ _ _ a y`. Express the relevant statement in the definitionally equal form `infEmb E a (grpEq E a y) ∈ Reduction.maxCompact (K := E) (n := a) ↔ _`. Establish `hf : ∀ v, Reduction.finAt v (infEmb E a (grpEq E a y)) ∈ GLnLocal.integralGL (v.adicCompletion E) a`. Introduce `v`. Establish `: Reduction.finAt v (infEmb E a (grpEq E a y)) = 1` using `by show (AdelicGLn.finiteRestrictedEquiv E a (AdelicGLn.prodEquiv E a (infEmb E a (grpEq E a y))).2) v = 1`.

Rewrite using `[prodEquiv_infEmb, map_one]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `one_mem _`. Rewrite using `[Reduction.mem_maxCompact, and_iff_left hf, pi_unitary_iff]`.

Use `forall_congr' fun w => ?_` and prove the remaining obligations. Rewrite using `[Reduction.mem_archCompact, ← real_unitary_iff]`. Use `set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef`. Establish `hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖` using `fun z => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) z`. Establish `e : ∀ z : Fin a → w.Completion, (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (infEmb E a (grpEq E a y)) : Matrix (Fin a) (Fin a) w.Completion)) j)) = (fun i => ψ.toRingHom (z i)) ᵥ* y.val.map (fun x => x w)`.

Introduce `z`. Use extensionality with `j`. Simplify using `only [vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[infAt_grpEq]`.

Conclude with `congrArg _ (ψ.apply_symm_apply _)`. Prove the components needed by the constructor for the conclusion. Introduce `h z`. Establish `hz : z = fun i => ψ.toRingHom (ψ.symm (z i))` using `funext fun i => (ψ.apply_symm_apply _).symm`. Rewrite using `[hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]`.

Introduce `h z`. Rewrite using `[← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]`.
-/
theorem UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces :
    UpperTheory.V.Fb.CptIff := by
  intro E _ _ _ a y
  change infEmb E a (grpEq E a y) ∈ Reduction.maxCompact (K := E) (n := a) ↔ _
  have hf : ∀ v, Reduction.finAt v (infEmb E a (grpEq E a y)) ∈ GLnLocal.integralGL (v.adicCompletion E) a := by
    intro v
    have : Reduction.finAt v (infEmb E a (grpEq E a y)) = 1 := by
      show (AdelicGLn.finiteRestrictedEquiv E a (AdelicGLn.prodEquiv E a (infEmb E a (grpEq E a y))).2) v = 1
      rw [prodEquiv_infEmb, map_one]
      rfl
    rw [this]
    exact one_mem _
  rw [Reduction.mem_maxCompact, and_iff_left hf, pi_unitary_iff]
  refine forall_congr' fun w => ?_
  rw [Reduction.mem_archCompact, ← real_unitary_iff]
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  have e : ∀ z : Fin a → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (infEmb E a (grpEq E a y)) : Matrix (Fin a) (Fin a) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* y.val.map (fun x => x w) := by
    intro z
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infAt_grpEq]
    exact congrArg _ (ψ.apply_symm_apply _)
  constructor
  · intro h z
    have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
    rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
  · intro h z
    rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
