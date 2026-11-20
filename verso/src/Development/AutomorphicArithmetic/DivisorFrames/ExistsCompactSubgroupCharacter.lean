import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

/- English proof (translation)
Take `⟨δ, hδ, h⟩` from `Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)`. Use `⟨δ, hδ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `key : ∀ k : ℕ, ∀ x : K, ‖x‖ < δ → ‖ψ x - 1‖ ≤ (2 / 3 : ℝ) ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `x hx`. Use `h (x := x) (by simpa using hx)` as an intermediate fact. Rewrite `this` using `[AddChar.map_zero_eq_one, dist_eq_norm]`. Simplify using `only [pow_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k ih`. Introduce `x hx`. Establish `h1` using `h (x := x) (by simpa using hx)`. Rewrite `h1` using `[AddChar.map_zero_eq_one, dist_eq_norm]`.

Establish `h2` using `ih (x + x) (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x x) (by simpa using hx))`. Establish `e : ψ (x + x) - 1 = (ψ x - 1) * (ψ x + 1)` using `by rw [AddChar.map_add_eq_mul]; ring`. Rewrite `h2` using `[e, norm_mul]`. Establish `h3 : (2 : ℝ) ≤ ‖ψ x + 1‖ + ‖ψ x - 1‖`. Use `norm_sub_le (ψ x + 1) (ψ x - 1)` as an intermediate fact.

Establish `e2 : ψ x + 1 - (ψ x - 1) = 2` using `by ring`. Rewrite `this` using `[e2]`. Simplify using `using this`. Establish `h4 : ‖ψ x - 1‖ * (3 / 2) ≤ ‖ψ x - 1‖ * ‖ψ x + 1‖` using `mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)`. Rewrite using `[pow_succ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl : Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)`. Use `ge_of_tendsto' hl fun k => key k x hx` as an intermediate fact. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 this)`.
-/
private theorem char_one_near {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have key : ∀ k : ℕ, ∀ x : K, ‖x‖ < δ → ‖ψ x - 1‖ ≤ (2 / 3 : ℝ) ^ k := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := h (x := x) (by simpa using hx)
      rw [AddChar.map_zero_eq_one, dist_eq_norm] at this
      simp only [pow_zero]; linarith
    | succ k ih =>
      intro x hx
      have h1 := h (x := x) (by simpa using hx)
      rw [AddChar.map_zero_eq_one, dist_eq_norm] at h1
      have h2 := ih (x + x) (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x x) (by simpa using hx))
      have e : ψ (x + x) - 1 = (ψ x - 1) * (ψ x + 1) := by rw [AddChar.map_add_eq_mul]; ring
      rw [e, norm_mul] at h2
      have h3 : (2 : ℝ) ≤ ‖ψ x + 1‖ + ‖ψ x - 1‖ := by
        have := norm_sub_le (ψ x + 1) (ψ x - 1)
        have e2 : ψ x + 1 - (ψ x - 1) = 2 := by ring
        rw [e2] at this
        simpa using this
      have h4 : ‖ψ x - 1‖ * (3 / 2) ≤ ‖ψ x - 1‖ * ‖ψ x + 1‖ :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      rw [pow_succ]; linarith
  have hl : Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := ge_of_tendsto' hl fun k => key k x hx
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/- English proof (translation)
Use `haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A`. Take `⟨δ, hδ, hone⟩` from `char_one_near ψ hc`. Take `⟨y₀, hy₀⟩` from `AddChar.ne_one_iff.1 hψ`. Establish `hs : Continuous b.equivFun.symm` using `IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap`. Establish `hf : Continuous b.equivFun` using `IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap`.

Establish `hU' : b.equivFun.symm ⁻¹' U ∈ 𝓝 (0 : ι → K)` using `hs.continuousAt.preimage_mem_nhds (by simpa using hU)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hU'`. Use `set R : ℝ := ‖y₀‖ / ε + 1 with hR`. Establish `hR0 : 0 < R` using `by positivity`. Set `T : (ι → K) →ₗ[K] A` to `Fintype.linearCombination K c`.

Set `L₀ : AddSubgroup (ι → K)` to `{ carrier := {a | ∀ i, ‖a i‖ ≤ R} zero_mem' := fun i => by simpa using hR0.le add_mem' := fun {a a'} ha ha' i => (IsUltrametricDist.norm_add_le_max (a i) (a' i)).trans (max_le (ha i) (ha' i)) neg_mem' := fun {a} ha i => by simpa using ha i }`. Establish `hBT : ∀ x a, B x (T a) = ∑ i, a i * b.repr x i`. Introduce `x a`. Simplify using `[T, Fintype.linearCombination_apply, hB]`. Establish `hset : {x | ∀ y ∈ L₀.map T.toAddMonoidHom, ψ (B x y) = 1} = {x | ∀ a : ι → K, (∀ i, ‖a i‖ ≤ R) → ψ (∑ i, a i * b.repr x i) = 1}`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Rewrite using `[← hBT]`. Conclude with `h _ ⟨a, ha, rfl⟩`.

Introduce and unpack `h _ ⟨a, ha, rfl⟩`. Conclude with `(congrArg ψ (hBT x a)).trans (h a ha)`. Use `⟨L₀.map T.toAddMonoidHom, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : (L₀ : Set (ι → K)) = Set.univ.pi fun _ => Metric.closedBall (0 : K) R`. Use extensionality with `a`.

Simplify using `[L₀]`. Rewrite using `[AddSubgroup.coe_map, h0]`. Conclude with `(isCompact_univ_pi fun i => isCompact_closedBall _ _).image (IsModuleTopology.continuous_of_linearMap T)`. Rewrite using `[hset, isOpen_iff_mem_nhds]`. Introduce `x hx`.

Establish `hn : b.equivFun ⁻¹' Metric.ball (b.equivFun x) (δ / R) ∈ 𝓝 x` using `hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))`. Use `mem_of_superset hn fun x' hx' a ha => ?_` and prove the remaining obligations. Establish `e : ∑ i, a i * b.repr x' i = ∑ i, a i * b.repr x i + ∑ i, a i * (b.repr x' i - b.repr x i)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Rewrite using `[e, AddChar.map_add_eq_mul, hx a ha, one_mul]`. Use `Finset.sum_induction _ (fun z => ψ z = 1) (fun z z' hz hz' => ?_) ψ.map_zero_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.map_add_eq_mul, hz, hz', one_mul]`. Apply `hone` to reduce the goal to its premises. Establish `h1 : ‖b.repr x' i - b.repr x i‖ < δ / R`.

Use `(dist_le_pi_dist (b.equivFun x') (b.equivFun x) i).trans_lt (Metric.mem_ball.1 hx')` as an intermediate fact. Simplify `this` using `[dist_eq_norm]`. Rewrite `h1` using `[lt_div_iff₀ hR0]`. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (b.repr x' i - b.repr x i))` as an intermediate fact.

Combine the linear relations using `[mul_comm R ‖b.repr x' i - b.repr x i‖]`. Establish `: {x | ∀ y ∈ L₀.map T.toAddMonoidHom, ψ (B x y) = 1} = ⋂ y ∈ L₀.map T.toAddMonoidHom, {x : A | ψ (B x y) = 1}`. Use extensionality with `l`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Rewrite using `[this]`.

Conclude with `isClosed_biInter fun t _ => isClosed_eq (hc.comp (IsModuleTopology.continuous_of_linearMap (B.flip t))) continuous_const`. Rewrite using `[hset]`. Introduce `x hx`. Establish `: b.equivFun x ∈ Metric.ball (0 : ι → K) ε`. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff hε]`.

Introduce `i`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Rewrite `hlt` using `[Module.Basis.equivFun_apply]`. Establish `hx0 : 0 < ‖b.repr x i‖` using `hε.trans_le hlt`.

Establish `hx1 : b.repr x i ≠ 0` using `norm_pos_iff.1 hx0`. Establish `h` using `hx (Pi.single i (y₀ / b.repr x i)) fun j => by`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same, norm_div]`.

Use `div_le_div_of_nonneg_left (norm_nonneg y₀) hε hlt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Pi.single_eq_of_ne hj, norm_zero]`. Conclude with `hR0.le`. Rewrite `h` using `[Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp), Pi.single_eq_same, div_mul_cancel₀ _ hx1]`.

Conclude with `hy₀ h`. Simplify using `using hball this`.
-/
private theorem exists_dual {K A ι : Type} [NormedField K] [ProperSpace K] [IsUltrametricDist K] [AddCommGroup A]
    [Module K A] [TopologicalSpace A] [IsModuleTopology K A] [Fintype ι] (b : Module.Basis ι K A) (c : ι → A)
    (B : A →ₗ[K] A →ₗ[K] K) (hB : ∀ i x, B x (c i) = b.repr x i) (ψ : AddChar K ℂ) (hc : Continuous ψ)
    (hψ : ψ ≠ 1) {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ L : AddSubgroup A, IsCompact (L : Set A) ∧ IsOpen {x | ∀ y ∈ L, ψ (B x y) = 1} ∧
      IsClosed {x | ∀ y ∈ L, ψ (B x y) = 1} ∧ {x | ∀ y ∈ L, ψ (B x y) = 1} ⊆ U := by
  classical
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  obtain ⟨δ, hδ, hone⟩ := char_one_near ψ hc
  obtain ⟨y₀, hy₀⟩ := AddChar.ne_one_iff.1 hψ
  have hs : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hf : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hU' : b.equivFun.symm ⁻¹' U ∈ 𝓝 (0 : ι → K) := hs.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  set R : ℝ := ‖y₀‖ / ε + 1 with hR
  have hR0 : 0 < R := by positivity
  let T : (ι → K) →ₗ[K] A := Fintype.linearCombination K c
  let L₀ : AddSubgroup (ι → K) :=
    { carrier := {a | ∀ i, ‖a i‖ ≤ R}
      zero_mem' := fun i => by simpa using hR0.le
      add_mem' := fun {a a'} ha ha' i =>
        (IsUltrametricDist.norm_add_le_max (a i) (a' i)).trans (max_le (ha i) (ha' i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hBT : ∀ x a, B x (T a) = ∑ i, a i * b.repr x i := by
    intro x a
    simp [T, Fintype.linearCombination_apply, hB]
  have hset : {x | ∀ y ∈ L₀.map T.toAddMonoidHom, ψ (B x y) = 1} =
      {x | ∀ a : ι → K, (∀ i, ‖a i‖ ≤ R) → ψ (∑ i, a i * b.repr x i) = 1} := by
    ext x
    constructor
    · intro h a ha
      rw [← hBT]
      exact h _ ⟨a, ha, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩
      exact (congrArg ψ (hBT x a)).trans (h a ha)
  refine ⟨L₀.map T.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · have h0 : (L₀ : Set (ι → K)) = Set.univ.pi fun _ => Metric.closedBall (0 : K) R := by
      ext a; simp [L₀]
    rw [AddSubgroup.coe_map, h0]
    exact (isCompact_univ_pi fun i => isCompact_closedBall _ _).image (IsModuleTopology.continuous_of_linearMap T)
  · rw [hset, isOpen_iff_mem_nhds]
    intro x hx
    have hn : b.equivFun ⁻¹' Metric.ball (b.equivFun x) (δ / R) ∈ 𝓝 x :=
      hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
    refine mem_of_superset hn fun x' hx' a ha => ?_
    have e : ∑ i, a i * b.repr x' i = ∑ i, a i * b.repr x i + ∑ i, a i * (b.repr x' i - b.repr x i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, AddChar.map_add_eq_mul, hx a ha, one_mul]
    refine Finset.sum_induction _ (fun z => ψ z = 1) (fun z z' hz hz' => ?_) ψ.map_zero_eq_one fun i _ => ?_
    · rw [AddChar.map_add_eq_mul, hz, hz', one_mul]
    · apply hone
      have h1 : ‖b.repr x' i - b.repr x i‖ < δ / R := by
        have := (dist_le_pi_dist (b.equivFun x') (b.equivFun x) i).trans_lt (Metric.mem_ball.1 hx')
        simpa [dist_eq_norm] using this
      rw [lt_div_iff₀ hR0] at h1
      rw [norm_mul]
      have := mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (b.repr x' i - b.repr x i))
      linarith [mul_comm R ‖b.repr x' i - b.repr x i‖]
  · have : {x | ∀ y ∈ L₀.map T.toAddMonoidHom, ψ (B x y) = 1} =
        ⋂ y ∈ L₀.map T.toAddMonoidHom, {x : A | ψ (B x y) = 1} := by
      ext l; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun t _ =>
      isClosed_eq (hc.comp (IsModuleTopology.continuous_of_linearMap (B.flip t))) continuous_const
  · rw [hset]
    intro x hx
    have : b.equivFun x ∈ Metric.ball (0 : ι → K) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro i
      by_contra hlt
      push Not at hlt
      rw [Module.Basis.equivFun_apply] at hlt
      have hx0 : 0 < ‖b.repr x i‖ := hε.trans_le hlt
      have hx1 : b.repr x i ≠ 0 := norm_pos_iff.1 hx0
      have h := hx (Pi.single i (y₀ / b.repr x i)) fun j => by
        by_cases hj : j = i
        · subst hj
          rw [Pi.single_eq_same, norm_div]
          have := div_le_div_of_nonneg_left (norm_nonneg y₀) hε hlt
          linarith
        · rw [Pi.single_eq_of_ne hj, norm_zero]; exact hR0.le
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp),
        Pi.single_eq_same, div_mul_cancel₀ _ hx1] at h
      exact hy₀ h
    simpa using hball this

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [sigR, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`.
-/
private theorem sigR_smul' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) : sigR R σ (r • a) = r • sigR R σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hJ v ψ hc hψ U hU`. Use `haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v`. Use `haveI : Module.Finite F E := GlobalTheory.LocTateInt.finite_FE`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Set `b` to `Module.finBasis F E`.

Establish `hσ : Function.Surjective σ` using `(Algebra.IsAlgebraic.algHom_bijective σ).2`. Use `choose τ hτ using hσ`. Set `B : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v` to `LinearMap.mk₂ (Fv F v) (fun x y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)) (fun x x' y => by rw [pairV, pairV, pairV, add_dotProduct, map_add]) (fun r x y => by rw [pairV, pairV, smul_dotProduct, map_smul]) (fun x y y' => by rw [pairV_add_right, map_add]) (fun r …`. Establish `e : (fun i => sigR (Fv F v) σ ((r • y) i)) = r • fun i => sigR (Fv F v) σ (y i)`. Use function extensionality and compare the values at `fun i => sigR_smul' _ σ r (y i)`.

Rewrite using `[pairV, pairV, e, Matrix.mulVec_smul, dotProduct_smul, map_smul])`. Use `exists_dual (Pi.basis fun _ : Fin n => Algebra.TensorProduct.basis (Fv F v) b) (fun p i => inclR (Fv F v) (τ ((J⁻¹ *ᵥ Pi.single p.1 (b.traceDual p.2)) i))) B ?_ ψ hc hψ hU` and prove the remaining obligations. Introduce and unpack `⟨j, k⟩ x`. Establish `e1 : (fun i => sigR (Fv F v) σ (inclR (Fv F v) (τ ((J⁻¹ *ᵥ Pi.single j (b.traceDual k)) i)))) = (inclR (F` using `F) (Fv F v)) ∘ (J⁻¹ *ᵥ Pi.single j (b.traceDual k)) := by`. Use function extensionality and compare the values at `i`.

Simplify using `only [sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one, hτ, Function.comp_apply]`. Establish `e2 : J.map (inclR (F` using `F) (Fv F v)) *ᵥ ((inclR (F := F) (Fv F v)) ∘ (J⁻¹ *ᵥ Pi.single j (b.traceDual k))) = Pi.single j ((1 : Fv F v) ⊗ₜ[F] b.traceDual k) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[← RingHom.map_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mulVec]`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_same]`. Both sides reduce to the same expression. Rewrite using `[Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]`. Use `show Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x _) = _`.

Rewrite using `[pairV, e1, e2, dotProduct_single, Pi.basis_repr, mul_comm, ← GlobalTheory.TraceAnnCompact.trace_traceDual_mul (Fv F v) b k (x j), Algebra.traceForm_apply]`.
-/
theorem UpperTheory.exists_compact_subgroup_character :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
        ∀ (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 → ∀ U ∈ 𝓝 (0 : Fin n → Fv F v ⊗[F] E),
        ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsCompact (L : Set (Fin n → Fv F v ⊗[F] E)) ∧
          IsOpen {x | ∀ y ∈ L, ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)) = 1} ∧
          IsClosed {x | ∀ y ∈ L, ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)) = 1} ∧
          {x | ∀ y ∈ L, ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)) = 1} ⊆ U := by
  intro F E _ _ _ _ _ σ n J hJ v ψ hc hψ U hU
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : Module.Finite F E := GlobalTheory.LocTateInt.finite_FE
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  have hσ : Function.Surjective σ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  choose τ hτ using hσ
  let B : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v :=
    LinearMap.mk₂ (Fv F v) (fun x y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y))
      (fun x x' y => by rw [pairV, pairV, pairV, add_dotProduct, map_add])
      (fun r x y => by rw [pairV, pairV, smul_dotProduct, map_smul])
      (fun x y y' => by rw [pairV_add_right, map_add])
      (fun r x y => by
        have e : (fun i => sigR (Fv F v) σ ((r • y) i)) = r • fun i => sigR (Fv F v) σ (y i) :=
          funext fun i => sigR_smul' _ σ r (y i)
        rw [pairV, pairV, e, Matrix.mulVec_smul, dotProduct_smul, map_smul])
  refine exists_dual (Pi.basis fun _ : Fin n => Algebra.TensorProduct.basis (Fv F v) b)
    (fun p i => inclR (Fv F v) (τ ((J⁻¹ *ᵥ Pi.single p.1 (b.traceDual p.2)) i))) B ?_ ψ hc hψ hU
  rintro ⟨j, k⟩ x
  have e1 : (fun i => sigR (Fv F v) σ (inclR (Fv F v) (τ ((J⁻¹ *ᵥ Pi.single j (b.traceDual k)) i)))) =
      (inclR (F := F) (Fv F v)) ∘ (J⁻¹ *ᵥ Pi.single j (b.traceDual k)) := by
    funext i
    simp only [sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, hτ, Function.comp_apply]
  have e2 : J.map (inclR (F := F) (Fv F v)) *ᵥ ((inclR (F := F) (Fv F v)) ∘ (J⁻¹ *ᵥ Pi.single j (b.traceDual k))) =
      Pi.single j ((1 : Fv F v) ⊗ₜ[F] b.traceDual k) := by
    funext i
    rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mulVec]
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]
  show Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x _) = _
  rw [pairV, e1, e2, dotProduct_single, Pi.basis_repr, mul_comm,
    ← GlobalTheory.TraceAnnCompact.trace_traceDual_mul (Fv F v) b k (x j), Algebra.traceForm_apply]
