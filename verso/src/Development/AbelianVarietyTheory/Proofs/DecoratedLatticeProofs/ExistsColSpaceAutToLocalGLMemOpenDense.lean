import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

/- English proof (translation)
Introduce `E k _ _ _ _ _ ι hι A _ _ M e y V hV hy`. Use `haveI : T2Space k := by`. Rewrite using `[t2Space_iff_disjoint_nhds]`. Introduce `a b hab`. Establish `hne : valuation k (a - b) ≠ 0` using `(Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)`.

Set `γ : (ValueGroupWithZero k)ˣ` to `Units.mk0 _ hne`. Rewrite using `[Filter.disjoint_iff]`. Use `⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`. Introduce `z hz1 hz2`.

Establish `h` using `Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2) (show valuation k (z - a) < γ from hz1)`. Establish `e : (z - b) - (z - a) = a - b` using `by ring`. Rewrite `h` using `[e, Units.val_mk0]`. Conclude with `lt_irrefl _ h`. Set `φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ` to `fun m => (m, MulOpposite.op m⁻¹)`.

Establish `hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g`. Introduce `g`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Simplify using `[φ, Matrix.coe_units_inv]`. Take `⟨W, hW, rfl⟩` from `(Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV`.

Establish `hdet : y.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`. Establish `hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val`. Establish `h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate`. Use function extensionality and compare the values at `m`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`.

Rewrite using `[h1]`. Conclude with `ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt) (continuous_id.matrix_adjugate).continuousAt`. Establish `hφc : ContinuousAt φ y.val` using `ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)`. Establish `hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val`. Use `Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_` and prove the remaining obligations.

Rewrite using `[hφ]`. Conclude with `hy`. Conclude with `(isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet`. Establish `hD : DenseRange (fun m : Matrix A A E => m.map ι)` using `DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))`. Take `⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩` from `Dense.inter_nhds_nonempty hD hU`.

Establish `hm'u : IsUnit m'.det`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations. Introduce `h0`. Apply `hm'd` to reduce the goal to its premises. Use `show (m'.map ι).det = 0`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Set `n : Matrix (Fin M) (Fin M) E` to `m'.submatrix e.symm e.symm`. Establish `hn : IsUnit n.det`. Simplify `hm'u` using `[n, Matrix.det_submatrix_equiv_self]`. Use `⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩` and prove the remaining obligations.

Use `show Units.embedProduct _ _ ∈ W`. Rewrite using `[← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']`. Establish `h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n`. Conclude with `LinearMap.toMatrix'_toLin' n`. Rewrite using `[h2]`.

Establish `h3 : n.submatrix e e = m'`. Use extensionality with `i j`. Simplify using `[n]`. Rewrite using `[h3]`. Conclude with `hm'W`.
-/
theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := by
    rw [t2Space_iff_disjoint_nhds]
    intro a b hab
    have hne : valuation k (a - b) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)
    let γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hne
    rw [Filter.disjoint_iff]
    refine ⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩,
      {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h := Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2)
      (show valuation k (z - a) < γ from hz1)
    have e : (z - b) - (z - a) = a - b := by ring
    rw [e, Units.val_mk0] at h
    exact lt_irrefl _ h
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val := by
    have h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate := by
      funext m; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt)
      (continuous_id.matrix_adjugate).continuousAt
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
