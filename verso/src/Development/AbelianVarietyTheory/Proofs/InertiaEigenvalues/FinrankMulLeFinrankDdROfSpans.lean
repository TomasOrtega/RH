import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

/- English proof (translation)
Set `bD` to `Module.finBasis K D`. Set `s : Finset M` to `Finset.univ.image fun i => ((bD i : D) : M)`. Establish `hs : Submodule.span F (s : Set M) = ⊤`. Rewrite using `[eq_top_iff, ← h, Submodule.span_le]`. Introduce `x hx`.

Establish `hx'` using `congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hx'`. Rewrite using `[← hx']`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul F]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp

/- English proof (translation)
Use `haveI : Nontrivial F := by`. Use `nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `(PD.Fil 2).zero_mem`. Unfold `Spans mulR at hs`.

Use `set W := DdR PD ρ with hW`. Set `e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V` to `TensorProduct.comm Qp V F`. Establish `he : ∀ (b : F) (x : V ⊗[Qp] F), e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x`. Introduce `b x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v y => simp [e, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Establish `hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W → AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W`. Introduce `c x hx`.

Simplify using `only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Introduce `g`. Establish `hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) (actVdR PD ρ g y)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v z => simp [actVdR]`. Consider the case `add y y' hy hy' => simp only [map_add, hy, hy']`. Rewrite using `[hcomm, hx g]`. Set `D' : Submodule K (F ⊗[Qp] V)` to `{ carrier := e '' (W : Set (V ⊗[Qp] F)) add_mem' := by`.

Introduce and unpack `_ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩`. Conclude with `⟨x + y, W.add_mem hx hy, map_add e x y⟩`. Use the proof step `zero_mem' := ⟨0, W.zero_mem, map_zero e⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨x, hx, rfl⟩`.

Use `⟨_, hK c x hx, ?_⟩` and prove the remaining obligations. Rewrite using `[he, algebraMap_smul] }`. Establish `hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Take `⟨m, b, d, hd, hy⟩` from `hs (e.symm y)`. Establish `hy' : y = ∑ i, b i • e (d i)`. Rewrite using `[← e.apply_symm_apply y, hy, map_sum]`. Simplify using `only [he]`. Rewrite using `[hy']`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))`. Use `haveI : FiniteDimensional LL W := hfin`. Use `haveI : FiniteDimensional Qp W := Module.Finite.trans LL W`. Set `φ : W ≃ₗ[Qp] D'` to `LinearEquiv.ofBijective ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩ map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y) map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D') ⟨fun x y hxy => Subtype.ext (e.injectiv …`. Use `haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ`.

Use `haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'`. Establish `h1` using `finrank_le_of_span_subspace D' hspan`. Rewrite `h1` using `[Module.finrank_baseChange]`. Establish `h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W`. Rewrite using `[Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]`.

Establish `h3 : finrank Qp LL * finrank LL V = finrank Qp V` using `Module.finrank_mul_finrank _ _ _`. Establish `hpos : 0 < finrank Qp LL` using `Module.finrank_pos`. Establish `key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.le_of_mul_le_mul_left key hpos`.
-/
theorem finrank_mul_le_finrank_DdR_of_spans {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add, hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by
      rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos

end GlobalTheory.DRFil
