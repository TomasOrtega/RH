import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

open Module Submodule

noncomputable section

namespace Formalism.F

/- English proof (translation)
Set `V : Submodule ℝ E` to `Submodule.span ℝ (L : Set E)`. Set `L' : Submodule ℤ V` to `L.comap (V.subtype.restrictScalars ℤ)`. Set `φ : L ≃ₗ[ℤ] L'` to `{ toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩ invFun := fun y => ⟨((y : V) : E), y.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `haveI : DiscreteTopology L' := DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L)) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) (by`. Introduce `a c h`.

Establish `h'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (Subtype.ext h'))`. Use `haveI : IsZLattice ℝ L' := ⟨by`. Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype]`.

Use `show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `hy`. Introduce `hx`. Conclude with `⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩`. Establish `hrank` using `ZLattice.rank ℝ L'`. Establish `hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L`.

Establish `h1` using `congrArg (Submodule.map L.subtype) b.span_eq`. Rewrite `h1` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Conclude with `h1`. Establish `key : Fintype.card ι = Module.finrank ℝ V`. Rewrite using `[← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]`.

Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`. Use `show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))`. Rewrite using `[← Submodule.span_span_of_tower ℤ ℝ, hLspan]`. Conclude with `key`.
-/
theorem linearIndependent_coe_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical

  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩
      invFun := fun y => ⟨((y : V) : E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (by
        intro a c h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hrank := ZLattice.rank ℝ L'
  have hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    exact h1
  have key : Fintype.card ι = Module.finrank ℝ V := by
    rw [← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]
  rw [linearIndependent_iff_card_eq_finrank_span]
  show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))
  rw [← Submodule.span_span_of_tower ℤ ℝ, hLspan]
  exact key

/- English proof (translation)
Introduce `E _ _ _ L hL`. Use `haveI := hL`. Rewrite using `[covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises. Conclude with `(Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos`.
-/
theorem covol_pos' : CovolPos := by
  intro E _ _ _ L hL
  haveI := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  apply Real.sqrt_pos.2
  exact (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos

/- English proof (translation)
Establish `hv' : 0 < ‖v‖` using `norm_pos_iff.2 hv`. Rewrite using `[discreteTopology_iff_isOpen_singleton_zero]`. Establish `hs : ({0} : Set (span ℤ ({v} : Set E))) = Metric.ball 0 ‖v‖`. Use extensionality with `⟨x, hx⟩`. Rewrite using `[Set.mem_singleton_iff, mem_ball_zero_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, norm_zero]`. Conclude with `hv'`. Introduce `h`.

Take `⟨n, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Establish `hn : ‖n • v‖ < ‖v‖` using `h`. Rewrite `hn` using `[← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]`. Establish `h1 : |(n : ℝ)| < 1` using `(mul_lt_iff_lt_one_left hv').1 hn`. Establish `hn0 : n = 0` using `Int.abs_lt_one_iff.1 (by exact_mod_cast h1)`.

Substitute `hn0` using the available equality. Conclude with `Subtype.ext (zero_smul ℤ v)`. Rewrite using `[hs]`. Conclude with `Metric.isOpen_ball`.
-/
theorem discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hs : ({0} : Set (span ℤ ({v} : Set E))) = Metric.ball 0 ‖v‖ := by
    ext ⟨x, hx⟩
    rw [Set.mem_singleton_iff, mem_ball_zero_iff]
    constructor
    · intro h
      rw [h, norm_zero]
      exact hv'
    · intro h
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have hn : ‖n • v‖ < ‖v‖ := h
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs] at hn
      have h1 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left hv').1 hn
      have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
      subst hn0
      exact Subtype.ext (zero_smul ℤ v)
  rw [hs]
  exact Metric.isOpen_ball

/- English proof (translation)
Introduce `E _ _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance`. Rewrite using `[covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]`. Simplify using `[Matrix.det_isEmpty]`.

Introduce `v hv haveI := discreteTopology_span_singleton hv`. Establish `hli : LinearIndependent ℤ (fun _ : Unit => v)`. Establish `hR : LinearIndependent ℝ (fun _ : Unit => v)`. Rewrite using `[linearIndependent_unique_iff]`. Use `first`.

Consider the case `exact hv`. Consider the case `(intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)`. Use `first`. Consider the case `exact hR.restrict_scalars' ℤ`. Consider the case `exact hR.restrict_scalars (by intro a c h; simpa using h)`.

Establish `hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E)`. Rewrite using `[Set.range_const]`. Set `b : Basis Unit ℤ (span ℤ ({v} : Set E))` to `(Basis.span hli).map (LinearEquiv.ofEq _ _ hr)`. Establish `hb : (fun i => (b i : E)) = fun _ => v`. Use function extensionality and compare the values at `i`.

Simplify using `[b, Basis.span_apply]`. Rewrite using `[covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem covol_basic_properties : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · intro v hv
    haveI := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) := by
      have hR : LinearIndependent ℝ (fun _ : Unit => v) := by
        rw [linearIndependent_unique_iff]
        first
          | exact hv
          | (intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)
      first
        | exact hR.restrict_scalars' ℤ
        | exact hR.restrict_scalars (by intro a c h; simpa using h)
    have hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E) := by
      rw [Set.range_const]
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hr)
    have hb : (fun i => (b i : E)) = fun _ => v := by
      funext i
      simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Formalism.F
