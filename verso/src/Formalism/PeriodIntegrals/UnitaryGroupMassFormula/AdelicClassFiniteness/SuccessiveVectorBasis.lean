import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf

noncomputable section

namespace PIW.AdelClassFin

open NumberField

/- English proof (translation)
Introduce `E _ _ m M hfg hspan`. Set `M' : Submodule ℤ (Fin m → E)` to `M.restrictScalars ℤ`. Establish `hfg' : M'.FG` using `hfg.restrictScalars`. Establish `: Module.Finite ℤ M'` using `Module.Finite.iff_fg.2 hfg'`. Establish `: Module.Free ℤ M'` using `Module.free_of_finite_type_torsion_free'`.

Set `b` to `Module.Free.chooseBasis ℤ M'`. Set `e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E` to `fun i => (b i : Fin m → E)`. Establish `hli : LinearIndependent ℤ e0` using `b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)`. Establish `hliQ : LinearIndependent ℚ e0` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hli`. Establish `hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i`.

Introduce `x hx`. Establish `h1` using `congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm`. Rewrite `h1` using `[Submodule.coe_sum]`. Simplify `h1` using `only [Submodule.coe_smul]`. Establish `hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0)`.

Introduce `x hx`. Rewrite using `[hrep x hx]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0)`. Introduce `c v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨i, rfl⟩` from `hv`.

Take `⟨y, hy0, hyi⟩` from `IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))`. Set `α : 𝓞 E` to `⟨y • c, hyi⟩`. Establish `hαv : α • e0 i ∈ M` using `M.smul_mem α (b i).2`. Establish `hyQ : (y : ℚ) ≠ 0` using `Int.cast_ne_zero.2 hy0`. Establish `: c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i)`.

Establish `hα : (α • e0 i) = ((y : E) * c) • e0 i`. Rewrite `*` using `[Algebra.smul_def (A := E)]`. Use `show ((y • c : E)) • e0 i = _`. Rewrite using `[zsmul_eq_mul]`. Rewrite using `[hα, mul_smul, ← smul_assoc]`.

Rewrite using `[show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by`. Rewrite using `[Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]`. Rewrite using `[one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (hmemM _ hαv)`.

Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul q x _ hx => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ _ hx`. Establish `hspanQ : Submodule.span ℚ (Set.range e0) = ⊤`. Set `W : Submodule E (Fin m → E)` to `{ toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid smul_mem' := fun c v hv => hstab c v hv }`. Establish `hle : Submodule.span E (M : Set (Fin m → E)) ≤ W` using `Submodule.span_le.2 fun x hx => hmemM x hx`. Rewrite `hle` using `[hspan]`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Conclude with `hle (Submodule.mem_top)`. Set `B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E)` to `Module.Basis.mk hliQ (by rw [hspanQ])`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E`.

Rewrite using `[← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]`. Simplify using the standard rewrite rules. Set `σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M'` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩` and prove the remaining obligations. Use `⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [hrep x hx]`. Rewrite using `[← Equiv.sum_comp σ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Both sides reduce to the same expression.
-/
theorem successive_vector_basis : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

end PIW.AdelClassFin

end
