import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ToricLatticeDenominators
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.ExportCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.IntegralHeckeForms.sIdx, Formalism.MainNotions.IntegralHeckeForms.lenR, signedLength, relLength_eq_length_quotient_comap]`. Use `push_cast`. Rewrite using `[sub_div]`.
-/
theorem sIdx_eq {W : Type} [AddCommGroup W] [Module R W] (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      (signedLength M N : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  simp only [Formalism.MainNotions.IntegralHeckeForms.sIdx, Formalism.MainNotions.IntegralHeckeForms.lenR, signedLength, relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]

/- English proof (translation)
Simplify using `only [sIdx_eq, signedLength, relLength_map_of_injective f hf]`.
-/
theorem sIdx_map {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') (hf : Function.Injective f) (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (M.map f) (N.map f) = Formalism.MainNotions.IntegralHeckeForms.sIdx l M N := by
  simp only [sIdx_eq, signedLength, relLength_map_of_injective f hf]

/- English proof (translation)
Establish `h` using `(IsLocalization.surj (nonZeroDivisors R) x).choose_spec`. Simplify using `only [vK, nval]`. Use `set p := (IsLocalization.surj (nonZeroDivisors R) x).choose`. Establish `inj` using `IsFractionRing.injective R (FractionRing R)`. Establish `h2 : (p.2 : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero _`.

Establish `h1 : p.1 ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, map_zero]`. Conclude with `mul_ne_zero hx ((map_ne_zero_iff _ inj).2 h2) h`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h1)`.

Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h2)`. Establish `h3` using `congrArg (Ring.ordFrac R) h`. Rewrite `h3` using `[map_mul, ordFrac_algebraMap_eq_exp hm.symm, ordFrac_algebraMap_eq_exp hn.symm]`. Establish `h4 : Ring.ordFrac R x = WithZero.exp ((m : ℤ) - n)`. Rewrite using `[WithZero.exp_sub, ← h3, mul_div_cancel_right₀ _ WithZero.exp_ne_zero]`.

Rewrite using `[h4, WithZero.log_exp, ← hm, ← hn, ← sub_div]`. Simplify using the standard rewrite rules.
-/
theorem vK_eq (l : ℕ) (x : FractionRing R) (hx : x ≠ 0) :
    vK R l x = (WithZero.log (Ring.ordFrac R x) : ℤ) /
      ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  have h := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  simp only [vK, nval]
  set p := (IsLocalization.surj (nonZeroDivisors R) x).choose
  have inj := IsFractionRing.injective R (FractionRing R)
  have h2 : (p.2 : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have h1 : p.1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact mul_ne_zero hx ((map_ne_zero_iff _ inj).2 h2) h
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h1)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h2)
  have h3 := congrArg (Ring.ordFrac R) h
  rw [map_mul, ordFrac_algebraMap_eq_exp hm.symm, ordFrac_algebraMap_eq_exp hn.symm] at h3
  have h4 : Ring.ordFrac R x = WithZero.exp ((m : ℤ) - n) := by
    rw [WithZero.exp_sub, ← h3, mul_div_cancel_right₀ _ WithZero.exp_ne_zero]
  rw [h4, WithZero.log_exp, ← hm, ← hn, ← sub_div]
  simp

variable {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

/- English proof (translation)
Use `and_congr_right fun _ => ⟨fun h => ⟨fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `Submodule.subset_span hx`. Rewrite `hx` using `[← h, Submodule.restrictScalars_mem]`. Take `⟨c, hc⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) (FractionRing R) (L : Set W) x hx`.

Rewrite `hc` using `[Submodule.span_eq]`. Conclude with `⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩`. Use `le_antisymm (Submodule.span_le.2 h.1) fun x hx => ?_` and prove the remaining obligations. Take `⟨c, hc, hx⟩` from `h.2 x hx`. Establish `hc' : algebraMap R (FractionRing R) c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hc`.

Establish `: x = (algebraMap R (FractionRing R) c)⁻¹ • (c • x)`. Rewrite using `[← algebraMap_smul (FractionRing R) c x, inv_smul_smul₀ hc']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`.
-/
theorem isLatIn_iff (V : Submodule (FractionRing R) W) (L : Submodule R W) :
    ToricLatticeDenominators.IsLatIn V L ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn L (V.restrictScalars R) := by
  refine and_congr_right fun _ => ⟨fun h => ⟨fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩
  · rw [← h]; exact Submodule.subset_span hx
  · rw [← h, Submodule.restrictScalars_mem] at hx
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) (FractionRing R)
      (L : Set W) x hx
    rw [Submodule.span_eq] at hc
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  · refine le_antisymm (Submodule.span_le.2 h.1) fun x hx => ?_
    obtain ⟨c, hc, hx⟩ := h.2 x hx
    have hc' : algebraMap R (FractionRing R) c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hc
    have : x = (algebraMap R (FractionRing R) c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul (FractionRing R) c x, inv_smul_smul₀ hc']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

def inside (V : Submodule (FractionRing R) W) (L : Submodule R W) : Submodule R ↥V :=
  L.comap (V.subtype.restrictScalars R)

/- English proof (translation)
Use `Submodule.map_comap_eq_self fun x hx => ⟨⟨x, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← h.2]`. Conclude with `Submodule.subset_span hx`.
-/
theorem map_inside {V : Submodule (FractionRing R) W} {L : Submodule R W} (h : ToricLatticeDenominators.IsLatIn V L) :
    (inside V L).map (V.subtype.restrictScalars R) = L := by
  refine Submodule.map_comap_eq_self fun x hx => ⟨⟨x, ?_⟩, rfl⟩
  rw [← h.2]; exact Submodule.subset_span hx

/- English proof (translation)
Establish `hinj : Function.Injective (V.subtype.restrictScalars R)` using `V.injective_subtype`. Prove the components needed by the constructor for the conclusion. Apply `Submodule.fg_of_fg_map_injective _ hinj` to reduce the goal to its premises. Rewrite using `[map_inside h]`. Conclude with `h.1`.

Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_subtype_top]`. Establish `: V.subtype '' (inside V L : Set V) = L` using `by conv_rhs => rw [← map_inside h]`. Both sides reduce to the same expression. Rewrite using `[this, h.2]`.
-/
theorem isLattice_inside {V : Submodule (FractionRing R) W} {L : Submodule R W} (h : ToricLatticeDenominators.IsLatIn V L) :
    Submodule.IsLattice (FractionRing R) (inside V L) := by
  have hinj : Function.Injective (V.subtype.restrictScalars R) := V.injective_subtype
  constructor
  · apply Submodule.fg_of_fg_map_injective _ hinj
    rw [map_inside h]; exact h.1
  · apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top]
    have : V.subtype '' (inside V L : Set V) = L := by
      conv_rhs => rw [← map_inside h]
      rfl
    rw [this, h.2]

/- English proof (translation)
Take `⟨h₁, h₂, g, hg, rfl⟩` from `h`. Use `isLattice_inside h₁` as an intermediate fact. Establish `e₂ : (inside V L₁).map ((g : V →ₗ[FractionRing R] V).restrictScalars R) = inside V L₂`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(hg w).1 hw`. Introduce `hv`. Use `⟨g.symm v, (hg _).2 ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[g.apply_symm_apply]`.

Conclude with `hv`. Rewrite using `[← map_inside h₁, ← map_inside h₂, sIdx_map _ (by exact V.injective_subtype), sIdx_eq, vK_eq _ _ (LinearEquiv.isUnit_det' g).ne_zero, (signedLength_eq_log_ordFrac_det_of_map_eq g e₂).2]`.
-/
theorem eq_sIdx_of_isIdx {l : ℕ} {V : Submodule (FractionRing R) W} {L₁ L₂ : Submodule R W} {x : ℝ}
    (h : ToricLatticeDenominators.IsIdx l V L₁ L₂ x) : x = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  obtain ⟨h₁, h₂, g, hg, rfl⟩ := h
  have := isLattice_inside h₁
  have e₂ : (inside V L₁).map ((g : V →ₗ[FractionRing R] V).restrictScalars R) = inside V L₂ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hg w).1 hw
    · intro hv
      refine ⟨g.symm v, (hg _).2 ?_, by simp⟩
      rw [g.apply_symm_apply]; exact hv
  rw [← map_inside h₁, ← map_inside h₂, sIdx_map _ (by exact V.injective_subtype), sIdx_eq,
    vK_eq _ _ (LinearEquiv.isUnit_det' g).ne_zero, (signedLength_eq_log_ordFrac_det_of_map_eq g e₂).2]

/- English proof (translation)
It suffices to establish `h : ∃ x, ToricLatticeDenominators.IsIdx l V L₁ L₂ x by`. Take `⟨x, hx⟩` from `h`. Rewrite using `[← eq_sIdx_of_isIdx hx]`. Conclude with `hx`. Use `isLattice_inside h₁` as an intermediate fact.

Use `isLattice_inside h₂` as an intermediate fact. Take `⟨g, e₃⟩` from `exists_linearEquiv_map_eq_of_isLattice (FractionRing R) (inside V L₁) (inside V L₂)`. Use `⟨_, h₁, h₂, g, fun v => ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v ∈ inside V L₁ ↔ g v ∈ inside V L₂`. Rewrite using `[← e₃]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨v, hv, rfl⟩`. Introduce and unpack `⟨w, hw, e⟩`. Establish `: w = v` using `g.injective e`.

Conclude with `this ▸ hw`.
-/
theorem isIdx_sIdx (l : ℕ) {V : Submodule (FractionRing R) W} {L₁ L₂ : Submodule R W}
    (h₁ : ToricLatticeDenominators.IsLatIn V L₁) (h₂ : ToricLatticeDenominators.IsLatIn V L₂) :
    ToricLatticeDenominators.IsIdx l V L₁ L₂ (Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂) := by
  suffices h : ∃ x, ToricLatticeDenominators.IsIdx l V L₁ L₂ x by
    obtain ⟨x, hx⟩ := h
    rw [← eq_sIdx_of_isIdx hx]; exact hx
  have := isLattice_inside h₁
  have := isLattice_inside h₂
  obtain ⟨g, e₃⟩ := exists_linearEquiv_map_eq_of_isLattice (FractionRing R) (inside V L₁) (inside V L₂)
  refine ⟨_, h₁, h₂, g, fun v => ?_, rfl⟩
  change v ∈ inside V L₁ ↔ g v ∈ inside V L₂
  rw [← e₃]
  constructor
  · intro hv; exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, e⟩
    have : w = v := g.injective e
    exact this ▸ hw

end Index

section Transport

/- English proof (translation)
Use `⟨fun h => ⟨Submodule.fg_of_fg_map_injective f hf h.1, (Submodule.map_le_map_iff_of_injective hf _ _).1 h.2.1, fun x hx => ?_⟩, fun h => ⟨h.1.map f, Submodule.map_mono h.2.1, ?_⟩⟩` and prove the remaining obligations. Take `⟨c, hc, y, hy, e⟩` from `h.2.2 (f x) ⟨x, hx, rfl⟩`. Rewrite `e` using `[← map_smul]`. Conclude with `⟨c, hc, hf e ▸ hy⟩`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨c, hc, hy⟩` from `h.2.2 x hx`. Conclude with `⟨c, hc, c • x, hy, map_smul _ _ _⟩`.
-/
theorem isLatIn_map_iff {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] (f : W →ₗ[R] W') (hf : Function.Injective f) (M V : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (M.map f) (V.map f) ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn M V := by
  refine ⟨fun h => ⟨Submodule.fg_of_fg_map_injective f hf h.1,
    (Submodule.map_le_map_iff_of_injective hf _ _).1 h.2.1, fun x hx => ?_⟩,
    fun h => ⟨h.1.map f, Submodule.map_mono h.2.1, ?_⟩⟩
  · obtain ⟨c, hc, y, hy, e⟩ := h.2.2 (f x) ⟨x, hx, rfl⟩
    rw [← map_smul] at e
    exact ⟨c, hc, hf e ▸ hy⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hy⟩ := h.2.2 x hx
    exact ⟨c, hc, c • x, hy, map_smul _ _ _⟩

/- English proof (translation)
Use `⟨?_, Submodule.span_mono (Set.image_mono h.2.1), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `h.1.map r`. Rewrite using `[← Submodule.map_coe, ← hs, Submodule.span_span_of_tower]`. Conclude with `Submodule.fg_span s.finite_toSet`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨c, hc, hy⟩` from `h.2.2 y hy`. Use `⟨algebraMap R S c, (map_ne_zero_iff _ hi).2 hc, Submodule.subset_span ⟨_, hy, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_smul, algebraMap_smul]`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, hx⟩` from `hx`. Take `⟨d, hd, hy⟩` from `hy`. Use `⟨c * d, mul_ne_zero hc hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem _ _ hy`. Consider the case `smul a x _ hx`. Take `⟨c, hc, hx⟩` from `hx`. Conclude with `⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ hx⟩`.
-/
theorem isLatIn_span {R S W W' : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (hi : Function.Injective (algebraMap R S)) [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] [Module S W'] [IsScalarTower R S W'] (r : W →ₗ[R] W') {L V : Submodule R W}
    (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Submodule.span S (r '' L)) (Submodule.span S (r '' V)) := by
  refine ⟨?_, Submodule.span_mono (Set.image_mono h.2.1), fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := h.1.map r
    rw [← Submodule.map_coe, ← hs, Submodule.span_span_of_tower]
    exact Submodule.fg_span s.finite_toSet
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, hc, hy⟩ := h.2.2 y hy
      refine ⟨algebraMap R S c, (map_ne_zero_iff _ hi).2 hc, Submodule.subset_span ⟨_, hy, ?_⟩⟩
      rw [map_smul, algebraMap_smul]
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ hx⟩

variable (O : Type) [CommRing O] [IsDomain O] (F : Type) [AddCommGroup F]
  [Module (FractionRing O) F] [Module O F] [IsScalarTower O (FractionRing O) F]
  (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O']

def toFrac : O' ⊗[O] F →ₗ[O'] FractionRing O' ⊗[O] F :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O' (FractionRing O')) LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toFrac_tmul (a : O') (x : F) :
    toFrac O F O' (a ⊗ₜ x) = algebraMap O' (FractionRing O') a ⊗ₜ x := rfl

/- English proof (translation)
Use `haveI : Module.Flat O (FractionRing O) := IsLocalization.flat _ (nonZeroDivisors O)`. Use `haveI : Module.Flat O F := Module.Flat.trans O (FractionRing O) F`. Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := F) ((Algebra.linearMap O' (FractionRing O')).restrictScalars O) (IsFractionRing.injective O' _)`. Establish `e : ∀ x, toFrac O F O' x = ((Algebra.linearMap O' (FractionRing O')).restrictScalars O).rTensor F x`. Introduce `x`.

Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Introduce `x y hxy`.

Conclude with `h (by rw [← e, ← e, hxy])`.
-/
theorem toFrac_injective : Function.Injective (toFrac O F O') := by
  haveI : Module.Flat O (FractionRing O) := IsLocalization.flat _ (nonZeroDivisors O)
  haveI : Module.Flat O F := Module.Flat.trans O (FractionRing O) F
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := F)
    ((Algebra.linearMap O' (FractionRing O')).restrictScalars O) (IsFractionRing.injective O' _)
  have e : ∀ x, toFrac O F O' x =
      ((Algebra.linearMap O' (FractionRing O')).restrictScalars O).rTensor F x := by
    intro x
    induction x with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  exact h (by rw [← e, ← e, hxy])

/- English proof (translation)
Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := O') k`. Take `⟨a, ha, q', hq'⟩` from `(Algebra.IsIntegral.isIntegral (R := O) q).isAlgebraic.exists_nonzero_dvd hq`. Establish `ha' : algebraMap O (FractionRing O) a ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha`. Establish `hq0 : algebraMap O' (FractionRing O') q ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O' _)).2 (nonZeroDivisors.ne_zero hq)`. Use `⟨(p * q') ⊗ₜ ((algebraMap O (FractionRing O) a)⁻¹ • x), Submodule.tmul_mem_baseChange_of_mem _ (V.smul_mem _ hx), ?_⟩` and prove the remaining obligations.

Establish `hx' : x = a • ((algebraMap O (FractionRing O) a)⁻¹ • x)`. Rewrite using `[← algebraMap_smul (FractionRing O) a, smul_inv_smul₀ ha']`. Use `conv_rhs => rw [hx', ← TensorProduct.smul_tmul]`. Rewrite using `[toFrac_tmul]`. Use `congr 1`.

Rewrite using `[← algebraMap_smul O' a, Algebra.smul_def, hq', map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem toFrac_smul_mem (hi : Function.Injective (algebraMap O O')) [Module.Finite O O']
    (V : Submodule (FractionRing O) F) (k : FractionRing O') (x : F) (hx : x ∈ V) :
    k ⊗ₜ[O] x ∈ ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O') k
  obtain ⟨a, ha, q', hq'⟩ := (Algebra.IsIntegral.isIntegral (R := O) q).isAlgebraic.exists_nonzero_dvd hq
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  have hq0 : algebraMap O' (FractionRing O') q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O' _)).2 (nonZeroDivisors.ne_zero hq)
  refine ⟨(p * q') ⊗ₜ ((algebraMap O (FractionRing O) a)⁻¹ • x),
    Submodule.tmul_mem_baseChange_of_mem _ (V.smul_mem _ hx), ?_⟩
  have hx' : x = a • ((algebraMap O (FractionRing O) a)⁻¹ • x) := by
    rw [← algebraMap_smul (FractionRing O) a, smul_inv_smul₀ ha']
  conv_rhs => rw [hx', ← TensorProduct.smul_tmul]
  rw [toFrac_tmul]
  congr 1
  rw [← algebraMap_smul O' a, Algebra.smul_def, hq', map_mul, map_mul]
  field_simp

/- English proof (translation)
Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul k x`. Take `⟨z, -, hz⟩` from `toFrac_smul_mem O F O' hi ⊤ k x trivial`.

Conclude with `⟨z, hz⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add _ _ _⟩`.
-/
theorem toFrac_surjective (hi : Function.Injective (algebraMap O O')) [Module.Finite O O'] :
    Function.Surjective (toFrac O F O') := by
  intro y
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | tmul k x =>
    obtain ⟨z, -, hz⟩ := toFrac_smul_mem O F O' hi ⊤ k x trivial
    exact ⟨z, hz⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[Submodule.restrictScalars_mem]`. Establish `: ∀ k : FractionRing O', k • y ∈ ((V.restrictScalars O).baseChange O').map (toFrac O F O')`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Introduce `k`. Rewrite using `[TensorProduct.smul_tmul']`. Conclude with `toFrac_smul_mem O F O' hi V _ x hx`.

Consider the case `zero => intro k`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro k`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ (hx k) (hy k)`.

Consider the case `smul a x _ hx => intro k`. Rewrite using `[smul_smul]`. Conclude with `hx _`. Simplify using `using this 1`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨x, hx, ?_⟩` and prove the remaining obligations. Simplify using `[toFrac_tmul]`.
-/
theorem span_frac_eq (hi : Function.Injective (algebraMap O O')) [Module.Finite O O']
    (V : Submodule (FractionRing O) F) :
    (Submodule.span (FractionRing O') ((fun x => (1 : FractionRing O') ⊗ₜ[O] x) '' (V : Set F))).restrictScalars O' =
      ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.restrictScalars_mem] at hy
    have : ∀ k : FractionRing O', k • y ∈ ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        intro k
        rw [TensorProduct.smul_tmul']
        exact toFrac_smul_mem O F O' hi V _ x hx
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact Submodule.add_mem _ (hx k) (hy k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx _
    simpa using this 1
  · rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨x, hx, ?_⟩
    simp [toFrac_tmul]

end Transport
section Objects

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eOp_eq : ToricLatticeDenominators.eOp Y i j b = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[ToricLatticeDenominators.typePart, Formalism.MainNotions.IntegralHeckeForms.Fm0, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem typePart_eq : ToricLatticeDenominators.typePart Y i j b = Formalism.MainNotions.IntegralHeckeForms.Fm0 Y i j b := by
  ext x
  simp [ToricLatticeDenominators.typePart, Formalism.MainNotions.IntegralHeckeForms.Fm0, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ToricLatticeDenominators.eOp, ← map_mul, Y.eAlg_idem]`.
-/
theorem eOp_idem (x : Y.Fm i j b) : ToricLatticeDenominators.eOp Y i j b (ToricLatticeDenominators.eOp Y i j b x) = ToricLatticeDenominators.eOp Y i j b x := by
  rw [← Module.End.mul_apply, ToricLatticeDenominators.eOp, ← map_mul, Y.eAlg_idem]

/- English proof (translation)
Establish `h` using `congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N) (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_central i b (MonoidAlgebra.of _ _ g))`. Rewrite `h` using `[map_mul, map_mul, MonoidAlgebra.lift_of]`. Conclude with `LinearMap.congr_fun h x`.
-/
theorem eOp_comm (g : G0g N) (x : Y.Fm i j b) :
    ToricLatticeDenominators.eOp Y i j b (Y.actG i j b g x) = Y.actG i j b g (ToricLatticeDenominators.eOp Y i j b x) := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i))
    (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)))
    (Y.eAlg_central i b (MonoidAlgebra.of _ _ g))
  rw [map_mul, map_mul, MonoidAlgebra.lift_of] at h
  exact LinearMap.congr_fun h x

/- English proof (translation)
Simplify using `[ToricLatticeDenominators.typePart, Submodule.mem_iInf]`.
-/
theorem mem_typePart (x : Y.Fm i j b) : x ∈ ToricLatticeDenominators.typePart Y i j b ↔
    ∀ u : Y.U, Y.actG i j b u x = ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  simp [ToricLatticeDenominators.typePart, Submodule.mem_iInf]

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.V0, ← typePart_eq, ← eOp_eq]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨⟨y, rfl⟩, hx⟩`. Conclude with `⟨_, hx, eOp_idem Y i j b y⟩`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `⟨⟨x, rfl⟩, (mem_typePart Y i j b _).2 fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← eOp_comm, (mem_typePart Y i j b x).1 hx u, map_smul]`.
-/
theorem jointSpan_eq : ToricLatticeDenominators.V0 Y i j b = Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b := by
  rw [Formalism.MainNotions.IntegralHeckeForms.V0, ← typePart_eq, ← eOp_eq]
  apply le_antisymm
  · rintro x ⟨⟨y, rfl⟩, hx⟩
    exact ⟨_, hx, eOp_idem Y i j b y⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, (mem_typePart Y i j b _).2 fun u => ?_⟩
    rw [← eOp_comm, (mem_typePart Y i j b x).1 hx u, map_smul]

end Objects

section PartB

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

def away (Q : Finset (PlE D.host)) : Set (Y.Dat i j b) := {d | Disjoint (Y.lev i j b d) Q}

section Ext

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem eExt_toFrac (y : O' ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.eExt Y i j b O' (toFrac _ _ O' y) =
      toFrac _ _ O' ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Conclude with `LinearMap.ext (eExt_toFrac Y i j b O')`.
-/
theorem map_eExt (L : Submodule O' (O' ⊗[X.O i] Y.Fm i j b)) :
    (L.map (toFrac _ _ O')).map (ToricLatticeDenominators.eExt Y i j b O') =
      (L.map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O')).map (toFrac _ _ O') := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (eExt_toFrac Y i j b O')

/- English proof (translation)
Establish `h1 : ToricLatticeDenominators.ThetaExt Y i j b O' = ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Set.univ).baseChange O').map (toFrac _ _ O')`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span, ToricLatticeDenominators.ThetaExt, Submodule.map_coe, Set.image_image, Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]`. Use `congr 1`. Conclude with `Set.image_congr fun x _ => by simp [toFrac_tmul]`. Rewrite using `[h1, map_eExt, Formalism.MainNotions.IntegralHeckeForms.eTh]`.

Use `congr 1`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Submodule.map_coe, Submodule.map_coe, Set.image_image, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem thetaExt_eq : (ToricLatticeDenominators.ThetaExt Y i j b O').map (ToricLatticeDenominators.eExt Y i j b O') =
    ((Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Set.univ).baseChange O').map (toFrac _ _ O') := by
  have h1 : ToricLatticeDenominators.ThetaExt Y i j b O' =
      ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Set.univ).baseChange O').map (toFrac _ _ O') := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, ToricLatticeDenominators.ThetaExt, Submodule.map_coe, Set.image_image,
      Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]
    congr 1
    exact Set.image_congr fun x _ => by simp [toFrac_tmul]
  rw [h1, map_eExt, Formalism.MainNotions.IntegralHeckeForms.eTh]
  congr 1
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Submodule.map_coe, Submodule.map_coe, Set.image_image, Set.image_image]
  rfl

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def up : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.Ok i k] O' ⊗[X.O i] Y.Fm i j b :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap (X.Ok i k) O') LinearMap.id

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem up_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) : up Y i j b O' k y =
    LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap y := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem incl_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.incl Y i j b O' k y = toFrac _ _ O' (up Y i j b O' k y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem up_e (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    up Y i j b O' k ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k) y) =
      (Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' (up Y i j b O' k y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def ext (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Submodule O' (O' ⊗[X.O i] Y.Fm i j b) :=
  Submodule.span O' (up Y i j b O' k '' L)

/- English proof (translation)
Rewrite using `[ext, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]`.
-/
theorem ext_span (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    ext Y i j b O' k (Submodule.span _ S) = Submodule.span O' (up Y i j b O' k '' S) := by
  rw [ext, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]

/- English proof (translation)
Establish `: Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S) = (Submodule.span O' (up Y i j b O' k '' S)).map (toFrac _ _ O')`. Rewrite using `[Submodule.map_span, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun x _ => incl_eq Y i j b O' k x`. Rewrite using `[this, map_eExt, Submodule.map_span, Submodule.map_span (R₂ := X.Ok i k), ext_span, Set.image_image, Set.image_image]`.

Use `congr 2`. Conclude with `Set.image_congr fun x _ => (up_e Y i j b O' k x).symm`.
-/
theorem span_incl_map (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    (Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S)).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k ((Submodule.span _ S).map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)))).map
        (toFrac _ _ O') := by
  have : Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S) =
      (Submodule.span O' (up Y i j b O' k '' S)).map (toFrac _ _ O') := by
    rw [Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => incl_eq Y i j b O' k x
  rw [this, map_eExt, Submodule.map_span, Submodule.map_span (R₂ := X.Ok i k), ext_span, Set.image_image,
    Set.image_image]
  congr 2
  exact Set.image_congr fun x _ => (up_e Y i j b O' k x).symm

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.eThPsi, Formalism.MainNotions.IntegralHeckeForms.ThPsi, ← span_incl_map, Set.image_iUnion₂]`. Both sides reduce to the same expression.
-/
theorem thetaPsi_eq (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) :
    (ToricLatticeDenominators.ThetaPsi Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ (away Y i j b Q))).map (toFrac _ _ O') := by
  rw [Formalism.MainNotions.IntegralHeckeForms.eThPsi, Formalism.MainNotions.IntegralHeckeForms.ThPsi, ← span_incl_map, Set.image_iUnion₂]
  rfl

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.eThPMt, ← Submodule.span_eq ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)), ← span_incl_map, Submodule.map_coe, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem thetaMt_eq (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) :
    (ToricLatticeDenominators.ThetaMt Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k (Formalism.MainNotions.IntegralHeckeForms.eThPMt Y i j b k Q ψ)).map (toFrac _ _ O') := by
  rw [Formalism.MainNotions.IntegralHeckeForms.eThPMt, ← Submodule.span_eq ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)),
    ← span_incl_map, Submodule.map_coe, Set.image_image]
  rfl

/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span, Submodule.map_coe, Submodule.map_coe, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun x _ => by simp [up]`.
-/
theorem ext_baseChange (V : Submodule (X.O i) (Y.Fm i j b)) :
    ext Y i j b O' k (V.baseChange (X.Ok i k)) = V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span, Submodule.map_coe,
    Submodule.map_coe, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => by simp [up]

/- English proof (translation)
Use `X.Ok_fin i k` as an intermediate fact. Establish `: Module.Finite (X.O i) O'` using `Module.Finite.trans (X.Ok i k) O'`. Establish `hi' : Function.Injective (algebraMap (X.O i) O')`. Rewrite using `[IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']`. Conclude with `hi.comp (X.Ok_inj i k)`.

Rewrite using `[isLatIn_iff, ToricLatticeDenominators.invariantSpanBaseChange, span_frac_eq _ _ _ hi', jointSpan_eq, isLatIn_map_iff _ (toFrac_injective _ _ _)]`.
-/
theorem isLatIn_toFrac (hi : Function.Injective (algebraMap (X.Ok i k) O')) [Module.Finite (X.Ok i k) O']
    (M : Submodule O' (O' ⊗[X.O i] Y.Fm i j b)) :
    ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O') (M.map (toFrac _ _ O')) ↔
      Formalism.MainNotions.IntegralHeckeForms.IsLatIn M (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange O') := by
  have := X.Ok_fin i k
  have : Module.Finite (X.O i) O' := Module.Finite.trans (X.Ok i k) O'
  have hi' : Function.Injective (algebraMap (X.O i) O') := by
    rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
    exact hi.comp (X.Ok_inj i k)
  rw [isLatIn_iff, ToricLatticeDenominators.invariantSpanBaseChange, span_frac_eq _ _ _ hi', jointSpan_eq,
    isLatIn_map_iff _ (toFrac_injective _ _ _)]

end Ext

/- English proof (translation)
Establish `: ∀ y, up Y i j b (X.Ok i k) k y = y`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[ext, Set.image_congr fun y _ => this y, Set.image_id', Submodule.span_eq]`.
-/
theorem ext_self (k : ℕ) (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    ext Y i j b (X.Ok i k) k L = L := by
  have : ∀ y, up Y i j b (X.Ok i k) k y = y := by
    intro y
    induction y with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [ext, Set.image_congr fun y _ => this y, Set.image_id', Submodule.span_eq]

/- English proof (translation)
Establish `hQ' : Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ Set.univ`. Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.eThPsi, hQ]`. Both sides reduce to the same expression. Establish `hup : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O'] [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O'] (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)), Submodule.span O' ((LinearMap.rTensor (Y.Fm i j b) (IsScalarT …`. Introduce `O' _ _ _ _ _ _ L`.

Rewrite using `[ext, Set.image_congr fun y _ => up_eq Y i j b O' k y]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun O' _ _ _ _ _ _ hi hf M hM => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, y, hx, hy, hxy⟩` from `(h O' hi).2.2 _ ((isLatIn_toFrac Y i j b O' k hi M).2 hM)`.

Rewrite `hxy` using `[eq_sIdx_of_isIdx hx, eq_sIdx_of_isIdx hy, thetaPsi_eq, thetaExt_eq, sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _), hQ']`. Rewrite using `[hup]`. Conclude with `hxy`. Establish `h1` using `(h (X.Ok i k) Function.injective_id).1`. Rewrite `h1` using `[thetaPsi_eq, isLatIn_toFrac Y i j b _ k Function.injective_id, ext_self, hQ']`. Then use the resulting hypothesis.

Establish `h1` using `(h (X.Ok i k) Function.injective_id).2.1`. Rewrite `h1` using `[thetaPsi_eq, thetaMt_eq, Submodule.map_le_map_iff_of_injective (toFrac_injective _ _ _), ext_self, ext_self, hQ']`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2, h3⟩ O' _ _ _ _ _ _ hf hi`. Use `X.Ok_fin i k` as an intermediate fact. Establish `: Module.Finite (X.O i) O'` using `Module.Finite.trans (X.Ok i k) O'`.

Establish `hi' : Function.Injective (algebraMap (X.O i) O')`. Rewrite using `[IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']`. Conclude with `hi.comp (X.Ok_inj i k)`. Establish `l1 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O') ((ToricLatticeDenominators.ThetaPsi Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O'))`. Rewrite using `[thetaPsi_eq, isLatIn_toFrac Y i j b O' k hi, hQ', ← ext_baseChange Y i j b O' k]`.

Conclude with `isLatIn_span hi _ h2`. Establish `l2 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O') ((ToricLatticeDenominators.ThetaExt Y i j b O').map (ToricLatticeDenominators.eExt Y i j b O'))`. Rewrite using `[thetaExt_eq, isLatIn_toFrac Y i j b O' k hi, Submodule.baseChange_eq_span, Submodule.baseChange_eq_span]`. Conclude with `isLatIn_span hi' _ hΘ`. Use `⟨l1, ?_, fun M hM => ⟨_, _, isIdx_sIdx _ hM l1, isIdx_sIdx _ hM l2, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[thetaPsi_eq, thetaMt_eq, hQ']`. Conclude with `Submodule.map_mono (Submodule.span_mono (Set.image_mono h3))`. Take `⟨M, rfl⟩ : ∃ M', M = Submodule.map (toFrac _ _ O') M'` from `⟨_, (Submodule.map_comap_eq_of_surjective (toFrac_surjective _ _ O' hi') M).symm⟩`. Use `h1 O' hi hf M ((isLatIn_toFrac Y i j b O' k hi M).1 hM)` as an intermediate fact. Rewrite using `[thetaPsi_eq, thetaExt_eq, sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _), hQ', ← hup]`.

Conclude with `this`.
-/
theorem partBAt_iff (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) (ε : ℝ)
    (hΘ : Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Set.univ)
      ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)))
    (hQ : Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ Set.univ) :
    ToricLatticeDenominators.partBAt Y i j b k Q ψ ε ↔
      Formalism.MainNotions.IntegralHeckeForms.IdxAt Y i j b Set.univ k Q ψ ε ∧
      Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ Set.univ)
        (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
      Formalism.MainNotions.IntegralHeckeForms.InclAt Y i j b Set.univ k Q ψ := by
  have hQ' : Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ Set.univ := by
    rw [Formalism.MainNotions.IntegralHeckeForms.eThPsi, hQ]; rfl
  have hup : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O'] [Algebra (X.Ok i k) O']
      [IsScalarTower (X.O i) (X.Ok i k) O'] (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)),
      Submodule.span O' ((LinearMap.rTensor (Y.Fm i j b)
        (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap) '' (L : Set _)) = ext Y i j b O' k L := by
    intro O' _ _ _ _ _ _ L
    rw [ext, Set.image_congr fun y _ => up_eq Y i j b O' k y]
  constructor
  · intro h
    refine ⟨fun O' _ _ _ _ _ _ hi hf M hM => ?_, ?_, ?_⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := (h O' hi).2.2 _ ((isLatIn_toFrac Y i j b O' k hi M).2 hM)
      rw [eq_sIdx_of_isIdx hx, eq_sIdx_of_isIdx hy, thetaPsi_eq, thetaExt_eq,
        sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _), hQ'] at hxy
      rw [hup]; exact hxy
    · have h1 := (h (X.Ok i k) Function.injective_id).1
      rwa [thetaPsi_eq, isLatIn_toFrac Y i j b _ k Function.injective_id, ext_self, hQ'] at h1
    · have h1 := (h (X.Ok i k) Function.injective_id).2.1
      rwa [thetaPsi_eq, thetaMt_eq, Submodule.map_le_map_iff_of_injective (toFrac_injective _ _ _),
        ext_self, ext_self, hQ'] at h1
  · rintro ⟨h1, h2, h3⟩ O' _ _ _ _ _ _ hf hi
    have := X.Ok_fin i k
    have : Module.Finite (X.O i) O' := Module.Finite.trans (X.Ok i k) O'
    have hi' : Function.Injective (algebraMap (X.O i) O') := by
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
      exact hi.comp (X.Ok_inj i k)
    have l1 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O')
        ((ToricLatticeDenominators.ThetaPsi Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O')) := by
      rw [thetaPsi_eq, isLatIn_toFrac Y i j b O' k hi, hQ', ← ext_baseChange Y i j b O' k]
      exact isLatIn_span hi _ h2
    have l2 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O')
        ((ToricLatticeDenominators.ThetaExt Y i j b O').map (ToricLatticeDenominators.eExt Y i j b O')) := by
      rw [thetaExt_eq, isLatIn_toFrac Y i j b O' k hi, Submodule.baseChange_eq_span,
        Submodule.baseChange_eq_span]
      exact isLatIn_span hi' _ hΘ
    refine ⟨l1, ?_, fun M hM => ⟨_, _, isIdx_sIdx _ hM l1, isIdx_sIdx _ hM l2, ?_⟩⟩
    · rw [thetaPsi_eq, thetaMt_eq, hQ']
      exact Submodule.map_mono (Submodule.span_mono (Set.image_mono h3))
    · obtain ⟨M, rfl⟩ : ∃ M', M = Submodule.map (toFrac _ _ O') M' :=
        ⟨_, (Submodule.map_comap_eq_of_surjective (toFrac_surjective _ _ O' hi') M).symm⟩
      have := h1 O' hi hf M ((isLatIn_toFrac Y i j b O' k hi M).1 hM)
      rw [thetaPsi_eq, thetaExt_eq, sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _),
        hQ', ← hup]
      exact this

end PartB

section Basis

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

/- English proof (translation)
Establish `: ∀ k, NeZero (D.host.g k)` using `fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Rewrite using `[N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))`. Rewrite using `[Finset.prod_const, Finset.card_univ, N.card_PlG k]`.
-/
theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

/- English proof (translation)
Simplify using `only [ToricLatticeDenominators.AOp, Formalism.MainNotions.IntegralHeckeForms.AO, LinearMap.smul_apply, card_eq (N := N), Nat.cast_smul_eq_nsmul]`. Both sides reduce to the same expression.
-/
theorem AOp_apply (x : Y.Fm i j b) : ToricLatticeDenominators.AOp Y i j b x = Formalism.MainNotions.IntegralHeckeForms.AO Y i j b x := by
  simp only [ToricLatticeDenominators.AOp, Formalism.MainNotions.IntegralHeckeForms.AO, LinearMap.smul_apply, card_eq (N := N), Nat.cast_smul_eq_nsmul]
  rfl

/- English proof (translation)
Rewrite using `[ToricLatticeDenominators.ATheta, Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]`. Use `congr 1`. Conclude with `LinearMap.ext (AOp_apply Y i j b)`.
-/
theorem ATheta_eq : ToricLatticeDenominators.ATheta Y i j b =
    (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Set.univ).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b) := by
  rw [ToricLatticeDenominators.ATheta, Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]
  congr 1
  exact LinearMap.ext (AOp_apply Y i j b)

/- English proof (translation)
Use `haveI : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective`. Use `haveI : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero`. Use `haveI : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)`. Conclude with `Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'`.
-/
theorem card_ne_zero : ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) ≠ 0 := by
  haveI : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  haveI : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  haveI : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  exact Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

/- English proof (translation)
Use `set n : X.O i := ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) with hn`. Establish `hn0 : algebraMap (X.O i) (FractionRing (X.O i)) n ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (card_ne_zero i)`. Establish `hinj : Function.Injective (n • LinearMap.id : Y.Fm i j b →ₗ[X.O i] Y.Fm i j b)`. Introduce `x y hxy`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at hxy`.

Rewrite `hxy` using `[← algebraMap_smul (FractionRing (X.O i)) n x, ← algebraMap_smul (FractionRing (X.O i)) n y]`. Conclude with `smul_right_injective _ hn0 hxy`. Establish `e1 : (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg).map (n • LinearMap.id) = (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b)`. Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.eTh, ← Submodule.map_comp]`. Both sides reduce to the same expression.

Establish `e2 : ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).map (n • LinearMap.id) = (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `Submodule.smul_mem _ n hx`. Introduce `x hx`.

Use `⟨(algebraMap (X.O i) (FractionRing (X.O i)) n)⁻¹ • x, Submodule.smul_mem (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) _ hx, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← algebraMap_smul (FractionRing (X.O i)) n, smul_inv_smul₀ hn0]`. Rewrite using `[← isLatIn_map_iff _ hinj, e1, e2, ← isLatIn_iff]`. Conclude with `h`.
-/
theorem eTh_isLatIn (Sg : Set (Y.Dat i j b))
    (h : ToricLatticeDenominators.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b))) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg) ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)) := by
  set n : X.O i := ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) with hn
  have hn0 : algebraMap (X.O i) (FractionRing (X.O i)) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (card_ne_zero i)
  have hinj : Function.Injective (n • LinearMap.id : Y.Fm i j b →ₗ[X.O i] Y.Fm i j b) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    rw [← algebraMap_smul (FractionRing (X.O i)) n x, ← algebraMap_smul (FractionRing (X.O i)) n y] at hxy
    exact smul_right_injective _ hn0 hxy
  have e1 : (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b) := by
    rw [Formalism.MainNotions.IntegralHeckeForms.eTh, ← Submodule.map_comp]; rfl
  have e2 : ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.smul_mem _ n hx
    · intro x hx
      refine ⟨(algebraMap (X.O i) (FractionRing (X.O i)) n)⁻¹ • x, Submodule.smul_mem (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) _ hx, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [← algebraMap_smul (FractionRing (X.O i)) n, smul_inv_smul₀ hn0]
  rw [← isLatIn_map_iff _ hinj, e1, e2, ← isLatIn_iff]
  exact h

variable (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)

/- English proof (translation)
Rewrite `h1`, `h2` using `[Formalism.MainNotions.IntegralHeckeForms.SgJ, hE]`. Establish `hr : (Set.range fun a : Fin S.card => ToricLatticeDenominators.AOp Y i j b (Y.th i j b (S.equivFin.symm a))) = (fun a => Formalism.MainNotions.IntegralHeckeForms.AO Y i j b (Y.th i j b a)) '' ↑S`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨_, (S.equivFin.symm a).2, (AOp_apply Y i j b _).symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨S.equivFin ⟨a, ha⟩, by simp [AOp_apply]⟩`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ATheta_eq, ← h2.2.2]`.

Conclude with `Submodule.fg_span (S.finite_toSet.image _)`. Rewrite using `[ATheta_eq, jointSpan_eq]`. Conclude with `h1.2.2`. Simplify using `only [AOp_apply]`. Conclude with `h2.2.1.comp _ S.equivFin.symm.injective`.

Rewrite using `[hr, ATheta_eq, h2.2.2]`.
-/
theorem isBasisSeries_of_basisOf (hE : E.Dat0 i j b = Set.univ) (S : Finset (Y.Dat i j b))
    (h1 : Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b))
    (h2 : Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) S) :
    ToricLatticeDenominators.IsBasisSeries Y i j b (fun a : Fin S.card => (S.equivFin.symm a : Y.Dat i j b)) := by
  rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE] at h1 h2
  have hr : (Set.range fun a : Fin S.card => ToricLatticeDenominators.AOp Y i j b (Y.th i j b (S.equivFin.symm a))) =
      (fun a => Formalism.MainNotions.IntegralHeckeForms.AO Y i j b (Y.th i j b a)) '' ↑S := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (S.equivFin.symm a).2, (AOp_apply Y i j b _).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨S.equivFin ⟨a, ha⟩, by simp [AOp_apply]⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ATheta_eq, ← h2.2.2]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [ATheta_eq, jointSpan_eq]; exact h1.2.2
  · simp only [AOp_apply]
    exact h2.2.1.comp _ S.equivFin.symm.injective
  · rw [hr, ATheta_eq, h2.2.2]

open Classical in

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.SgJ, hE]`. Take `⟨⟨-, h1⟩, h2, h3⟩` from `h`. Rewrite `h1` using `[ATheta_eq, jointSpan_eq]`. Rewrite `h3` using `[ATheta_eq]`. Simplify using `only [AOp_apply] at h2 h3`.

Use `⟨⟨by rw [hE], fun x hx => ?_, h1⟩, Set.subset_univ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`. Conclude with `Submodule.subset_span hx`. Establish `hc : ∀ a : ↥(Finset.univ.image d), ∃ t, d t = a` using `fun a => by`. Take `⟨t, -, ht⟩` from `Finset.mem_image.1 a.2`.

Conclude with `⟨t, ht⟩`. Use `choose t ht using hc`. Use `h2.comp t (fun a a' e => Subtype.ext (by rw [← ht a, ← ht a', e]))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`.

Simplify using `[ht]`. Rewrite using `[← h3, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem basisOf_of_isBasisSeries (hE : E.Dat0 i j b = Set.univ) {n : ℕ} (d : Fin n → Y.Dat i j b)
    (h : ToricLatticeDenominators.IsBasisSeries Y i j b d) :
    Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) ∧
      Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (Finset.univ.image d) := by
  rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE]
  obtain ⟨⟨-, h1⟩, h2, h3⟩ := h
  rw [ATheta_eq, jointSpan_eq] at h1
  rw [ATheta_eq] at h3
  simp only [AOp_apply] at h2 h3
  refine ⟨⟨by rw [hE], fun x hx => ?_, h1⟩, Set.subset_univ _, ?_, ?_⟩
  · rw [← h1]; exact Submodule.subset_span hx
  · have hc : ∀ a : ↥(Finset.univ.image d), ∃ t, d t = a := fun a => by
      obtain ⟨t, -, ht⟩ := Finset.mem_image.1 a.2
      exact ⟨t, ht⟩
    choose t ht using hc
    have := h2.comp t (fun a a' e => Subtype.ext (by rw [← ht a, ← ht a', e]))
    convert this using 1
    funext a
    simp [ht]
  · rw [← h3, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
    rfl

/- English proof (translation)
Rewrite using `[← h.1.2]`. Conclude with `Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, rfl⟩, rfl⟩`.
-/
theorem good_part_mem_basis_series {n : ℕ} (d : Fin n → Y.Dat i j b) (h : ToricLatticeDenominators.IsBasisSeries Y i j b d) (a : Y.Dat i j b) :
    ToricLatticeDenominators.AOp Y i j b (Y.th i j b a) ∈ ToricLatticeDenominators.V0 Y i j b := by
  rw [← h.1.2]
  exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

/- English proof (translation)
Establish `key : ∀ a, ToricLatticeDenominators.AOp Y i j b (Y.th i j b a) = 0`. Introduce `a`. Take `⟨a', ha'⟩` from `hg a`. Establish `h1` using `(mem_typePart Y i j b _).1 (good_part_mem_basis_series Y i j b d h a).2 u`. Establish `h2` using `(mem_typePart Y i j b _).1 (good_part_mem_basis_series Y i j b d h a').2 u'`.

Establish `h3 : ToricLatticeDenominators.AOp Y i j b (Y.th i j b a') = Y.actG i j b g (ToricLatticeDenominators.AOp Y i j b (Y.th i j b a))`. Rewrite using `[ha']`. Simplify using `only [ToricLatticeDenominators.AOp, LinearMap.smul_apply, eOp_comm, map_smul]`. Use `set x := ToricLatticeDenominators.AOp Y i j b (Y.th i j b a)`. Rewrite `h2` using `[h3, ← LinearEquiv.mul_apply, ← map_mul, hu, map_mul, LinearEquiv.mul_apply, h1, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]`.

Break down `h2 with h2 | h2` into its components or cases. Conclude with `absurd (Units.ext h2).symm hψ`. Conclude with `(Y.actG i j b g).map_eq_zero_iff.1 h2`. Rewrite using `[← h.1.2, ← h.2.2]`. Simplify using `[key]`.
-/
theorem good_part_bot_of_translate {n : ℕ} (d : Fin n → Y.Dat i j b) (h : ToricLatticeDenominators.IsBasisSeries Y i j b d)
    (g : G0g N) (hg : ∀ a, ∃ a', Y.th i j b a' = Y.actG i j b g (Y.th i j b a))
    (u u' : Y.U) (hu : (u' : G0g N) * g = g * u) (hψ : Y.psiU i b u' ≠ Y.psiU i b u) :
    ToricLatticeDenominators.V0 Y i j b = ⊥ := by
  have key : ∀ a, ToricLatticeDenominators.AOp Y i j b (Y.th i j b a) = 0 := by
    intro a
    obtain ⟨a', ha'⟩ := hg a
    have h1 := (mem_typePart Y i j b _).1 (good_part_mem_basis_series Y i j b d h a).2 u
    have h2 := (mem_typePart Y i j b _).1 (good_part_mem_basis_series Y i j b d h a').2 u'
    have h3 : ToricLatticeDenominators.AOp Y i j b (Y.th i j b a') = Y.actG i j b g (ToricLatticeDenominators.AOp Y i j b (Y.th i j b a)) := by
      rw [ha']; simp only [ToricLatticeDenominators.AOp, LinearMap.smul_apply, eOp_comm, map_smul]
    set x := ToricLatticeDenominators.AOp Y i j b (Y.th i j b a)
    rw [h3, ← LinearEquiv.mul_apply, ← map_mul, hu, map_mul, LinearEquiv.mul_apply, h1, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (Units.ext h2).symm hψ
    · exact (Y.actG i j b g).map_eq_zero_iff.1 h2
  rw [← h.1.2, ← h.2.2]
  simp [key]

/- English proof (translation)
Establish `: ToricLatticeDenominators.ATheta Y i j b = ⊥`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal (X.O i)) _ h.1.1 ?_ (IsLocalRing.maximalIdeal_le_jacobson _)` and prove the remaining obligations. Rewrite using `[ToricLatticeDenominators.ATheta, ToricLatticeDenominators.Theta, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, rfl⟩`. Take `⟨a', ha'⟩` from `hd a`.

Rewrite using `[← ha', map_smul]`. Conclude with `Submodule.smul_mem_smul hc (Submodule.subset_span ⟨_, ⟨a', rfl⟩, rfl⟩)`. Rewrite using `[← h.1.2, this]`. Simplify using the standard rewrite rules.
-/
theorem good_part_bot_of_divisible {n : ℕ} (d : Fin n → Y.Dat i j b) (h : ToricLatticeDenominators.IsBasisSeries Y i j b d)
    (c : X.O i) (hc : c ∈ IsLocalRing.maximalIdeal (X.O i))
    (hd : ∀ a, ∃ a', c • Y.th i j b a' = Y.th i j b a) : ToricLatticeDenominators.V0 Y i j b = ⊥ := by
  have : ToricLatticeDenominators.ATheta Y i j b = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal (X.O i)) _ h.1.1 ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [ToricLatticeDenominators.ATheta, ToricLatticeDenominators.Theta, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨a', ha'⟩ := hd a
    rw [← ha', map_smul]
    exact Submodule.smul_mem_smul hc (Submodule.subset_span ⟨_, ⟨a', rfl⟩, rfl⟩)
  rw [← h.1.2, this]
  simp

end Basis

section Main

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X)

/- English proof (translation)
Take `⟨e, h0, h1, h2⟩` from `h`. Establish `hi : (0 : ℝ) ≤ (nu X i : ℝ)` using `Nat.cast_nonneg _`. Use `(Finset.sum_le_sum fun s hs => h2 s ((mem_SigG bkP i s).1 hs)).trans ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg fun s _ => add_nonneg hi (h0 s)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem partA_of_partAT {i : X.Tw} {Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} {eps' : ℝ}
    (h : partAT bkP i Q k' ψ' eps') : partA bkP i Q k' ψ' eps' := by
  obtain ⟨e, h0, h1, h2⟩ := h
  have hi : (0 : ℝ) ≤ (nu X i : ℝ) := Nat.cast_nonneg _
  refine (Finset.sum_le_sum fun s hs => h2 s ((mem_SigG bkP i s).1 hs)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => add_nonneg hi (h0 s)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)

open Classical in

def GoodAll (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b))
    (A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  PsiOk i (Formalism.MainNotions.IntegralHeckeForms.levs Y i S ∪ A) Q k' ψ' ∧ ToricLatticeDenominators.ThroughDel Y i k' Q (ψ'.comp (X.art i Q)) ∧
    ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧ ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
        (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
          Formalism.MainNotions.IntegralHeckeForms.IdxAt Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (epsB j b) ∧
          Formalism.MainNotions.IntegralHeckeForms.IsLatIn
            (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b))
            (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k')) ∧
          Formalism.MainNotions.IntegralHeckeForms.InclAt Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q)))) ∧
        partAT bkP i Q k' (ψ' ^ a) eps' ∧ partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps'

def exportAll (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), GoodAll bkP Y E N0 i eps' S A Q k' ψ'

def RankAt (i : X.Tw) : Prop :=
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) ∧
      Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (S j b)

/- English proof (translation)
Take `⟨h1, -, e, h0, hs, h⟩` from `h`. Establish `h` using `h 1 isCoprime_one_left`. Rewrite `h` using `[zpow_one]`. Conclude with `⟨h1, ⟨e, h0, hs, fun j hj b => (h.1 j hj b).1⟩, fun j hj b => (h.1 j hj b).2, h.2⟩`.
-/
theorem goodTw_of_goodAll {N0 : X.Tw → ℕ} {i : X.Tw} {eps' : ℝ} {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)}
    {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}
    (h : GoodAll bkP Y E N0 i eps' S A Q k' ψ') : Formalism.MainNotions.IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' ψ' := by
  obtain ⟨h1, -, e, h0, hs, h⟩ := h
  have h := h 1 isCoprime_one_left
  rw [zpow_one] at h
  exact ⟨h1, ⟨e, h0, hs, fun j hj b => (h.1 j hj b).1⟩, fun j hj b => (h.1 j hj b).2, h.2⟩

/- English proof (translation)
Introduce `hs eps' he hr S hS A`. Take `⟨Q, k', ψ', h⟩` from `h hs eps' he hr S hS A`. Conclude with `⟨Q, k', ψ', goodTw_of_goodAll bkP Y E h⟩`.
-/
theorem first_typing_of_export_all (N0 : X.Tw → ℕ) (i : X.Tw) (h : exportAll bkP Y E N0 i) :
    Formalism.MainNotions.IntegralHeckeForms.TwistTheoremAtIndex Y bkP E N0 i := by
  intro hs eps' he hr S hS A
  obtain ⟨Q, k', ψ', h⟩ := h hs eps' he hr S hS A
  exact ⟨Q, k', ψ', goodTw_of_goodAll bkP Y E h⟩

open Classical in
/- English proof (translation)
Simplify using `only [PsiOk, Finset.disjoint_union_right, disjoint_comm (a := B)]`. The claim follows by propositional logic.
-/
theorem psiOk_union_iff {i : X.Tw} (B A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) :
    PsiOk i (B ∪ A) Q k' ψ' ↔ PsiOk i A Q k' ψ' ∧ Disjoint B Q := by
  simp only [PsiOk, Finset.disjoint_union_right, disjoint_comm (a := B)]
  tauto

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.IntegralHeckeForms.levs, Finset.disjoint_biUnion_left, Finset.mem_univ, true_imp_iff]`.
-/
theorem disjoint_levs_iff (i : X.Tw) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (Q : Finset (PlE D.host)) :
    Disjoint (Formalism.MainNotions.IntegralHeckeForms.levs Y i S) Q ↔
      ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ∀ a ∈ S j b, Disjoint (Y.lev i j b a) Q := by
  simp only [Formalism.MainNotions.IntegralHeckeForms.levs, Finset.disjoint_biUnion_left, Finset.mem_univ, true_imp_iff]

def AwaySpans (i : X.Tw) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ),
    (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) →
    Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ Set.univ

open Classical in

/- English proof (translation)
Establish `key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ {n : ℕ} (d : Fin n → bkP.ex.Dat i j b), ToricLatticeDenominators.IsBasisSeries bkP.ex i j b d → ∀ {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}, PsiOk i A Q k' ψ' → ∀ (ψ : GE N →* (X.Ok i k')ˣ) (ε : ℝ), (ToricLatticeD …`. Introduce `j hj b n d hd A Q k' ψ' hψ ψ ε`. Rewrite using `[Formalism.MainNotions.IntegralHeckeForms.SgJ, hE j hj b]`. Use `partBAt_iff _ i j b k' Q ψ ε (eTh_isLatIn _ i j b _ ?_) (hQ j hj b k' Q ψ (fun P hP => (hψ.1 P hP).1) (Finset.disjoint_union_right.1 hψ.2.1).1)` and prove the remaining obligations. Rewrite using `[← ATheta_eq, ← jointSpan_eq]`.

Conclude with `hd.1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun hs => ?_, fun hs eps' he _ S _ A => ?_⟩` and prove the remaining obligations. Take `⟨n, d, hd, -⟩` from `h hs`.

Conclude with `⟨fun j b => Finset.univ.image (d j b), fun j hj b => basisOf_of_isBasisSeries _ i j b E (hE j hj b) _ (hd j hj b)⟩`. Take `⟨n, d, hd, H⟩` from `h hs`. Take `⟨Q, k', ψ', e, h1, -, h2, h3, h4, h5⟩` from `H eps' he (Formalism.MainNotions.IntegralHeckeForms.levs bkP.ex i S ∪ A)`. Use `⟨Q, k', ψ', h1, h2, e, h3, h4, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨-, g2, g3, g4⟩` from `h5 a ha`.

Conclude with `⟨fun j hj b => (key j hj b _ (hd j hj b) h1 _ _).1 (g3 j hj b), g2, g4⟩`. Introduce and unpack `⟨h1, h2⟩ hs`. Take `⟨S, hS⟩` from `h1 hs`. Establish `hd` using `fun j hj b => isBasisSeries_of_basisOf _ i j b E (hE j hj b) (S j b) (hS j hj b).1 (hS j hj b).2`. Use `⟨fun j b => (S j b).card, fun j b a => (S j b).equivFin.symm a, hd, fun eps' he A => ?_⟩` and prove the remaining obligations.

Take `⟨Q, k', ψ', g1, g2, e, g3, g4, g5⟩` from `h2 hs eps' he (fun j hj b => (hS j hj b).1) S (fun j hj b => (hS j hj b).2) A`. Take `⟨g0, g1'⟩` from `(psiOk_union_iff _ _ _ _ _).1 g1`. Use `⟨Q, k', ψ', e, g0, fun j hj b a => (disjoint_levs_iff _ i S Q).1 g1' j hj b _ ((S j b).equivFin.symm a).2, g2, g3, g4, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨f1, f2, f3⟩` from `g5 a ha`. Conclude with `⟨partA_of_partAT bkP f2, f2, fun j hj b => (key j hj b _ (hd j hj b) g0 _ _).2 (f1 j hj b), f3⟩`.
-/
theorem exportAt_iff (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat bkP.ex) (N0 : X.Tw → ℕ) (i : X.Tw)
    (hE : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = Set.univ) (hQ : AwaySpans bkP.ex i) :
    ToricLatticeDenominators.exportAt bkP N0 i ↔ (SetHyp bkP i → RankAt bkP.ex E i) ∧ exportAll bkP bkP.ex E N0 i := by
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ {n : ℕ} (d : Fin n → bkP.ex.Dat i j b),
      ToricLatticeDenominators.IsBasisSeries bkP.ex i j b d → ∀ {A Q : Finset (PlE D.host)} {k' : ℕ}
      {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}, PsiOk i A Q k' ψ' → ∀ (ψ : GE N →* (X.Ok i k')ˣ) (ε : ℝ),
      (ToricLatticeDenominators.partBAt bkP.ex i j b k' Q ψ ε ↔
        Formalism.MainNotions.IntegralHeckeForms.IdxAt bkP.ex i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b) k' Q ψ ε ∧
        Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eThPsi bkP.ex i j b k' Q ψ (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b))
          (((Formalism.MainNotions.IntegralHeckeForms.V0 bkP.ex i j b).restrictScalars (X.O i)).baseChange (X.Ok i k')) ∧
        Formalism.MainNotions.IntegralHeckeForms.InclAt bkP.ex i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b) k' Q ψ) := by
    intro j hj b n d hd A Q k' ψ' hψ ψ ε
    rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE j hj b]
    refine partBAt_iff _ i j b k' Q ψ ε (eTh_isLatIn _ i j b _ ?_)
      (hQ j hj b k' Q ψ (fun P hP => (hψ.1 P hP).1) (Finset.disjoint_union_right.1 hψ.2.1).1)
    rw [← ATheta_eq, ← jointSpan_eq]; exact hd.1
  constructor
  · intro h
    refine ⟨fun hs => ?_, fun hs eps' he _ S _ A => ?_⟩
    · obtain ⟨n, d, hd, -⟩ := h hs
      exact ⟨fun j b => Finset.univ.image (d j b), fun j hj b =>
        basisOf_of_isBasisSeries _ i j b E (hE j hj b) _ (hd j hj b)⟩
    · obtain ⟨n, d, hd, H⟩ := h hs
      obtain ⟨Q, k', ψ', e, h1, -, h2, h3, h4, h5⟩ := H eps' he (Formalism.MainNotions.IntegralHeckeForms.levs bkP.ex i S ∪ A)
      refine ⟨Q, k', ψ', h1, h2, e, h3, h4, fun a ha => ?_⟩
      obtain ⟨-, g2, g3, g4⟩ := h5 a ha
      exact ⟨fun j hj b => (key j hj b _ (hd j hj b) h1 _ _).1 (g3 j hj b), g2, g4⟩
  · rintro ⟨h1, h2⟩ hs
    obtain ⟨S, hS⟩ := h1 hs
    have hd := fun j hj b => isBasisSeries_of_basisOf _ i j b E (hE j hj b) (S j b) (hS j hj b).1 (hS j hj b).2
    refine ⟨fun j b => (S j b).card, fun j b a => (S j b).equivFin.symm a, hd, fun eps' he A => ?_⟩
    obtain ⟨Q, k', ψ', g1, g2, e, g3, g4, g5⟩ :=
      h2 hs eps' he (fun j hj b => (hS j hj b).1) S (fun j hj b => (hS j hj b).2) A
    obtain ⟨g0, g1'⟩ := (psiOk_union_iff _ _ _ _ _).1 g1
    refine ⟨Q, k', ψ', e, g0, fun j hj b a => (disjoint_levs_iff _ i S Q).1 g1' j hj b _
      ((S j b).equivFin.symm a).2, g2, g3, g4, fun a ha => ?_⟩
    obtain ⟨f1, f2, f3⟩ := g5 a ha
    exact ⟨partA_of_partAT bkP f2, f2, fun j hj b => (key j hj b _ (hd j hj b) g0 _ _).2 (f1 j hj b), f3⟩

end Main

def ExportAllConjugates (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → exportAll (Formalism.MainNotions.BlochKatoReduction.pin bkP) D.nexp E N0 i

/- English proof (translation)
Introduce `i hi` and use `first_typing_of_export_all _ _ _ N0 i (h i hi)`.
-/
theorem export_of_all_conjugates {D : Formalism.BasicNotions.D7} {bkP : Formalism.MainNotions.BlochKatoReduction.BK D} {E : Formalism.MainNotions.IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ}
    (h : ExportAllConjugates D bkP E N0) : Formalism.MainNotions.IntegralHeckeForms.aux₃ D bkP E N0 :=
  fun i hi => first_typing_of_export_all _ _ _ N0 i (h i hi)

/- English proof (translation)
Establish `h : ToricLatticeDenominators.aux₃ D bkP N0 ↔ (∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → RankAt D.nexp E i) ∧ ExportAllConjugates D bkP E N0`. Use `fun i hi => exportAt_iff (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i (hE i hi) (hQ i hi)` as an intermediate fact. Conclude with `⟨fun h => ⟨fun i hi => ((this i hi).1 (h i hi)).1, fun i hi => ((this i hi).1 (h i hi)).2⟩, fun h i hi => (this i hi).2 ⟨h.1 i hi, h.2 i hi⟩⟩`. Conclude with `⟨h, fun h' => export_of_all_conjugates (h.1 h').2⟩`.
-/
theorem compare (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ)
    (hE : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = Set.univ)
    (hQ : ∀ i, D.ntw.NonzeroIndexPlace i → AwaySpans D.nexp i) :
    (ToricLatticeDenominators.aux₃ D bkP N0 ↔
      (∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → RankAt D.nexp E i) ∧ ExportAllConjugates D bkP E N0) ∧
    (ToricLatticeDenominators.aux₃ D bkP N0 → Formalism.MainNotions.IntegralHeckeForms.aux₃ D bkP E N0) := by
  have h : ToricLatticeDenominators.aux₃ D bkP N0 ↔
      (∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → RankAt D.nexp E i) ∧ ExportAllConjugates D bkP E N0 := by
    have := fun i hi => exportAt_iff (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i (hE i hi) (hQ i hi)
    exact ⟨fun h => ⟨fun i hi => ((this i hi).1 (h i hi)).1, fun i hi => ((this i hi).1 (h i hi)).2⟩,
      fun h i hi => (this i hi).2 ⟨h.1 i hi, h.2 i hi⟩⟩
  exact ⟨h, fun h' => export_of_all_conjugates (h.1 h').2⟩

end GlobalTheory.ExportCompare

end
