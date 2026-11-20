import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatFreeHolds

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def UnitElt : Prop :=
  ∃ a : 𝓞 X.B.I.E, ∃ w ∈ OpX X p, w * (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1

/- English proof (translation)
Use `show (θ (c • t)).1 = c * (θ t).1`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.
-/
theorem firstSplitCoord_smul (c : FpX X p) (t : TpX X p) : th1 X p θ (c • t) = c * th1 X p θ t := by
  show (θ (c • t)).1 = c * (θ t).1
  rw [map_smul]
  rfl

/- English proof (translation)
Use `show (θ (c • t)).2 = c * (θ t).2`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.
-/
theorem secondSplitCoord_smul (c : FpX X p) (t : TpX X p) : th2 X p θ (c • t) = c * th2 X p θ t := by
  show (θ (c • t)).2 = c * (θ t).2
  rw [map_smul]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem osmul_eq (c : OpX X p) (t : TpX X p) : c • t = (c : FpX X p) • t := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem th_incl (e : X.B.I.E) : θ (inclR (FpX X p) e) = (iota1 X p θ e, iota2 X p θ e) := rfl

/- English proof (translation)
Take `⟨a, w, hw, hwa⟩` from `h`. Establish `hc2 : iota2 X p θ (a : X.B.I.E) ∈ OpX X p` using `MassDataIdxLatFree.int_mem (OpX X p) (iota2 X p θ) a`. Establish `heq : (fun j => θ.symm (iota1 X p θ (l j), 0)) = (⟨w, hw⟩ : OpX X p) • (ratV (F` using `X.B.I.F) (FpX X p) (a • l) - (⟨iota2 X p θ (a : X.B.I.E), hc2⟩ : OpX X p) • ratV (F := X.B.I.F) (FpX X p) l) := by`. Use function extensionality and compare the values at `j`. Apply `θ.injective` to reduce the goal to its premises.

Rewrite using `[AlgEquiv.apply_symm_apply]`. Use `show _ = θ ((w : FpX X p) • (inclR (FpX X p) ((a : X.B.I.E) * l j) - (iota2 X p θ (a : X.B.I.E)) • inclR (FpX X p) (l j)))`. Rewrite using `[map_smul, map_sub, map_smul, map_mul, map_mul]`. Simplify using `only [th_incl]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use `show iota1 X p θ (l j) = w * (iota1 X p θ (a : X.B.I.E) * iota1 X p θ (l j) - iota2 X p θ (a : X.B.I.E) * iota1 X p θ (l j))`. Take the linear combination `(-(iota1 X p θ (l j))) * hwa`. Use `show (0 : FpX X p) = w * (iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j) - iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`.

Use `Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨a • l, X.B.I.L.smul_mem a hl, rfl⟩`. Conclude with `Submodule.subset_span ⟨l, hl, rfl⟩`.
-/
theorem first_raising_mem_equivariant (h : UnitElt X p θ) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    (fun j => θ.symm (iota1 X p θ (l j), 0)) ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  obtain ⟨a, w, hw, hwa⟩ := h
  have hc2 : iota2 X p θ (a : X.B.I.E) ∈ OpX X p := MassDataIdxLatFree.int_mem (OpX X p) (iota2 X p θ) a
  have heq : (fun j => θ.symm (iota1 X p θ (l j), 0)) =
      (⟨w, hw⟩ : OpX X p) • (ratV (F := X.B.I.F) (FpX X p) (a • l) -
        (⟨iota2 X p θ (a : X.B.I.E), hc2⟩ : OpX X p) • ratV (F := X.B.I.F) (FpX X p) l) := by
    funext j
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = θ ((w : FpX X p) • (inclR (FpX X p) ((a : X.B.I.E) * l j) -
      (iota2 X p θ (a : X.B.I.E)) • inclR (FpX X p) (l j)))
    rw [map_smul, map_sub, map_smul, map_mul, map_mul]
    simp only [th_incl]
    refine Prod.ext ?_ ?_
    · show iota1 X p θ (l j) = w * (iota1 X p θ (a : X.B.I.E) * iota1 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota1 X p θ (l j))
      linear_combination (-(iota1 X p θ (l j))) * hwa
    · show (0 : FpX X p) = w * (iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j))
      ring
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span ⟨a • l, X.B.I.L.smul_mem a hl, rfl⟩
  · exact Submodule.subset_span ⟨l, hl, rfl⟩

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Conclude with `first_raising_mem_equivariant X p θ h l hl`. Consider the case `zero`.

Use `Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Consider the case `add y y' _ _ hy hy'`. Use `Submodule.add_mem _ hy hy' using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply]`. Rewrite using `[← map_add, Prod.mk_add_mk, add_zero]`. Consider the case `smul c y _ hy`. Use `Submodule.smul_mem _ c hy using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[osmul_eq X p, ← map_smul, Prod.smul_mk, smul_zero]`. Both sides reduce to the same expression.
-/
theorem firstLattice_mem_local (h : UnitElt X p θ) (y : Fin X.B.I.n → FpX X p) (hy : y ∈ Mlat1 X p θ) :
    (fun j => θ.symm (y j, 0)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact first_raising_mem_equivariant X p θ h l hl
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1
    funext j
    simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, add_zero]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply]
    rw [osmul_eq X p, ← map_smul, Prod.smul_mk, smul_zero]
    rfl

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨l, hl, rfl⟩` from `hz`. Establish `h1` using `first_raising_mem_equivariant X p θ h l hl`. Establish `h2 : ratV (F` using `X.B.I.F) (FpX X p) l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := Submodule.subset_span ⟨l, hl, rfl⟩`.

Use `Submodule.sub_mem _ h2 h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.sub_apply, ratV]`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, th_incl]`.

Apply the tactic sequence `ext <;> simp`. Consider the case `zero`. Use `Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Consider the case `add y y' _ _ hy hy'`. Use `Submodule.add_mem _ hy hy' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply]`. Rewrite using `[← map_add, Prod.mk_add_mk, zero_add]`.

Consider the case `smul c y _ hy`. Use `Submodule.smul_mem _ c hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[osmul_eq X p, ← map_smul, Prod.smul_mk, smul_zero]`.

Both sides reduce to the same expression.
-/
theorem secondLattice_mem_local (h : UnitElt X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    (fun j => θ.symm (0, z j)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have h1 := first_raising_mem_equivariant X p θ h l hl
    have h2 : ratV (F := X.B.I.F) (FpX X p) l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    convert Submodule.sub_mem _ h2 h1 using 1
    funext j
    simp only [Pi.sub_apply, ratV]
    apply θ.injective
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, th_incl]
    ext <;> simp
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1
    funext j
    simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, zero_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply]
    rw [osmul_eq X p, ← map_smul, Prod.smul_mk, smul_zero]
    rfl

/- English proof (translation)
Unfold `LatSplitP`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Conclude with `⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩`. Consider the case `zero`. Simplify using `only [Pi.zero_apply, map_zero]`.

Conclude with `⟨Submodule.zero_mem _, Submodule.zero_mem _⟩`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Pi.add_apply, map_add]`. Conclude with `⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩`. Consider the case `smul c x _ hx`.

Simplify using `only [Pi.smul_apply, osmul_eq X p, firstSplitCoord_smul, secondSplitCoord_smul]`. Conclude with `⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `hx : x = (fun j => θ.symm (th1 X p θ (x j), 0)) + (fun j => θ.symm (0, th2 X p θ (x j)))`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.add_apply]`. Rewrite using `[← map_add, Prod.mk_add_mk, add_zero, zero_add]`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[hx]`. Conclude with `Submodule.add_mem _ (firstLattice_mem_local X p θ h _ h1) (secondLattice_mem_local X p θ h _ h2)`.
-/
theorem latSplit_of (h : UnitElt X p θ) : LatSplitP X p θ := by
  unfold LatSplitP
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add]
      exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul c x _ hx =>
      simp only [Pi.smul_apply, osmul_eq X p, firstSplitCoord_smul, secondSplitCoord_smul]
      exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
  · rintro ⟨h1, h2⟩
    have hx : x = (fun j => θ.symm (th1 X p θ (x j), 0)) + (fun j => θ.symm (0, th2 X p θ (x j))) := by
      funext j
      simp only [Pi.add_apply]
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      apply θ.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [hx]
    exact Submodule.add_mem _ (firstLattice_mem_local X p θ h _ h1) (secondLattice_mem_local X p θ h _ h2)

end Loc

end MassDataIdxSteps
