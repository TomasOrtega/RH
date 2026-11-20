import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.MemDualLat
import ReciprocityTheory.DualLattices.MemSupOfRestrictToSubgroupMemSq
import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfProdEq

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

open scoped TensorProduct Kronecker

/- English proof (translation)
Rewrite using `[← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem tmul_move {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (a : A) (y : B) :
    algebraMap A B a ⊗ₜ[A] y = (1 : B) ⊗ₜ[A] (algebraMap A B a * y) := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {Q : Type} [AddCommGroup Q] [Fintype Q] [DecidableEq Q]

def subalg (A : HopfOrder (C := C) R Q) : Subalgebra R (Q → C) :=
  A.carrier.toSubalgebra A.one_mem A.mul_mem

noncomputable def ev (A : HopfOrder (C := C) R Q) : subalg A ⊗[R] subalg A →ₐ[R] (Q × Q → C) :=
  Algebra.TensorProduct.lift
    ((AlgHom.pi fun p : Q × Q => Pi.evalAlgHom R (fun _ : Q => C) p.1).comp
      (subalg A).val)
    ((AlgHom.pi fun p : Q × Q => Pi.evalAlgHom R (fun _ : Q => C) p.2).comp
      (subalg A).val)
    fun _ _ => Commute.all _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_tmul (A : HopfOrder (C := C) R Q) (g h : subalg A) :
    ev A (g ⊗ₜ h) = fun p => g.1 p.1 * h.1 p.2 := rfl

/- English proof (translation)
Take `⟨β, hβ, hA⟩` from `A.lat`. Set `w : Q → subalg A` to `fun j => ⟨fun x => β x j, by`. Express the relevant statement in the definitionally equal form `_ ∈ A.carrier`. Rewrite using `[hA]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩⟩`.

Establish `hw : Submodule.span R (Set.range w) = ⊤`. Apply `Submodule.map_injective_of_injective (f := (subalg A).val.toLinearMap) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, ← Set.range_comp, Submodule.map_top]`. Use `Eq.trans hA.symm ?_` and prove the remaining obligations. Use extensionality with `f`.

Conclude with `⟨fun hf => ⟨⟨f, hf⟩, rfl⟩, by rintro ⟨g, rfl⟩; exact g.2⟩`. Establish `hsp : Submodule.span R (Set.range fun p : Q × Q => w p.1 ⊗ₜ[R] w p.2) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `t ht`. Use `clear ht`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `tmul a b`. Establish `ha : a ∈ Submodule.span R (Set.range w)` using `hw ▸ Submodule.mem_top`.

Establish `hb : b ∈ Submodule.span R (Set.range w)` using `hw ▸ Submodule.mem_top`. Take `⟨r, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 ha`. Take `⟨s, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hb`. Rewrite using `[TensorProduct.sum_tmul]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩))`. Use `LinearMap.injective_of_linearIndependent (f := (ev A).toLinearMap) hsp ?_` and prove the remaining obligations.

Establish `hu : IsUnit (β ⊗ₖ β)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker]`. Conclude with `(hβ.pow _).mul (hβ.pow _)`. Establish `hli` using `Matrix.linearIndependent_cols_iff_isUnit.2 hu`. Establish `: FaithfulSMul R C` using `(faithfulSMul_iff_algebraMap_injective R C).2 hinj`.

Conclude with `hli.restrict_scalars' R`.
-/
theorem ev_injective (hinj : Function.Injective (algebraMap R C)) (A : HopfOrder (C := C) R Q) :
    Function.Injective (ev A) := by
  obtain ⟨β, hβ, hA⟩ := A.lat
  let w : Q → subalg A := fun j => ⟨fun x => β x j, by
    change _ ∈ A.carrier
    rw [hA]
    exact Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : Submodule.span R (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := (subalg A).val.toLinearMap) Subtype.val_injective
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top]
    refine Eq.trans hA.symm ?_
    ext f
    exact ⟨fun hf => ⟨⟨f, hf⟩, rfl⟩, by rintro ⟨g, rfl⟩; exact g.2⟩
  have hsp : Submodule.span R (Set.range fun p : Q × Q => w p.1 ⊗ₜ[R] w p.2) = ⊤ := by
    rw [eq_top_iff]
    intro t ht
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul a b =>
      have ha : a ∈ Submodule.span R (Set.range w) := hw ▸ Submodule.mem_top
      have hb : b ∈ Submodule.span R (Set.range w) := hw ▸ Submodule.mem_top
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hb
      rw [TensorProduct.sum_tmul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩))
  refine LinearMap.injective_of_linearIndependent (f := (ev A).toLinearMap) hsp ?_
  have hu : IsUnit (β ⊗ₖ β) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker]
    exact (hβ.pow _).mul (hβ.pow _)
  have hli := Matrix.linearIndependent_cols_iff_isUnit.2 hu
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hinj
  exact hli.restrict_scalars' R

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨g, hg, h, hh, rfl⟩` from `hF`. Conclude with `⟨(⟨g, hg⟩ : subalg A) ⊗ₜ (⟨_, A.antipode h hh⟩ : subalg A), rfl⟩`. Consider the case `zero => exact Subalgebra.zero_mem _`.

Consider the case `add F G _ _ hF hG => exact Subalgebra.add_mem _ hF hG`. Consider the case `smul c F _ hF => exact Subalgebra.smul_mem _ hF c`.
-/
theorem tensorSpan_le (A : HopfOrder (C := C) R Q) {F : Q × Q → C} (hF : F ∈ tensorSpan R A.carrier) :
    (fun p : Q × Q => F (p.1, -p.2)) ∈ (ev A).range := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨g, hg, h, hh, rfl⟩ := hF
    exact ⟨(⟨g, hg⟩ : subalg A) ⊗ₜ (⟨_, A.antipode h hh⟩ : subalg A), rfl⟩
  | zero => exact Subalgebra.zero_mem _
  | add F G _ _ hF hG => exact Subalgebra.add_mem _ hF hG
  | smul c F _ hF => exact Subalgebra.smul_mem _ hF c

/- English proof (translation)
Set `B' : Subalgebra R (subalg A)` to `((subalg A').map (AlgHom.pi fun x : Q => Pi.evalAlgHom R (fun _ : N' => C) (i x))).comap (subalg A).val`. Establish `: Module.Finite R (subalg A)` using `Module.Finite.iff_fg.2 (SecondCohomologyLattice.fg_of_isLat A.lat)`. Establish `: Module.Finite B' (subalg A)` using `Module.Finite.of_restrictScalars_finite R _ _`. Set `π : subalg A ⊗[R] subalg A →ₐ[R] subalg A ⊗[B'] subalg A` to `Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft) (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ => Commute.all _ _`. Establish `hπ : ∀ a b : subalg A, π (a ⊗ₜ b) = a ⊗ₜ b`.

Introduce `a b`. Simplify using `[π]`. Set `S : Submodule R (Q × Q → C)` to `(LinearMap.ker π.toLinearMap).map (ev A).toLinearMap`. Establish `hS : ∀ F ∈ S, ∀ G ∈ (ev A).range, F * G ∈ S`. Introduce and unpack `_ ⟨t, ht, rfl⟩ _ ⟨u, rfl⟩`.

Use `⟨t * u, ?_, map_mul (ev A) t u⟩` and prove the remaining obligations. Establish `ht' : π t = 0` using `ht`. Express the relevant statement in the definitionally equal form `π (t * u) = 0`. Rewrite using `[map_mul, ht', zero_mul]`. Establish `hA : ∀ c ∈ A.carrier, (fun p : Q × Q => c (p.1 - p.2)) ∈ (ev A).range`.

Introduce `c hc`. Use `tensorSpan_le A (A.comul c hc)` as an intermediate fact. Simplify using `only [sub_eq_add_neg]`. Conclude with `this`. Establish `hB0 : ∀ F ∈ tensorSpan R A'.carrier, (fun p : Q × Q => F (i p.1, -i p.2) - F (i p.2, -i p.2)) ∈ S`.

Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨g, hg, h, hh, rfl⟩` from `hF`. Set `g' : subalg A` to `⟨_, h1 g hg⟩`.

Set `h' : subalg A` to `⟨_, h1 _ (A'.antipode h hh)⟩`. Use `⟨g' ⊗ₜ h' - 1 ⊗ₜ (g' * h'), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (g' ⊗ₜ h' - 1 ⊗ₜ (g' * h')) = 0`. Set `b : B'` to `⟨g', g, hg, rfl⟩`. Rewrite using `[map_sub, hπ, hπ, sub_eq_zero]`.

Conclude with `tmul_move b h'`. Express the relevant statement in the definitionally equal form `ev A (g' ⊗ₜ h' - 1 ⊗ₜ (g' * h')) = _`. Rewrite using `[map_sub, ev_tmul, ev_tmul]`. Use function extensionality and compare the values at `p`. Simplify using `[g', h']`.

Consider the case `zero => convert S.zero_mem using 1`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Consider the case `add F G _ _ hF hG => convert S.add_mem hF hG using 1`. Use function extensionality and compare the values at `p`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c F _ hF => convert S.smul_mem c hF using 1`. Use function extensionality and compare the values at `p`. Simplify using `only [Pi.smul_apply, smul_sub]`.

Establish `hC : ∀ c ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (i : Q → N')) * A.carrier, (fun p : Q × Q => c (p.1 - p.2)) ∈ S`. Introduce `c hc`. Use `Submodule.mul_induction_on hc ?_ fun a b ha hb => S.add_mem ha hb` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩ c hc`. Establish `hg0 : g 0 = 0` using `hg.2`.

Use `hS _ (hB0 _ (A'.comul g hg.1)) _ (hA c hc)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[addPull, LinearMap.funLeft_apply, hg0, sub_eq_add_neg]`. Establish `hD : ∀ F ∈ tensorSpan R A.carrier, (fun p : Q × Q => F (p.1 - p.2, p.2) - F (0, p.2)) ∈ S`.

Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨g, hg, h, hh, rfl⟩` from `hF`. Take `⟨r, hr⟩` from `A.le_int hg 0`.

Establish `hm` using `hC _ (h2 (g - r • 1) (A.carrier.sub_mem hg (A.carrier.smul_mem r A.one_mem)) (by simp [Algebra.smul_def, hr]))`. Use `hS _ hm _ ⟨1 ⊗ₜ (⟨h, hh⟩ : subalg A), rfl⟩` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[ev_tmul, Algebra.smul_def, hr, sub_mul]`.

Consider the case `zero => convert S.zero_mem using 1`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Consider the case `add F G _ _ hF hG => convert S.add_mem hF hG using 1`. Use function extensionality and compare the values at `p`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c F _ hF => convert S.smul_mem c hF using 1`. Use function extensionality and compare the values at `p`. Simplify using `only [Pi.smul_apply, smul_sub]`.

Establish `hsurj` using `epi B' (subalg A) fun b => by`. Take `⟨t, ht, e⟩` from `hD _ (A.comul b.1 b.2)`. Establish `: t = b ⊗ₜ 1 - 1 ⊗ₜ b`. Apply `ev_injective hinj A` to reduce the goal to its premises. Use `e.trans ?_` and prove the remaining obligations.

Rewrite using `[map_sub, ev_tmul, ev_tmul]`. Use function extensionality and compare the values at `p`. Simplify using `[addPull, LinearMap.funLeft_apply]`. Establish `ht' : π t = 0` using `ht`. Rewrite `ht'` using `[this, map_sub, hπ, hπ, sub_eq_zero]`. Then use the resulting hypothesis.

Introduce `g hg`. Take `⟨⟨b, g', hg', e⟩, hb⟩` from `hsurj ⟨g, hg⟩`. Establish `hb' : b.1 = g` using `congrArg Subtype.val hb`. Conclude with `⟨g', hg', hb' ▸ e⟩`.
-/
theorem pull_eq (hinj : Function.Injective (algebraMap R C)) (A : HopfOrder (C := C) R Q)
    {N' : Type} [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (A' : HopfOrder (C := C) R N')
    (i : Q →+ N') (h1 : ∀ g ∈ A'.carrier, (fun x => g (i x)) ∈ A.carrier)
    (h2 : ∀ g ∈ A.carrier, g 0 = 0 →
      g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (i : Q → N')) * A.carrier) :
    A.carrier ≤ A'.carrier.map (LinearMap.funLeft R C (i : Q → N')) := by
  let B' : Subalgebra R (subalg A) :=
    ((subalg A').map (AlgHom.pi fun x : Q =>
      Pi.evalAlgHom R (fun _ : N' => C) (i x))).comap (subalg A).val
  have : Module.Finite R (subalg A) := Module.Finite.iff_fg.2 (SecondCohomologyLattice.fg_of_isLat A.lat)
  have : Module.Finite B' (subalg A) := Module.Finite.of_restrictScalars_finite R _ _
  let π : subalg A ⊗[R] subalg A →ₐ[R] subalg A ⊗[B'] subalg A :=
    Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ => Commute.all _ _
  have hπ : ∀ a b : subalg A, π (a ⊗ₜ b) = a ⊗ₜ b := by
    intro a b
    simp [π]
  let S : Submodule R (Q × Q → C) := (LinearMap.ker π.toLinearMap).map (ev A).toLinearMap
  have hS : ∀ F ∈ S, ∀ G ∈ (ev A).range, F * G ∈ S := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨u, rfl⟩
    refine ⟨t * u, ?_, map_mul (ev A) t u⟩
    have ht' : π t = 0 := ht
    change π (t * u) = 0
    rw [map_mul, ht', zero_mul]
  have hA : ∀ c ∈ A.carrier, (fun p : Q × Q => c (p.1 - p.2)) ∈ (ev A).range := by
    intro c hc
    have := tensorSpan_le A (A.comul c hc)
    simp only [sub_eq_add_neg]
    exact this
  have hB0 : ∀ F ∈ tensorSpan R A'.carrier,
      (fun p : Q × Q => F (i p.1, -i p.2) - F (i p.2, -i p.2)) ∈ S := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨g, hg, h, hh, rfl⟩ := hF
      let g' : subalg A := ⟨_, h1 g hg⟩
      let h' : subalg A := ⟨_, h1 _ (A'.antipode h hh)⟩
      refine ⟨g' ⊗ₜ h' - 1 ⊗ₜ (g' * h'), ?_, ?_⟩
      · change π (g' ⊗ₜ h' - 1 ⊗ₜ (g' * h')) = 0
        let b : B' := ⟨g', g, hg, rfl⟩
        rw [map_sub, hπ, hπ, sub_eq_zero]
        exact tmul_move b h'
      · change ev A (g' ⊗ₜ h' - 1 ⊗ₜ (g' * h')) = _
        rw [map_sub, ev_tmul, ev_tmul]
        funext p
        simp [g', h']
    | zero => convert S.zero_mem using 1; funext p; simp
    | add F G _ _ hF hG => convert S.add_mem hF hG using 1; funext p; simp only [Pi.add_apply]; ring
    | smul c F _ hF => convert S.smul_mem c hF using 1; funext p; simp only [Pi.smul_apply, smul_sub]
  have hC : ∀ c ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (i : Q → N')) * A.carrier,
      (fun p : Q × Q => c (p.1 - p.2)) ∈ S := by
    intro c hc
    refine Submodule.mul_induction_on hc ?_ fun a b ha hb => S.add_mem ha hb
    rintro _ ⟨g, hg, rfl⟩ c hc
    have hg0 : g 0 = 0 := hg.2
    have := hS _ (hB0 _ (A'.comul g hg.1)) _ (hA c hc)
    convert this using 1
    funext p
    simp [addPull, LinearMap.funLeft_apply, hg0, sub_eq_add_neg]
  have hD : ∀ F ∈ tensorSpan R A.carrier,
      (fun p : Q × Q => F (p.1 - p.2, p.2) - F (0, p.2)) ∈ S := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨g, hg, h, hh, rfl⟩ := hF
      obtain ⟨r, hr⟩ := A.le_int hg 0
      have hm := hC _ (h2 (g - r • 1) (A.carrier.sub_mem hg (A.carrier.smul_mem r A.one_mem))
        (by simp [Algebra.smul_def, hr]))
      have := hS _ hm _ ⟨1 ⊗ₜ (⟨h, hh⟩ : subalg A), rfl⟩
      convert this using 1
      funext p
      simp [ev_tmul, Algebra.smul_def, hr, sub_mul]
    | zero => convert S.zero_mem using 1; funext p; simp
    | add F G _ _ hF hG => convert S.add_mem hF hG using 1; funext p; simp only [Pi.add_apply]; ring
    | smul c F _ hF => convert S.smul_mem c hF using 1; funext p; simp only [Pi.smul_apply, smul_sub]
  have hsurj := epi B' (subalg A) fun b => by
    obtain ⟨t, ht, e⟩ := hD _ (A.comul b.1 b.2)
    have : t = b ⊗ₜ 1 - 1 ⊗ₜ b := by
      apply ev_injective hinj A
      refine e.trans ?_
      rw [map_sub, ev_tmul, ev_tmul]
      funext p
      simp [addPull, LinearMap.funLeft_apply]
    have ht' : π t = 0 := ht
    rwa [this, map_sub, hπ, hπ, sub_eq_zero] at ht'
  intro g hg
  obtain ⟨⟨b, g', hg', e⟩, hb⟩ := hsurj ⟨g, hg⟩
  have hb' : b.1 = g := congrArg Subtype.val hb
  exact ⟨g', hg', hb' ▸ e⟩

end

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv _ N _ _ _ AA N' _ _ _ A' j h1 hker`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `⟨h1 g hg, fun x k hk => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (j (x + k)) = g (j x)`.

Rewrite using `[map_add, AddMonoidHom.mem_ker.1 hk, add_zero]`. Establish `: Fintype (N ⧸ j.ker)` using `Fintype.ofFinite _`. Take `⟨-, ⟨AQ, hAQ⟩, -⟩` from `h2 C R v hv N j.ker AA`. Take `⟨f, hf, hfree⟩` from `exists_coset_basis hv AA j.ker`. Rewrite `hfree` using `[← hAQ]`.

Set `J` to `(augIdeal A'.carrier).map (LinearMap.funLeft R C (QuotientAddGroup.kerLift j : N ⧸ j.ker → N')) * AQ.carrier`. Establish `hi1 : ∀ g ∈ A'.carrier, (fun x => g (QuotientAddGroup.kerLift j x)) ∈ AQ.carrier`. Introduce `g hg`. Rewrite using `[hAQ]`. Conclude with `h1 g hg`.

Establish `hJ : J ≤ AQ.carrier`. Use `Submodule.mul_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩ c hc`. Conclude with `AQ.mul_mem _ _ (hi1 g hg.1) hc`. Establish `hco : ∀ g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier, ∃ b : j.ker → (N ⧸ j.ker → C), (∀ k, b k ∈ J) ∧ g = ∑ k, pullQ (R` using `R) j.ker (b k) * f k := by`.

Introduce `g hg`. Use `Submodule.mul_induction_on hg ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩ c hc`. Take `⟨b, ⟨hb, rfl⟩, -⟩` from `hfree c hc`. Use `choose b' hb' e using hb`.

Use `⟨fun k => _ * b' k, fun k => Submodule.mul_mem_mul ⟨g, hg, rfl⟩ (hb' k), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← e k, ← mul_assoc]`. Both sides reduce to the same expression.

Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`. Use `⟨a + b, fun k => J.add_mem (ha k) (hb k), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Establish `hmain` using `pull_eq hv.hom_inj AQ A' (QuotientAddGroup.kerLift j) hi1 (by`. Introduce `g hg hg0`.

Establish `hg' : pullQ (R` using `R) j.ker g ∈ AA.carrier := by rw [hAQ] at hg; exact hg`. Establish `hm` using `AA.mul_mem _ _ hg' (hf 0)`. Take `⟨b, hb, e⟩` from `hco _ (hker _ hm fun k hk => by`. Express the relevant statement in the definitionally equal form `g (k : N ⧸ j.ker) * _ = 0`. Rewrite using `[(QuotientAddGroup.eq_zero_iff _).2 hk, hg0, zero_mul])`.

Establish `hu` using `(hfree _ hm).unique (y₁ := fun k => pullQ (R := R) j.ker (b k)) (y₂ := fun k => if k = 0 then pullQ (R := R) j.ker g else 0) ⟨fun k => ⟨_, hJ (hb k), rfl⟩, e⟩ ⟨fun k => by`. Distinguish the cases in `hk : k = 0`. Rewrite using `[if_pos hk]`. Conclude with `⟨g, hg, rfl⟩`. Rewrite using `[if_neg hk]; exact Submodule.zero_mem _, by simp⟩`.

Establish `h0` using `congrFun hu 0`. Rewrite `h0` using `[if_pos rfl]`. Establish `: b 0 = g`. Use function extensionality and compare the values at `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Conclude with `congrFun h0 x`. Conclude with `this ▸ hb 0)`. Introduce `g hg`. Take `⟨g', hg', rfl⟩` from `mem_map_comap_pullbackQuotient AA j.ker hg.1 fun x k => hg.2 x k k.2`. Rewrite `hg'` using `[← hAQ]`.

Take `⟨a, ha, rfl⟩` from `hmain hg'`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem sub_closed : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA N' _ _ _ A' j h1 hker
  classical
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨h1 g hg, fun x k hk => ?_⟩
    change g (j (x + k)) = g (j x)
    rw [map_add, AddMonoidHom.mem_ker.1 hk, add_zero]
  have : Fintype (N ⧸ j.ker) := Fintype.ofFinite _
  obtain ⟨-, ⟨AQ, hAQ⟩, -⟩ := h2 C R v hv N j.ker AA
  obtain ⟨f, hf, hfree⟩ := exists_coset_basis hv AA j.ker
  rw [← hAQ] at hfree
  let J := (augIdeal A'.carrier).map
    (LinearMap.funLeft R C (QuotientAddGroup.kerLift j : N ⧸ j.ker → N')) * AQ.carrier
  have hi1 : ∀ g ∈ A'.carrier, (fun x => g (QuotientAddGroup.kerLift j x)) ∈ AQ.carrier := by
    intro g hg
    rw [hAQ]
    exact h1 g hg
  have hJ : J ≤ AQ.carrier := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩ c hc
    exact AQ.mul_mem _ _ (hi1 g hg.1) hc
  have hco : ∀ g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier,
      ∃ b : j.ker → (N ⧸ j.ker → C), (∀ k, b k ∈ J) ∧
        g = ∑ k, pullQ (R := R) j.ker (b k) * f k := by
    intro g hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩ c hc
      obtain ⟨b, ⟨hb, rfl⟩, -⟩ := hfree c hc
      choose b' hb' e using hb
      refine ⟨fun k => _ * b' k, fun k => Submodule.mul_mem_mul ⟨g, hg, rfl⟩ (hb' k), ?_⟩
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← e k, ← mul_assoc]
      rfl
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      refine ⟨a + b, fun k => J.add_mem (ha k) (hb k), ?_⟩
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have hmain := pull_eq hv.hom_inj AQ A' (QuotientAddGroup.kerLift j) hi1 (by
    intro g hg hg0
    have hg' : pullQ (R := R) j.ker g ∈ AA.carrier := by rw [hAQ] at hg; exact hg
    have hm := AA.mul_mem _ _ hg' (hf 0)
    obtain ⟨b, hb, e⟩ := hco _ (hker _ hm fun k hk => by
      change g (k : N ⧸ j.ker) * _ = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 hk, hg0, zero_mul])
    have hu := (hfree _ hm).unique
      (y₁ := fun k => pullQ (R := R) j.ker (b k))
      (y₂ := fun k => if k = 0 then pullQ (R := R) j.ker g else 0)
      ⟨fun k => ⟨_, hJ (hb k), rfl⟩, e⟩
      ⟨fun k => by
        by_cases hk : k = 0
        · rw [if_pos hk]; exact ⟨g, hg, rfl⟩
        · rw [if_neg hk]; exact Submodule.zero_mem _, by simp⟩
    have h0 := congrFun hu 0
    rw [if_pos rfl] at h0
    have : b 0 = g := by
      funext q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact congrFun h0 x
    exact this ▸ hb 0)
  intro g hg
  obtain ⟨g', hg', rfl⟩ := mem_map_comap_pullbackQuotient AA j.ker hg.1 fun x k => hg.2 x k k.2
  rw [← hAQ] at hg'
  obtain ⟨a, ha, rfl⟩ := hmain hg'
  exact ⟨a, ha, rfl⟩

end PositivityTheory.HtPt.Rh
