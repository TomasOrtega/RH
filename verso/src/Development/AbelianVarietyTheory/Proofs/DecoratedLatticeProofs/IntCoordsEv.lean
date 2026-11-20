import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlaceStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

/- English proof (translation)
The claim follows from `(algebraMap D.host.F (Af D.host.F) c).2`.
-/
theorem alg_int_ev (c : D.host.F) : ∀ᶠ w in Filter.cofinite,
    algebraMap D.host.F (Fv D.host.F w) c ∈ (w : Pl D).adicCompletionIntegers D.host.F :=
  (algebraMap D.host.F (Af D.host.F) c).2

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `[Finsupp.mapRange_apply, smul_eq_mul]`.
-/
theorem repr_tmul_loc (w : Pl D) (x : Fv D.host.F w) (e : D.host.E) (i : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (x ⊗ₜ[D.host.F] e) i =
      x * algebraMap D.host.F (Fv D.host.F w) ((Module.finBasis D.host.F D.host.E).repr e i) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

/- English proof (translation)
Use `set b := Module.finBasis D.host.F D.host.E`. Use `set B := NumberField.RingOfIntegers.basis D.host.E`. Establish `hev : ∀ᶠ w in Filter.cofinite, ∀ i j, algebraMap D.host.F (Fv D.host.F w) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) i) ∈ (w : Pl D).adicCompletionIntegers D.host.F`. Rewrite using `[Filter.eventually_all]`. Introduce `i`.

Rewrite using `[Filter.eventually_all]`. Introduce `j`. Conclude with `alg_int_ev _`. Use `filter_upwards [hev] with w hw`. Introduce `z hz`.

Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, o, rfl⟩` from `hy`. Introduce `i`. Establish `hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] (o : D.host.E)) = evalV D.host.F w α ⊗ₜ[D.host.F] (o : D.host.E)` using `rfl`.

Rewrite using `[hc, repr_tmul_loc]`. Use `mul_mem (hα w) ?_` and prove the remaining obligations. Establish `ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E)` using `by conv_lhs => rw [← B.sum_repr o]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[ho, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Finsupp.smul_apply, map_zsmul]`. Conclude with `zsmul_mem (hw i j) _`. Consider the case `zero => intro i`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro i`. Rewrite using `[map_add, map_add, Finsupp.add_apply]`. Conclude with `add_mem (hx i) (hy i)`. Consider the case `neg x _ hx => intro i`.

Rewrite using `[map_neg, map_neg, Finsupp.neg_apply]`. Conclude with `neg_mem (hx i)`.
-/
theorem int_coords_ev : ∀ᶠ w in Filter.cofinite, ∀ z ∈ intAE D, ∀ i,
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
      (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z) i ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ w in Filter.cofinite, ∀ i j,
      algebraMap D.host.F (Fv D.host.F w) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) i) ∈
        (w : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact alg_int_ev _
  filter_upwards [hev] with w hw
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, o, rfl⟩ := hy
    intro i
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [hc, repr_tmul_loc]
    refine mul_mem (hα w) ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl
    rw [ho, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hw i j) _
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [map_add, map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  | neg x _ hx => intro i; rw [map_neg, map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

/- English proof (translation)
Use `conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem sum_repr_tmul (w : Pl D) (y : Fv D.host.F w ⊗[D.host.F] D.host.E) :
    ∑ i, (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr y i ⊗ₜ[D.host.F]
      (Module.finBasis D.host.F D.host.E) i = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Introduce `D a _ ⟨T, hT⟩`. Use `set b := Module.finBasis D.host.F D.host.E`. Set `c : Fin (Module.finrank D.host.F D.host.E) → (w : Pl D) → Fv D.host.F w` to `fun i w => (Algebra.TensorProduct.basis (Fv D.host.F w) b).repr (compAt D w (a w)) i`. Establish `hc : ∀ i, ∀ᶠ w in Filter.cofinite, c i w ∈ (w : Pl D).adicCompletionIntegers D.host.F`. Introduce `i`.

Use `filter_upwards [int_coords_ev (D := D), T.finite_toSet.compl_mem_cofinite] with w hw hwT`. Conclude with `hw _ (hT w hwT).2 i`. Set `C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F` to `fun i => RestrictedProduct.mk (c i) (hc i)`. Use `⟨∑ i, pairA D.host.F 0 (C i) ⊗ₜ[D.host.F] b i, ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_eq_zero fun i _ => infPart_pair _ _`. Unfold `idOff`. Use `(Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `w`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`.

Simplify using `only [compAt_pair]`. Conclude with `sum_repr_tmul w (compAt D w (a w))`.
-/
theorem glue : ∀ (D : D7) (a : Pl D → AE D), (∀ x, a x ∈ idAt D (· = x)) →
    (∃ T : Finset (Pl D), ∀ x ∉ T, a x ∈ intAt D (· = x)) →
    ∃ s : AE D, infPart D s = 0 ∧ ∀ x, s - a x ∈ idOff D (· = x) := by
  intro D a _ ⟨T, hT⟩
  classical
  set b := Module.finBasis D.host.F D.host.E
  let c : Fin (Module.finrank D.host.F D.host.E) → (w : Pl D) → Fv D.host.F w := fun i w =>
    (Algebra.TensorProduct.basis (Fv D.host.F w) b).repr (compAt D w (a w)) i
  have hc : ∀ i, ∀ᶠ w in Filter.cofinite, c i w ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
    intro i
    filter_upwards [int_coords_ev (D := D), T.finite_toSet.compl_mem_cofinite] with w hw hwT
    exact hw _ (hT w hwT).2 i
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun i => RestrictedProduct.mk (c i) (hc i)
  refine ⟨∑ i, pairA D.host.F 0 (C i) ⊗ₜ[D.host.F] b i, ?_, fun x => ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => infPart_pair _ _
  · unfold idOff
    refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
    obtain ⟨w, rfl⟩ := w
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [compAt_pair]
    exact sum_repr_tmul w (compAt D w (a w))

end GlobalTheory.FinPlLoc
