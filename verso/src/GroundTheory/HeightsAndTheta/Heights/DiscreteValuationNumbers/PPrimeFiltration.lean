import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
The claim follows from `weightedDecomposition.decompose'_apply R (blockWeight ι) r b`.
-/
theorem decompose_blockWeight {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (r : MRing ι R) (b : K → ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) r b : MRing ι R) =
      weightedHomogeneousComponent (blockWeight ι) b r :=
  weightedDecomposition.decompose'_apply R (blockWeight ι) r b

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h b r hr`. Rewrite using `[decompose_blockWeight]`. Conclude with `h r hr b`. Introduce `h r hr b`.

Rewrite using `[← decompose_blockWeight]`. Conclude with `h b hr`.
-/
theorem isMultiHomogIdeal_iff_isHomogeneous {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
  constructor
  · intro h b r hr
    rw [decompose_blockWeight]
    exact h r hr b
  · intro h r hr b
    rw [← decompose_blockWeight]
    exact h b hr

/- English proof (translation)
Rewrite `hJ`, the goal using `[isMultiHomogIdeal_iff_isHomogeneous]`. Use `hJ.sup (Ideal.homogeneous_span _ _ ?_)` and prove the remaining obligations. Introduce and unpack `x rfl`. Conclude with `⟨s, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩`.
-/
theorem isMultiHomogIdeal_sup_span {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} {J : Ideal (MRing ι R)} {f : MRing ι R} {s : K → ℕ}
    (hJ : IsMultiHomogIdeal J) (hf : IsMultiHomog f s) :
    IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ ?_)
  rintro x rfl
  exact ⟨s, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩

/- English proof (translation)
Unfold `multAt`. Establish `: Subsingleton (MRing ι R ⧸ (⊤ : Ideal (MRing ι R)))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Conclude with `Module.length_eq_zero`.
-/
theorem multAt_top {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (W : Ideal (MRing ι R)) [W.IsPrime] : multAt (⊤ : Ideal (MRing ι R)) W = 0 := by
  unfold multAt
  have : Subsingleton (MRing ι R ⧸ (⊤ : Ideal (MRing ι R))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

/- English proof (translation)
Introduce `F _ K _ _ ι _ J`. Establish `: WellFoundedGT (Ideal (MRing ι F))` using `inferInstance`. Proceed by induction on `J using WellFoundedGT.induction`. Name the introduced variables `J ih`. Introduce `hJ`.

Distinguish the cases in `hT : J = ⊤`. Substitute `hT` using the available equality. Use `⟨[], by simp, fun m => by simp [hilbFn_top], fun W _ => by simp [multAt_top]⟩` and prove the remaining obligations. Take `⟨f, s, hf, hfJ, hQ⟩` from `h1 F K ι J hJ hT`. Establish `hQh : IsMultiHomogIdeal (J.colon {f})` using `h4 F K ι J f s hJ hf`.

Establish `hJQ : J ≤ J.colon {f}` using `fun x hx => Submodule.mem_colon_singleton.mpr (J.mul_mem_right f hx)`. Establish `hlt : J < J ⊔ Ideal.span {f}` using `SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, f, Ideal.mem_sup_right (Ideal.mem_span_singleton_self f), hfJ⟩`. Take `⟨l', hl'1, hl'2, hl'3⟩` from `ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)`. Use `⟨(J.colon {f}, s) :: l', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Break down `List.mem_cons.mp hp with rfl | hp` into its components or cases. Conclude with `⟨hQ, hQh, hJQ⟩`. Take `⟨a, b, c⟩` from `hl'1 p hp`. Conclude with `⟨a, b, le_sup_left.trans c⟩`. Introduce `m`.

Rewrite using `[h2 F K ι J f s hJ hf m, hl'2 m, List.map_cons, List.sum_cons, add_comm]`. Introduce `W _`. Rewrite using `[h3 F K ι J W f, hl'3 W, List.map_cons, List.sum_cons, add_comm]`.
-/
theorem PrimeFiltration.proof (h1 : AssociatedMultiHomogPrime.Statement.{u})
    (h2 : FiltrationStepHilb.Statement.{u}) (h3 : FiltrationStepLength.Statement.{u})
    (h4 : ColonMultiHomog.Statement.{u}) : PrimeFiltration.Statement.{u} := by
  intro F _ K _ _ ι _ J
  have : WellFoundedGT (Ideal (MRing ι F)) := inferInstance
  induction J using WellFoundedGT.induction
  rename_i J ih
  intro hJ
  by_cases hT : J = ⊤
  · subst hT
    refine ⟨[], by simp, fun m => by simp [hilbFn_top], fun W _ => by simp [multAt_top]⟩
  obtain ⟨f, s, hf, hfJ, hQ⟩ := h1 F K ι J hJ hT
  have hQh : IsMultiHomogIdeal (J.colon {f}) := h4 F K ι J f s hJ hf
  have hJQ : J ≤ J.colon {f} := fun x hx =>
    Submodule.mem_colon_singleton.mpr (J.mul_mem_right f hx)
  have hlt : J < J ⊔ Ideal.span {f} :=
    SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, f, Ideal.mem_sup_right (Ideal.mem_span_singleton_self f), hfJ⟩
  obtain ⟨l', hl'1, hl'2, hl'3⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨(J.colon {f}, s) :: l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hQ, hQh, hJQ⟩
    · obtain ⟨a, b, c⟩ := hl'1 p hp
      exact ⟨a, b, le_sup_left.trans c⟩
  · intro m
    rw [h2 F K ι J f s hJ hf m, hl'2 m, List.map_cons, List.sum_cons, add_comm]
  · intro W _
    rw [h3 F K ι J W f, hl'3 W, List.map_cons, List.sum_cons, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
