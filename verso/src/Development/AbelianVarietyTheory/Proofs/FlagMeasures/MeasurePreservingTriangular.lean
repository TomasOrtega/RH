import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RowRawRange
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CokernelPairSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.TriShift

section General
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]

open ValuativeRel MeasureTheory ComplexConjugate in
open scoped ComplexOrder in
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι] in
/- English proof (translation)
Set `p : ι → Prop` to `fun j => j ≠ i`. Set `e` to `MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p`. Establish `he : MeasurePreserving e (Measure.pi fun _ : ι => μ) ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ))` using `measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p`. Set `c : ({j // p j} → G) → ({j // ¬ p j} → G)` to `fun y _ => g (e.symm (y, 0))`. Establish `hc : Measurable c` using `measurable_pi_lambda _ fun _ => hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))`.

Establish `hT : MeasurePreserving (fun q : ({j // p j} → G) × ({j // ¬ p j} → G) => (id q.1, q.2 + c q.1)) ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ))` using `(MeasurePreserving.id _).skew_product (g := fun y z => z + c y) (measurable_snd.add (hc.comp measurable_fst)) (Filter.Eventually.of_forall fun y => map_add_right_eq_self _ _)`. Establish `hcomp` using `(MeasurePreserving.symm e he).comp (hT.comp he)`. Use `hcomp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[e, c, p]`. Conclude with `hgi _ _ fun k hk => by simp [hk]`. Simplify using `[e, c, p, hj]`.
-/
private lemma measurePreserving_update_add_of_indep [DecidableEq ι] (i : ι)
    (g : (ι → G) → G) (hg : Measurable g)
    (hgi : ∀ x y : ι → G, (∀ j, j ≠ i → x j = y j) → g x = g y) :
    MeasurePreserving (fun x : ι → G => Function.update x i (x i + g x))
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  let p : ι → Prop := fun j => j ≠ i
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p
  have he : MeasurePreserving e (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  let c : ({j // p j} → G) → ({j // ¬ p j} → G) := fun y _ => g (e.symm (y, 0))
  have hc : Measurable c :=
    measurable_pi_lambda _ fun _ =>
      hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hT : MeasurePreserving
      (fun q : ({j // p j} → G) × ({j // ¬ p j} → G) => (id q.1, q.2 + c q.1))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    (MeasurePreserving.id _).skew_product (g := fun y z => z + c y)
      (measurable_snd.add (hc.comp measurable_fst))
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self _ _)
  have hcomp := (MeasurePreserving.symm e he).comp (hT.comp he)
  convert hcomp using 1
  funext x j
  by_cases hj : j = i
  · subst hj
    simp [e, c, p]
    exact hgi _ _ fun k hk => by simp [hk]
  · simp [e, c, p, hj]

open ValuativeRel MeasureTheory ComplexConjugate in
open scoped ComplexOrder in
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι] in

/- English proof (translation)
Set `Φ : Finset ι → (ι → G) → ι → G` to `fun s x j => if j ∈ s then x j + f j x else x j`. Establish `hΦ : ∀ s, MeasurePreserving (Φ s) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on_max_value rk with`. Consider the case `empty`.

Use `MeasurePreserving.id (Measure.pi fun _ : ι => μ) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x j`. Simplify using `[Φ]`. Consider the case `insert a s ha hmax ih`. Establish `hstep` using `measurePreserving_update_add_of_indep μ a (f a) (hf a) fun x y hxy => hd a x y fun j hj => hxy j (by rintro rfl; exact lt_irrefl _ hj)`.

Use `ih.comp hstep using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x j`. Distinguish the cases in `hja : j = a`. Substitute `hja` using the available equality. Simplify using `[Φ, ha]`.

Distinguish the cases in `hjs : j ∈ s`. Establish `hf' : f j (Function.update x a (x a + f a x)) = f j x` using `hd j _ _ fun k hk => by`. Establish `hka : k ≠ a`. Introduce and unpack `rfl`. Conclude with `absurd (hmax j hjs) (not_le.2 hk)`.

Simplify using `[hka]`. Simplify using `[Φ, hja, hjs, hf']`. Simplify using `[Φ, hja, hjs]`. Use `hΦ Finset.univ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x j`.

Simplify using `[Φ]`.
-/
theorem _root_.GlobalTheory.SgLoc.TriShift.measurePreserving_triangular (rk : ι → ℕ) (f : ι → (ι → G) → G)
    (hf : ∀ i, Measurable (f i))
    (hd : ∀ i x y, (∀ j, rk j < rk i → x j = y j) → f i x = f i y) :
    MeasurePreserving (fun (x : ι → G) i => x i + f i x) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
  classical
  let Φ : Finset ι → (ι → G) → ι → G := fun s x j => if j ∈ s then x j + f j x else x j
  have hΦ : ∀ s, MeasurePreserving (Φ s) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
    intro s
    induction s using Finset.induction_on_max_value rk with
    | empty =>
      convert MeasurePreserving.id (Measure.pi fun _ : ι => μ) using 1
      funext x j
      simp [Φ]
    | insert a s ha hmax ih =>
      have hstep := measurePreserving_update_add_of_indep μ a (f a) (hf a)
        fun x y hxy => hd a x y fun j hj => hxy j (by rintro rfl; exact lt_irrefl _ hj)
      convert ih.comp hstep using 1
      funext x j
      by_cases hja : j = a
      · subst hja
        simp [Φ, ha]
      · by_cases hjs : j ∈ s
        · have hf' : f j (Function.update x a (x a + f a x)) = f j x :=
            hd j _ _ fun k hk => by
              have hka : k ≠ a := by
                rintro rfl
                exact absurd (hmax j hjs) (not_le.2 hk)
              simp [hka]
          simp [Φ, hja, hjs, hf']
        · simp [Φ, hja, hjs]
  convert hΦ Finset.univ using 1
  funext x j
  simp [Φ]

end General

end GlobalTheory.SgLoc.TriShift
