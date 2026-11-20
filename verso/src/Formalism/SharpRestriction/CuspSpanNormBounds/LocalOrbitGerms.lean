import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqZeroOfIdealCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures

namespace Formalism.MainNotions.LocalOrbitGerms

section Defs

variable {K : Type} [CommRing K] {n : ℕ}

def mk (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) :
    Matrix (Fin n) (Fin n) K :=
  fun a b => if a = b then 1 else if h : P (a, b) then x ⟨(a, b), h⟩ else 0

abbrev PL (n : ℕ) : Fin n × Fin n → Prop := fun p => p.2 < p.1

abbrev PU (n : ℕ) : Fin n × Fin n → Prop := fun p => p.1 < p.2

abbrev PN (sb : Fin n → Fin n → Bool) : Fin n × Fin n → Prop :=
  fun p => p.1 < p.2 ∧ sb p.1 p.2 = false

abbrev PW (sb : Fin n → Fin n → Bool) : Fin n × Fin n → Prop :=
  fun p => p.2 < p.1 ∧ sb p.1 p.2 = false

abbrev PV (sb : Fin n → Fin n → Bool) : Fin n × Fin n → Prop :=
  fun p => p.2 < p.1 ∧ sb p.1 p.2 = true

end Defs

def TriangularShearMeasurePreserving : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Type) [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ρ : ι → ℕ) (g : (ι → E) → ι → E), Measurable g →
    (∀ i x x', (∀ j, ρ j < ρ i → x j = x' j) → g x i = g x' i) →
    ∃ e : (ι → E) ≃ᵐ (ι → E), (∀ x, e x = x + g x) ∧
      MeasurePreserving e (Measure.pi fun _ => μ) (Measure.pi fun _ => μ)

def CoordinateMergeMeasurable : Prop :=
  ∀ (ι₁ ι₂ ι : Type) [Fintype ι₁] [Fintype ι₂] [Fintype ι] (E : Type) [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (e : ι₁ ⊕ ι₂ ≃ ι),
    ∃ m : ((ι₁ → E) × (ι₂ → E)) ≃ᵐ (ι → E), (∀ p i, m p i = Sum.elim p.1 p.2 (e.symm i)) ∧
      MeasurePreserving m ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
        (Measure.pi fun _ => μ)

def UnipotentProductMeasureInvariant : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (R : Subring K), μ (R : Set K) = 1 →
  ∀ (s : List ℕ) (t : ℕ → Kˣ) (sb : Fin s.sum → Fin s.sum → Bool),
    (∀ a b, sb a b = true ↔ blk s a = blk s b) →
  ∃ (μ₁ : Measure (lowW K s t)) (μ₂ : Measure (upUniG K s.sum)),
    μ₁.IsMulRightInvariant ∧ μ₂.IsMulLeftInvariant ∧ SFinite μ₁ ∧ SFinite μ₂ ∧
    μ₁ (intSub R (lowW K s t) : Set (lowW K s t)) = 1 ∧
    μ₂ (intSub R (upUniG K s.sum) : Set (upUniG K s.sum)) = 1 ∧
    ∀ G : Matrix (Fin s.sum) (Fin s.sum) K → Matrix (Fin s.sum) (Fin s.sum) K → ℂ,
      ∫ p, G ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)
          ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) ∂(μ₁.prod μ₂) =
        ∫ xy : ({p // PW sb p} → K) × ({p // PU s.sum p} → K),
          G (mk (PW sb) xy.1) (mk (PU s.sum) xy.2)
            ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

def OrbitParametrisationsAgree : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (s : List ℕ) (t : ℕ → Kˣ) (sb : Fin s.sum → Fin s.sum → Bool),
    (∀ a b, sb a b = true ↔ blk s a = blk s b) →
    ∀ G : Matrix (Fin s.sum) (Fin s.sum) K → K → ℂ,
      ∫ xy : ({p // PL s.sum p} → K) × ({p // PN sb p} → K),
          G (mk (PL s.sum) xy.1 * pt s t * mk (PN sb) xy.2)
            (sLow (mk (PL s.sum) xy.1) + sUp (mk (PN sb) xy.2))
            ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) =
        ∫ xy : ({p // PW sb p} → K) × ({p // PU s.sum p} → K),
          G (mk (PW sb) xy.1 * pt s t * mk (PU s.sum) xy.2)
            (sLow (mk (PW sb) xy.1) + sUp (mk (PU s.sum) xy.2))
            ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
example {E : Type} [CommRing E] {n : ℕ} (x : Formalism.MainNotions.S.Loc.IL n → E) :
    Formalism.MainNotions.S.Loc.uLow x = mk (PL n) x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
example {E : Type} [CommRing E] {n : ℕ} (w : Formalism.MainNotions.S.Loc.Pt E n) (y : Formalism.MainNotions.S.Loc.IN w → E) :
    Formalism.MainNotions.S.Loc.uUp w y = mk (PN fun a b => Formalism.MainNotions.S.Loc.sameBlock w.blocks a b) y := rfl

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open MeasureTheory

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Meas

section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant]

def skewEquiv (S : ι → Prop) (g : (ι → E) → ι → E) (hg : Measurable g)
    (hdep : ∀ x x', (∀ j, ¬ S j → x j = x' j) → g x = g x') (hsupp : ∀ x i, ¬ S i → g x i = 0) :
    (ι → E) ≃ᵐ (ι → E) where
  toFun x := x + g x
  invFun x := x - g x
  left_inv x := by
    have : g (x + g x) = g x := hdep _ _ fun j hj => by simp [hsupp x j hj]
    simp [this]
  right_inv x := by
    have : g (x - g x) = g x := hdep _ _ fun j hj => by simp [hsupp x j hj]
    simp [this]
  measurable_toFun := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (measurable_pi_apply i).add ((measurable_pi_apply i).comp hg)
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (measurable_pi_apply i).sub ((measurable_pi_apply i).comp hg)

/- English proof (translation)
Set `Φ` to `MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) S`. Establish `hΦ : MeasurePreserving Φ (Measure.pi fun _ => μ) ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ))` using `measurePreserving_piEquivPiSubtypeProd (fun _ => μ) S`. Establish `hz : Measurable (fun v : {i // ¬ S i} → E => ((0 : Subtype S → E), v))` using `by first`. Consider the case `exact measurable_const.prodMk measurable_id`. Consider the case `exact measurable_const.prod_mk measurable_id`.

Consider the case `exact Measurable.prod measurable_const measurable_id`. Set `G : ({i // ¬ S i} → E) → (Subtype S → E)` to `fun v i => g (Φ.symm (0, v)) i.1`. Establish `hGm : Measurable G`. Use `measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Conclude with `(measurable_pi_apply i.1).comp (hg.comp (Φ.symm.measurable.comp hz))`.

Establish `hF : MeasurePreserving (fun p : ({i // ¬ S i} → E) × (Subtype S → E) => (id p.1, G p.1 + p.2)) ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ)) ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ))`. Use `MeasurePreserving.skew_product (g := fun v u => G v + u) (MeasurePreserving.id _) ?_ ?_` and prove the remaining obligations. Conclude with `(hGm.comp measurable_fst).add measurable_snd`. Use `first`. Consider the case `exact Filter.Eventually.of_forall fun v => map_add_left_eq_self _ (G v)`.

Consider the case `exact Filter.eventually_of_forall fun v => map_add_left_eq_self _ (G v)`. Establish `hsw1 : MeasurePreserving (Prod.swap : (Subtype S → E) × ({i // ¬ S i} → E) → _) ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ)) ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ))` using `Measure.measurePreserving_swap`. Establish `hsw2 : MeasurePreserving (Prod.swap : ({i // ¬ S i} → E) × (Subtype S → E) → _) ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ)) ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ))` using `Measure.measurePreserving_swap`. Establish `hall` using `(MeasurePreserving.symm Φ hΦ).comp (hsw2.comp (hF.comp (hsw1.comp hΦ)))`. Use `hall using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Use function extensionality and compare the values at `i`. Use `show x i + g x i = (if h : S i then (G (fun j : {i // ¬ S i} => x j) + fun j : Subtype S => x j) ⟨i, h⟩ else (fun j : {i // ¬ S i} => x j) ⟨i, h⟩)`. Distinguish the cases in `h : S i`. Rewrite using `[dif_pos h]`.

Establish `hx : g (Φ.symm (0, fun j : {i // ¬ S i} => x j)) = g x`. Apply `hdep` to reduce the goal to its premises. Introduce `j hj`. Use `show (if h' : S j then (0 : Subtype S → E) ⟨j, h'⟩ else (fun j : {i // ¬ S i} => x j) ⟨j, h'⟩) = x j`. Rewrite using `[dif_neg hj]`.

Use `show x i + g x i = g (Φ.symm (0, fun j : {i // ¬ S i} => x j)) i + x i`. Rewrite using `[hx, add_comm]`. Rewrite using `[dif_neg h, hsupp x i h, add_zero]`.
-/
theorem skew (S : ι → Prop) [DecidablePred S] (g : (ι → E) → ι → E) (hg : Measurable g)
    (hdep : ∀ x x', (∀ j, ¬ S j → x j = x' j) → g x = g x') (hsupp : ∀ x i, ¬ S i → g x i = 0) :
    MeasurePreserving (skewEquiv S g hg hdep hsupp) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ) := by
  let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) S
  have hΦ : MeasurePreserving Φ (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => μ) S
  have hz : Measurable (fun v : {i // ¬ S i} → E => ((0 : Subtype S → E), v)) := by
    first
      | exact measurable_const.prodMk measurable_id
      | exact measurable_const.prod_mk measurable_id
      | exact Measurable.prod measurable_const measurable_id
  let G : ({i // ¬ S i} → E) → (Subtype S → E) := fun v i => g (Φ.symm (0, v)) i.1
  have hGm : Measurable G := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (measurable_pi_apply i.1).comp (hg.comp (Φ.symm.measurable.comp hz))
  have hF : MeasurePreserving (fun p : ({i // ¬ S i} → E) × (Subtype S → E) => (id p.1, G p.1 + p.2))
      ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ))
      ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ)) := by
    refine MeasurePreserving.skew_product (g := fun v u => G v + u) (MeasurePreserving.id _) ?_ ?_
    · exact (hGm.comp measurable_fst).add measurable_snd
    · first
        | exact Filter.Eventually.of_forall fun v => map_add_left_eq_self _ (G v)
        | exact Filter.eventually_of_forall fun v => map_add_left_eq_self _ (G v)
  have hsw1 : MeasurePreserving (Prod.swap : (Subtype S → E) × ({i // ¬ S i} → E) → _)
      ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ))
      ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ)) :=
    Measure.measurePreserving_swap
  have hsw2 : MeasurePreserving (Prod.swap : ({i // ¬ S i} → E) × (Subtype S → E) → _)
      ((Measure.pi fun _ : {i // ¬ S i} => μ).prod (Measure.pi fun _ : Subtype S => μ))
      ((Measure.pi fun _ : Subtype S => μ).prod (Measure.pi fun _ : {i // ¬ S i} => μ)) :=
    Measure.measurePreserving_swap
  have hall := (MeasurePreserving.symm Φ hΦ).comp (hsw2.comp (hF.comp (hsw1.comp hΦ)))
  convert hall using 1
  funext x
  funext i
  show x i + g x i = (if h : S i then (G (fun j : {i // ¬ S i} => x j) + fun j : Subtype S => x j) ⟨i, h⟩
    else (fun j : {i // ¬ S i} => x j) ⟨i, h⟩)
  by_cases h : S i
  · rw [dif_pos h]
    have hx : g (Φ.symm (0, fun j : {i // ¬ S i} => x j)) = g x := by
      apply hdep
      intro j hj
      show (if h' : S j then (0 : Subtype S → E) ⟨j, h'⟩ else (fun j : {i // ¬ S i} => x j) ⟨j, h'⟩) = x j
      rw [dif_neg hj]
    show x i + g x i = g (Φ.symm (0, fun j : {i // ¬ S i} => x j)) i + x i
    rw [hx, add_comm]
  · rw [dif_neg h, hsupp x i h, add_zero]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `g _ _ hsupp`. Use `⟨MeasurableEquiv.refl _, fun x => ?_, MeasurePreserving.id _⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[hsupp x i (Nat.zero_le _)]`. Consider the case `succ N ih`. Introduce `g hg hdep hsupp`. Set `S : ι → Prop` to `fun i => ρ i = N`. Set `g1 : (ι → E) → ι → E` to `fun x i => if ρ i = N then g x i else 0`.

Set `g0 : (ι → E) → ι → E` to `fun x i => if ρ i < N then g x i else 0`. Establish `hg1 : Measurable g1`. Use `measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : ρ i = N`. Simplify using `only [g1, h, if_true]`.

Conclude with `(measurable_pi_apply i).comp hg`. Simplify using `only [g1, h, if_false]`. Conclude with `measurable_const`. Establish `hg0 : Measurable g0`. Use `measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations.

Distinguish the cases in `h : ρ i < N`. Simplify using `only [g0, h, if_true]`. Conclude with `(measurable_pi_apply i).comp hg`. Simplify using `only [g0, h, if_false]`. Conclude with `measurable_const`.

Establish `hdep1 : ∀ x x', (∀ j, ¬ S j → x j = x' j) → g1 x = g1 x'`. Introduce `x x' h`. Use function extensionality and compare the values at `i`. Simplify using `only [g1]`. Use `split_ifs with hi`.

Conclude with `hdep i x x' fun j hj => h j (by simp only [S]; omega)`. Both sides reduce to the same expression. Establish `hsupp1 : ∀ x i, ¬ S i → g1 x i = 0`. Introduce `x i hi`. Simplify using `only [g1]`.

Rewrite using `[if_neg hi]`. Take `⟨e0, he0, hm0⟩` from `ih g0 hg0 (by`. Introduce `i x x' h`. Simplify using `only [g0]`. Use `split_ifs with hi`.

Conclude with `hdep i x x' h`. Use the proof step `rfl)`. Use the proof step `(by`. Introduce `x i hi`. Simplify using `only [g0]`.

Rewrite using `[if_neg (not_lt.2 hi)])`. Use `⟨(skewEquiv S g1 hg1 hdep1 hsupp1).trans e0, fun x => ?_, (skew μ S g1 hg1 hdep1 hsupp1).trans hm0⟩` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.trans_apply, he0]`. Establish `hskew : skewEquiv S g1 hg1 hdep1 hsupp1 x = x + g1 x` using `rfl`. Rewrite using `[hskew]`.

Establish `h0 : g0 (x + g1 x) = g0 x`. Use function extensionality and compare the values at `i`. Simplify using `only [g0]`. Use `split_ifs with hi`. Apply `hdep i` to reduce the goal to its premises.

Introduce `j hj`. Simplify using `only [Pi.add_apply, g1]`. Rewrite using `[if_neg (by omega)]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite using `[h0]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, g0, g1]`. Distinguish the cases in `h1 : ρ i < N`. Rewrite using `[if_neg (by omega), if_pos h1]`.

Simplify using the standard rewrite rules. Distinguish the cases in `h2 : ρ i = N`. Rewrite using `[if_pos h2, if_neg h1]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h2, if_neg h1, hsupp x i (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem measurePreserving_of_card (ρ : ι → ℕ) (N : ℕ) : ∀ (g : (ι → E) → ι → E), Measurable g →
    (∀ i x x', (∀ j, ρ j < ρ i → x j = x' j) → g x i = g x' i) →
    (∀ x i, N ≤ ρ i → g x i = 0) →
    ∃ e : (ι → E) ≃ᵐ (ι → E), (∀ x, e x = x + g x) ∧
      MeasurePreserving e (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  induction N with
  | zero =>
    intro g _ _ hsupp
    refine ⟨MeasurableEquiv.refl _, fun x => ?_, MeasurePreserving.id _⟩
    funext i
    simp [hsupp x i (Nat.zero_le _)]
  | succ N ih =>
    intro g hg hdep hsupp
    let S : ι → Prop := fun i => ρ i = N
    let g1 : (ι → E) → ι → E := fun x i => if ρ i = N then g x i else 0
    let g0 : (ι → E) → ι → E := fun x i => if ρ i < N then g x i else 0
    have hg1 : Measurable g1 := by
      refine measurable_pi_iff.2 fun i => ?_
      by_cases h : ρ i = N
      · simp only [g1, h, if_true]
        exact (measurable_pi_apply i).comp hg
      · simp only [g1, h, if_false]
        exact measurable_const
    have hg0 : Measurable g0 := by
      refine measurable_pi_iff.2 fun i => ?_
      by_cases h : ρ i < N
      · simp only [g0, h, if_true]
        exact (measurable_pi_apply i).comp hg
      · simp only [g0, h, if_false]
        exact measurable_const
    have hdep1 : ∀ x x', (∀ j, ¬ S j → x j = x' j) → g1 x = g1 x' := by
      intro x x' h
      funext i
      simp only [g1]
      split_ifs with hi
      · exact hdep i x x' fun j hj => h j (by simp only [S]; omega)
      · rfl
    have hsupp1 : ∀ x i, ¬ S i → g1 x i = 0 := by
      intro x i hi
      simp only [g1]
      rw [if_neg hi]
    obtain ⟨e0, he0, hm0⟩ := ih g0 hg0
      (by
        intro i x x' h
        simp only [g0]
        split_ifs with hi
        · exact hdep i x x' h
        · rfl)
      (by
        intro x i hi
        simp only [g0]
        rw [if_neg (not_lt.2 hi)])
    refine ⟨(skewEquiv S g1 hg1 hdep1 hsupp1).trans e0, fun x => ?_,
      (skew μ S g1 hg1 hdep1 hsupp1).trans hm0⟩
    rw [MeasurableEquiv.trans_apply, he0]
    have hskew : skewEquiv S g1 hg1 hdep1 hsupp1 x = x + g1 x := rfl
    rw [hskew]
    have h0 : g0 (x + g1 x) = g0 x := by
      funext i
      simp only [g0]
      split_ifs with hi
      · apply hdep i
        intro j hj
        simp only [Pi.add_apply, g1]
        rw [if_neg (by omega)]
        simp
      · rfl
    rw [h0]
    funext i
    simp only [Pi.add_apply, g0, g1]
    by_cases h1 : ρ i < N
    · rw [if_neg (by omega), if_pos h1]
      simp
    · by_cases h2 : ρ i = N
      · rw [if_pos h2, if_neg h1]
        simp
      · rw [if_neg h2, if_neg h1, hsupp x i (by omega)]
        simp

end

end Meas

/- English proof (translation)
Introduce `ι _ _ E _ _ _ _ _ _ μ _ _ ρ g hg hdep`. Conclude with `Meas.measurePreserving_of_card μ ρ (Finset.univ.sup ρ + 1) g hg hdep (fun x i h => absurd h (by`. Use `Finset.le_sup (f := ρ) (Finset.mem_univ i)` as an intermediate fact. Use the proof step `omega))`.
-/
theorem shear : TriangularShearMeasurePreserving := by
  intro ι _ _ E _ _ _ _ _ _ μ _ _ ρ g hg hdep
  exact Meas.measurePreserving_of_card μ ρ (Finset.univ.sup ρ + 1) g hg hdep (fun x i h => absurd h (by
    have := Finset.le_sup (f := ρ) (Finset.mem_univ i)
    omega))

/- English proof (translation)
Introduce `ι₁ ι₂ ι _ _ _ E _ μ _ e`. Use `⟨(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => E)).symm.trans (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e), ?_, ?_⟩` and prove the remaining obligations. Introduce `p i`. Take `⟨j, rfl⟩` from `e.surjective i`. Break down `j with a | b` into its components or cases.

Use `first`. Consider the case `simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]`. Consider the case `(simp only [MeasurableEquiv.trans_apply, Equiv.symm_apply_apply] rfl)`. Use `first`. Consider the case `simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]`.

Consider the case `(simp only [MeasurableEquiv.trans_apply, Equiv.symm_apply_apply] rfl)`. Use `first`. Consider the case `exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ => μ)).trans (measurePreserving_piCongrLeft (fun _ : ι => μ) e)`. Consider the case `exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ => μ)).trans (measurePreserving_piCongrLeft (fun _ => E) (fun _ : ι => μ) e)`. Consider the case `exact (MeasurePreserving.symm _ (measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => μ))).trans (measurePreserving_piCongrLeft (fun _ : ι => μ) e)`.
-/
theorem merge : CoordinateMergeMeasurable := by
  intro ι₁ ι₂ ι _ _ _ E _ μ _ e
  refine ⟨(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => E)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e), ?_, ?_⟩
  · intro p i
    obtain ⟨j, rfl⟩ := e.surjective i
    rcases j with a | b
    · first
        | simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, MeasurableEquiv.sumPiEquivProdPi,
            Equiv.sumPiEquivProdPi]
        | (simp only [MeasurableEquiv.trans_apply, Equiv.symm_apply_apply]
           rfl)
    · first
        | simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, MeasurableEquiv.sumPiEquivProdPi,
            Equiv.sumPiEquivProdPi]
        | (simp only [MeasurableEquiv.trans_apply, Equiv.symm_apply_apply]
           rfl)
  · first
      | exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ => μ)).trans
          (measurePreserving_piCongrLeft (fun _ : ι => μ) e)
      | exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ => μ)).trans
          (measurePreserving_piCongrLeft (fun _ => E) (fun _ : ι => μ) e)
      | exact (MeasurePreserving.symm _ (measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => μ))).trans
          (measurePreserving_piCongrLeft (fun _ : ι => μ) e)

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace F`. Use `isUniformAddGroup_of_addCommGroup (G := F)` as an intermediate fact. Set `: (Valued.v (R` to `F)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Establish `: ProperSpace F` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`. Use `open scoped Valued in`. Conclude with `inferInstance`.
-/
theorem sc_F (hF : IsNonarchimedeanLocalField F) : SecondCountableTopology F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  open scoped Valued in
  exact inferInstance

end Top

/- English proof (translation)
Use `hOK.loc` as an intermediate fact. Use `Top.sc_F hOK.loc` as an intermediate fact. Use `Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK` as an intermediate fact. Use `M.L.top` as an intermediate fact. Use `M.L.free` as an intermediate fact.

Use `Formalism.MainNotions.LocalModelPeriodLattices.finite_E M` as an intermediate fact. Set `e` to `(Module.Free.chooseBasis F E).equivFun`. Set `h : E ≃ₜ (Module.Free.ChooseBasisIndex F E → F)` to `{ e.toEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }`. Conclude with `h.secondCountableTopology`.
-/
theorem secondCountable_of_OK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (hOK : M.OK) : SecondCountableTopology E := by
  have := hOK.loc
  have := Top.sc_F hOK.loc
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := M.L.top
  have := M.L.free
  have := Formalism.MainNotions.LocalModelPeriodLattices.finite_E M
  let e := (Module.Free.chooseBasis F E).equivFun
  let h : E ≃ₜ (Module.Free.ChooseBasisIndex F E → F) :=
    { e.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact h.secondCountableTopology

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Grp

section Alg

variable {K : Type} [CommRing K] {n : ℕ}

/- English proof (translation)
Simplify using `[mk]`.
-/
theorem mk_diag (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) (a : Fin n) :
    mk P x a a = 1 := by
  simp [mk]

/- English proof (translation)
Simplify using `[mk, hne, h]`.
-/
theorem mk_pos (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hne : a ≠ b) (h : P (a, b)) : mk P x a b = x ⟨(a, b), h⟩ := by
  simp [mk, hne, h]

/- English proof (translation)
Simplify using `[mk, hne, h]`.
-/
theorem mk_neg (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hne : a ≠ b) (h : ¬ P (a, b)) : mk P x a b = 0 := by
  simp [mk, hne, h]

/- English proof (translation)
Take `⟨⟨a, b⟩, hp⟩` from `p`. Conclude with `mk_pos P x (hne _ hp) hp`.
-/
theorem mk_coord {P : Fin n × Fin n → Prop} [DecidablePred P] (hne : ∀ p, P p → p.1 ≠ p.2)
    (x : {p // P p} → K) (p : {p // P p}) : mk P x p.1.1 p.1.2 = x p := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  exact mk_pos P x (hne _ hp) hp

structure IsCoord (P : Fin n × Fin n → Prop) [DecidablePred P] (H : Subgroup (GL (Fin n) K)) :
    Prop where
  ne : ∀ p, P p → p.1 ≠ p.2
  det : ∀ x : {p // P p} → K, (mk P x).det = 1
  mem : ∀ g : GL (Fin n) K, g ∈ H ↔
    ∃ x : {p // P p} → K, (g : Matrix (Fin n) (Fin n) K) = mk P x

def toGL (P : Fin n × Fin n → Prop) [DecidablePred P]
    (hdet : ∀ x : {p // P p} → K, (mk P x).det = 1) (x : {p // P p} → K) : GL (Fin n) K :=
  ⟨mk P x, (mk P x).adjugate, by rw [Matrix.mul_adjugate, hdet, one_smul],
    by rw [Matrix.adjugate_mul, hdet, one_smul]⟩

def rk (p : Fin n × Fin n) : ℕ := ((p.1 : ℕ) - (p.2 : ℕ)) + ((p.2 : ℕ) - (p.1 : ℕ))

/- English proof (translation)
Take `⟨⟨a, b⟩, hi⟩` from `i`. Establish `hab : a < b` using `hP _ hi`. Use `show (g * mk P x) a b - x ⟨(a, b), hi⟩ = (g * mk P x') a b - x' ⟨(a, b), hi⟩`. Simplify using `only [Matrix.mul_apply]`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]`.

Rewrite using `[hg.2 a, one_mul, one_mul, mk_pos P x hab.ne hi, mk_pos P x' hab.ne hi]`. Simplify using `only [add_sub_cancel_left]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hca : c ≠ a` using `Finset.ne_of_mem_erase hc`. Break down `lt_or_gt_of_ne hca with hlt | hgt` into its components or cases.

Rewrite using `[show g a c = 0 from hg.1 hlt, zero_mul, zero_mul]`. Use `congr 1`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Rewrite using `[mk_diag, mk_diag]`.

Distinguish the cases in `hp : P (c, b)`. Rewrite using `[mk_pos P x hcb hp, mk_pos P x' hcb hp]`. Apply `h` to reduce the goal to its premises. Establish `h1 : (c : ℕ) < b` using `Fin.lt_def.1 (hP _ hp)`. Establish `h2 : (a : ℕ) < c` using `Fin.lt_def.1 hgt`.

Use `show rk (c, b) < rk (a, b)`. Simplify using `only [rk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mk_neg P x hcb hp, mk_neg P x' hcb hp]`.
-/
theorem dep_left {P : Fin n × Fin n → Prop} [DecidablePred P] (hP : ∀ p, P p → p.1 < p.2)
    (g : Matrix (Fin n) (Fin n) K) (hg : IsUpUni g) (i : {p // P p}) (x x' : {p // P p} → K)
    (h : ∀ j : {p // P p}, rk j.1 < rk i.1 → x j = x' j) :
    (g * mk P x) i.1.1 i.1.2 - x i = (g * mk P x') i.1.1 i.1.2 - x' i := by
  obtain ⟨⟨a, b⟩, hi⟩ := i
  have hab : a < b := hP _ hi
  show (g * mk P x) a b - x ⟨(a, b), hi⟩ = (g * mk P x') a b - x' ⟨(a, b), hi⟩
  simp only [Matrix.mul_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  rw [hg.2 a, one_mul, one_mul, mk_pos P x hab.ne hi, mk_pos P x' hab.ne hi]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hca : c ≠ a := Finset.ne_of_mem_erase hc
  rcases lt_or_gt_of_ne hca with hlt | hgt
  · rw [show g a c = 0 from hg.1 hlt, zero_mul, zero_mul]
  · congr 1
    by_cases hcb : c = b
    · subst hcb
      rw [mk_diag, mk_diag]
    · by_cases hp : P (c, b)
      · rw [mk_pos P x hcb hp, mk_pos P x' hcb hp]
        apply h
        have h1 : (c : ℕ) < b := Fin.lt_def.1 (hP _ hp)
        have h2 : (a : ℕ) < c := Fin.lt_def.1 hgt
        show rk (c, b) < rk (a, b)
        simp only [rk]
        omega
      · rw [mk_neg P x hcb hp, mk_neg P x' hcb hp]

/- English proof (translation)
Take `⟨⟨a, b⟩, hi⟩` from `i`. Establish `hab : b < a` using `hP _ hi`. Use `show (mk P x * g) a b - x ⟨(a, b), hi⟩ = (mk P x' * g) a b - x' ⟨(a, b), hi⟩`. Simplify using `only [Matrix.mul_apply]`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]`.

Rewrite using `[hg.2 b, mul_one, mul_one, mk_pos P x hab.ne' hi, mk_pos P x' hab.ne' hi]`. Simplify using `only [add_sub_cancel_left]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hcb : c ≠ b` using `Finset.ne_of_mem_erase hc`. Break down `lt_or_gt_of_ne hcb with hlt | hgt` into its components or cases.

Rewrite using `[show g c b = 0 from hg.1 hlt, mul_zero, mul_zero]`. Use `congr 1`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Rewrite using `[mk_diag, mk_diag]`.

Distinguish the cases in `hp : P (a, c)`. Rewrite using `[mk_pos P x hac hp, mk_pos P x' hac hp]`. Apply `h` to reduce the goal to its premises. Establish `h1 : (c : ℕ) < a` using `Fin.lt_def.1 (hP _ hp)`. Establish `h2 : (b : ℕ) < c` using `Fin.lt_def.1 hgt`.

Use `show rk (a, c) < rk (a, b)`. Simplify using `only [rk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mk_neg P x hac hp, mk_neg P x' hac hp]`.
-/
theorem dep_right {P : Fin n × Fin n → Prop} [DecidablePred P] (hP : ∀ p, P p → p.2 < p.1)
    (g : Matrix (Fin n) (Fin n) K) (hg : IsLowUni g) (i : {p // P p}) (x x' : {p // P p} → K)
    (h : ∀ j : {p // P p}, rk j.1 < rk i.1 → x j = x' j) :
    (mk P x * g) i.1.1 i.1.2 - x i = (mk P x' * g) i.1.1 i.1.2 - x' i := by
  obtain ⟨⟨a, b⟩, hi⟩ := i
  have hab : b < a := hP _ hi
  show (mk P x * g) a b - x ⟨(a, b), hi⟩ = (mk P x' * g) a b - x' ⟨(a, b), hi⟩
  simp only [Matrix.mul_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  rw [hg.2 b, mul_one, mul_one, mk_pos P x hab.ne' hi, mk_pos P x' hab.ne' hi]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcb : c ≠ b := Finset.ne_of_mem_erase hc
  rcases lt_or_gt_of_ne hcb with hlt | hgt
  · rw [show g c b = 0 from hg.1 hlt, mul_zero, mul_zero]
  · congr 1
    by_cases hac : a = c
    · subst hac
      rw [mk_diag, mk_diag]
    · by_cases hp : P (a, c)
      · rw [mk_pos P x hac hp, mk_pos P x' hac hp]
        apply h
        have h1 : (c : ℕ) < a := Fin.lt_def.1 (hP _ hp)
        have h2 : (b : ℕ) < c := Fin.lt_def.1 hgt
        show rk (a, c) < rk (a, b)
        simp only [rk]
        omega
      · rw [mk_neg P x hac hp, mk_neg P x' hac hp]

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_diag P x⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Conclude with `mk_neg P x hij'.ne' (fun hp => lt_asymm hij' (hP (i, j) hp))`.
-/
theorem isUpUni_mk {P : Fin n × Fin n → Prop} [DecidablePred P] (hP : ∀ p, P p → p.1 < p.2)
    (x : {p // P p} → K) : IsUpUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_diag P x⟩
  have hij' : j < i := hij
  exact mk_neg P x hij'.ne' (fun hp => lt_asymm hij' (hP (i, j) hp))

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_diag P x⟩` and prove the remaining obligations. Establish `hij' : i < j` using `hij`. Conclude with `mk_neg P x hij'.ne (fun hp => lt_asymm hij' (hP (i, j) hp))`.
-/
theorem isLowUni_mk {P : Fin n × Fin n → Prop} [DecidablePred P] (hP : ∀ p, P p → p.2 < p.1)
    (x : {p // P p} → K) : IsLowUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_diag P x⟩
  have hij' : i < j := hij
  exact mk_neg P x hij'.ne (fun hp => lt_asymm hij' (hP (i, j) hp))

/- English proof (translation)
The claim follows from `ne_of_lt hp det x := isUpUni_det K (isUpUni_mk (fun _ hp => hp) x) mem g := by constructor · intro hg have hg' : IsUpUni (g : Matrix (Fin n) (Fin n) K) := hg refine ⟨fun p => (g : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2, ?_⟩ ext a b by_cases hab : a = b · subst hab; rw [mk_diag, hg …`.
-/
theorem isCoord_up (n : ℕ) : IsCoord (K := K) (PU n) (upUniG K n) where
  ne p hp := ne_of_lt hp
  det x := isUpUni_det K (isUpUni_mk (fun _ hp => hp) x)
  mem g := by
    constructor
    · intro hg
      have hg' : IsUpUni (g : Matrix (Fin n) (Fin n) K) := hg
      refine ⟨fun p => (g : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2, ?_⟩
      ext a b
      by_cases hab : a = b
      · subst hab; rw [mk_diag, hg'.2]
      · by_cases hp : PU n (a, b)
        · rw [mk_pos _ _ hab hp]
        · rw [mk_neg _ _ hab hp]
          exact Formalism.DoubleCosetMeasures.P.Phase.up_zero hg' (lt_of_le_of_ne (not_lt.1 hp) (Ne.symm hab))
    · rintro ⟨x, hx⟩
      show IsUpUni (g : Matrix (Fin n) (Fin n) K)
      rw [hx]
      exact isUpUni_mk (fun _ hp => hp) x

/- English proof (translation)
The claim follows from `ne_of_gt hp.1 det x := isLowUni_det K (isLowUni_mk (fun _ hp => hp.1) x) mem g := by rw [Formalism.DoubleCosetMeasures.P.Supp.mem_lowW_iff s t (Formalism.DoubleCosetMeasures.P.Phase.ptI s t) (Formalism.DoubleCosetMeasures.P.Phase.ptI_mul_pt s t) (Formalism.DoubleCosetMeasures.P.P …`.
-/
theorem isCoord_low (s : List ℕ) (t : ℕ → Kˣ) (sb : Fin s.sum → Fin s.sum → Bool)
    (hsb : ∀ a b, sb a b = true ↔ blk s a = blk s b) :
    IsCoord (K := K) (PW sb) (lowW K s t) where
  ne p hp := ne_of_gt hp.1
  det x := isLowUni_det K (isLowUni_mk (fun _ hp => hp.1) x)
  mem g := by
    rw [Formalism.DoubleCosetMeasures.P.Supp.mem_lowW_iff s t (Formalism.DoubleCosetMeasures.P.Phase.ptI s t) (Formalism.DoubleCosetMeasures.P.Phase.ptI_mul_pt s t)
      (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI s t) g]
    constructor
    · rintro ⟨hg, hc⟩
      refine ⟨fun p => (g : Matrix (Fin s.sum) (Fin s.sum) K) p.1.1 p.1.2, ?_⟩
      ext a b
      by_cases hab : a = b
      · subst hab; rw [mk_diag, hg.2]
      · by_cases hp : PW sb (a, b)
        · rw [mk_pos _ _ hab hp]
        · rw [mk_neg _ _ hab hp]
          rcases lt_or_gt_of_ne hab with h1 | h1
          · exact Formalism.DoubleCosetMeasures.P.Phase.low_zero hg h1
          · have hs : sb a b = true := by
              by_contra hcon
              exact hp ⟨h1, by simpa using hcon⟩
            have hb : blk s b = blk s a := ((hsb a b).1 hs).symm
            have hlt := Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_eq s hb h1
            have h0 := Formalism.DoubleCosetMeasures.P.Phase.low_zero hc hlt
            rw [Formalism.DoubleCosetMeasures.P.Phase.conj_apply, Formalism.DoubleCosetMeasures.P.Phase.revF_revF,
              Formalism.DoubleCosetMeasures.P.Phase.revF_revF] at h0
            have h2 := (Units.mul_left_eq_zero _).1 h0
            exact (Units.mul_right_eq_zero _).1 h2
    · rintro ⟨x, hx⟩
      have hl : IsLowUni (mk (PW sb) x) := isLowUni_mk (fun _ hp => hp.1) x
      rw [hx]
      refine ⟨hl, fun a c hac => ?_, fun a => ?_⟩
      · have hac' : a < c := by simpa using hac
        rw [Formalism.DoubleCosetMeasures.P.Phase.conj_apply]
        have h0 : mk (PW sb) x (Formalism.DoubleCosetMeasures.P.Phase.revF s a) (Formalism.DoubleCosetMeasures.P.Phase.revF s c) = 0 := by
          by_cases hb : blk s a = blk s c
          · refine mk_neg _ _ (fun e => ne_of_lt hac' (Formalism.DoubleCosetMeasures.P.Phase.revF_inj s e)) ?_
            rintro ⟨_, h2⟩
            have : sb (Formalism.DoubleCosetMeasures.P.Phase.revF s a) (Formalism.DoubleCosetMeasures.P.Phase.revF s c) = true := by
              rw [hsb, Formalism.DoubleCosetMeasures.P.Phase.blk_revF, Formalism.DoubleCosetMeasures.P.Phase.blk_revF]; exact hb
            simp only at h2
            rw [this] at h2
            exact absurd h2 (by decide)
          · exact Formalism.DoubleCosetMeasures.P.Phase.low_zero hl (Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_lt s
              (Formalism.DoubleCosetMeasures.P.Phase.blk_lt_of_lt_of_ne s hac' hb))
        rw [h0]; simp
      · rw [Formalism.DoubleCosetMeasures.P.Phase.conj_apply, hl.2]; simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨⟨a, b⟩, hp⟩`. Use `h a b` as an intermediate fact. Rewrite `this` using `[mk_pos P x (hne _ hp) hp]`. Then use the resulting hypothesis. Introduce `h a b`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[mk_diag]`. Conclude with `R.one_mem`. Distinguish the cases in `hp : P (a, b)`.

Rewrite using `[mk_pos P x hab hp]`. Conclude with `h _`. Rewrite using `[mk_neg P x hab hp]`. Conclude with `R.zero_mem`.
-/
theorem isInt_mk_iff {P : Fin n × Fin n → Prop} [DecidablePred P] (hne : ∀ p, P p → p.1 ≠ p.2)
    (R : Subring K) (x : {p // P p} → K) : IsInt R (mk P x) ↔ ∀ p, x p ∈ R := by
  constructor
  · rintro h ⟨⟨a, b⟩, hp⟩
    have := h a b
    rwa [mk_pos P x (hne _ hp) hp] at this
  · intro h a b
    by_cases hab : a = b
    · subst hab
      rw [mk_diag]
      exact R.one_mem
    · by_cases hp : P (a, b)
      · rw [mk_pos P x hab hp]
        exact h _
      · rw [mk_neg P x hab hp]
        exact R.zero_mem

end Alg

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [mk]`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`.
-/
theorem continuous_mk (P : Fin n × Fin n → Prop) [DecidablePred P] :
    Continuous (mk (K := K) P) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [mk]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

def homeo {P : Fin n × Fin n → Prop} [DecidablePred P] {H : Subgroup (GL (Fin n) K)}
    (hc : IsCoord P H) : ({p // P p} → K) ≃ₜ H where
  toFun x := ⟨toGL P hc.det x, (hc.mem _).2 ⟨x, rfl⟩⟩
  invFun g := fun p => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  left_inv x := by
    funext p
    exact mk_coord hc.ne x p
  right_inv g := by
    obtain ⟨x, hx⟩ := (hc.mem g.1).1 g.2
    apply Subtype.ext
    apply Units.ext
    show mk P (fun p : {p // P p} => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hx]
    congr 1
    funext p
    exact mk_coord hc.ne x p
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    rw [Units.continuous_iff]
    exact ⟨continuous_mk P, (continuous_mk P).matrix_adjugate⟩
  continuous_invFun := by
    refine continuous_pi fun p => ?_
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

end Top

section Meas

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}

/- English proof (translation)
Take `⟨e, he, hmp⟩` from `hS ι K μ ρ (fun x => T x - x) ((hT.sub continuous_id).measurable) (fun i x x' h => hdep i x x' h)`. Establish `hTe : T = e`. Use function extensionality and compare the values at `x`. Simplify using `only [he x]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hTe]`. Conclude with `hmp.map_eq`.
-/
theorem map_eq_of_shear (hS : TriangularShearMeasurePreserving) (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → ℕ) (T : (ι → K) → (ι → K)) (hT : Continuous T)
    (hdep : ∀ i x x', (∀ j, ρ j < ρ i → x j = x' j) → T x i - x i = T x' i - x' i) :
    Measure.map T (Measure.pi fun _ : ι => μ) = Measure.pi fun _ : ι => μ := by
  obtain ⟨e, he, hmp⟩ := hS ι K μ ρ (fun x => T x - x) ((hT.sub continuous_id).measurable)
    (fun i x x' h => hdep i x x' h)
  have hTe : T = e := by
    funext x
    simp only [he x]
    abel
  rw [hTe]
  exact hmp.map_eq

def meas {P : Fin n × Fin n → Prop} [DecidablePred P] {H : Subgroup (GL (Fin n) K)}
    (hc : IsCoord P H) (μ : Measure K) : Measure H :=
  (Measure.pi fun _ : {p // P p} => μ).map (homeo hc).toMeasurableEquiv

/- English proof (translation)
Establish `hT : Continuous (fun x => (homeo hc).symm (f (homeo hc x)))` using `(homeo hc).symm.continuous.comp (hf.comp (homeo hc).continuous)`. Establish `hmap` using `map_eq_of_shear hS μ (fun j : {p // P p} => rk j.1) (fun x => (homeo hc).symm (f (homeo hc x))) hT (fun i x x' h => hdep i x x' h)`. Unfold `meas`. Rewrite using `[Measure.map_map hf.measurable (homeo hc).toMeasurableEquiv.measurable]`. Establish `e1 : f ∘ (homeo hc).toMeasurableEquiv = (homeo hc).toMeasurableEquiv ∘ (fun x => (homeo hc).symm (f (homeo hc x)))`.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[e1, ← Measure.map_map (homeo hc).toMeasurableEquiv.measurable hT.measurable, hmap]`.
-/
theorem meas_map_of {P : Fin n × Fin n → Prop} [DecidablePred P] {H : Subgroup (GL (Fin n) K)}
    (hc : IsCoord P H) (hS : TriangularShearMeasurePreserving) (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (f : H → H) (hf : Continuous f)
    (hdep : ∀ (i : {p // P p}) (x x' : {p // P p} → K), (∀ j : {p // P p}, rk j.1 < rk i.1 → x j = x' j) →
      ((f (homeo hc x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i.1.1 i.1.2 - x i =
        ((f (homeo hc x') : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i.1.1 i.1.2 - x' i) :
    Measure.map f (meas hc μ) = meas hc μ := by
  have hT : Continuous (fun x => (homeo hc).symm (f (homeo hc x))) :=
    (homeo hc).symm.continuous.comp (hf.comp (homeo hc).continuous)
  have hmap := map_eq_of_shear hS μ (fun j : {p // P p} => rk j.1) (fun x => (homeo hc).symm (f (homeo hc x))) hT
    (fun i x x' h => hdep i x x' h)
  unfold meas
  rw [Measure.map_map hf.measurable (homeo hc).toMeasurableEquiv.measurable]
  have e1 : f ∘ (homeo hc).toMeasurableEquiv =
      (homeo hc).toMeasurableEquiv ∘ (fun x => (homeo hc).symm (f (homeo hc x))) := by
    funext x
    simp
  rw [e1, ← Measure.map_map (homeo hc).toMeasurableEquiv.measurable hT.measurable, hmap]

/- English proof (translation)
Unfold `meas`. Rewrite using `[MeasurableEquiv.map_apply]`. Establish `key : ∀ x : {p // P p} → K, (homeo hc).toMeasurableEquiv x ∈ intSub R H ↔ ∀ p, x p ∈ R`. Introduce `x`. Use `show (IsInt R (mk P x) ∧ IsInt R (mk P x).adjugate) ↔ ∀ p, x p ∈ R`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _⟩`. Conclude with `(isInt_mk_iff hc.ne R x).1 h1`. Introduce `h`. Establish `h1 : IsInt R (mk P x)` using `(isInt_mk_iff hc.ne R x).2 h`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce `i j`. Set `a' : Matrix (Fin n) (Fin n) R` to `fun i j => ⟨mk P x i j, h1 i j⟩`. Establish `e2 : mk P x = R.subtype.mapMatrix a'`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[e2, ← RingHom.map_adjugate]`. Conclude with `(a'.adjugate i j).2`. Establish `e : (homeo hc).toMeasurableEquiv ⁻¹' (intSub R H : Set H) = Set.univ.pi fun _ => (R : Set K)`. Use extensionality with `x`.

Conclude with `(key x).trans ⟨fun h p _ => h p, fun h p => h p (Set.mem_univ p)⟩`. Rewrite using `[e, Measure.pi_pi]`. Simplify using `[hR]`.
-/
theorem meas_int {P : Fin n × Fin n → Prop} [DecidablePred P] {H : Subgroup (GL (Fin n) K)}
    (hc : IsCoord P H) (μ : Measure K) [SigmaFinite μ] (R : Subring K) (hR : μ (R : Set K) = 1) :
    meas hc μ (intSub R H : Set H) = 1 := by
  unfold meas
  rw [MeasurableEquiv.map_apply]
  have key : ∀ x : {p // P p} → K, (homeo hc).toMeasurableEquiv x ∈ intSub R H ↔ ∀ p, x p ∈ R := by
    intro x
    show (IsInt R (mk P x) ∧ IsInt R (mk P x).adjugate) ↔ ∀ p, x p ∈ R
    constructor
    · rintro ⟨h1, _⟩
      exact (isInt_mk_iff hc.ne R x).1 h1
    · intro h
      have h1 : IsInt R (mk P x) := (isInt_mk_iff hc.ne R x).2 h
      refine ⟨h1, ?_⟩
      intro i j
      let a' : Matrix (Fin n) (Fin n) R := fun i j => ⟨mk P x i j, h1 i j⟩
      have e2 : mk P x = R.subtype.mapMatrix a' := by
        ext i j
        rfl
      rw [e2, ← RingHom.map_adjugate]
      exact (a'.adjugate i j).2
  have e : (homeo hc).toMeasurableEquiv ⁻¹' (intSub R H : Set H) = Set.univ.pi fun _ => (R : Set K) := by
    ext x
    exact (key x).trans ⟨fun h p _ => h p, fun h p => h p (Set.mem_univ p)⟩
  rw [e, Measure.pi_pi]
  simp [hR]

end Meas

end Grp

/- English proof (translation)
Introduce `K _ _ _ _ _ _ μ _ _ R hR s t sb hsb`. Establish `hcL` using `Grp.isCoord_low (K := K) s t sb hsb`. Establish `hcU` using `Grp.isCoord_up (K := K) s.sum`. Use `haveI : SFinite (Grp.meas hcL μ) := by first`. Consider the case `(unfold Grp.meas infer_instance)`.

Consider the case `exact inferInstanceAs (SFinite ((Measure.pi fun _ => μ).map (Grp.homeo hcL).toMeasurableEquiv))`. Use `haveI : SFinite (Grp.meas hcU μ) := by first`. Consider the case `(unfold Grp.meas infer_instance)`. Consider the case `exact inferInstanceAs (SFinite ((Measure.pi fun _ => μ).map (Grp.homeo hcU).toMeasurableEquiv))`. Use `⟨Grp.meas hcL μ, Grp.meas hcU μ, ⟨fun g => ?_⟩, ⟨fun g => ?_⟩, inferInstance, inferInstance, Grp.meas_int hcL μ R hR, Grp.meas_int hcU μ R hR, fun G => ?_⟩` and prove the remaining obligations.

Conclude with `Grp.meas_map_of hcL hS μ (· * g) (continuous_mul_right g) (fun i x x' h => Grp.dep_right (P := PW sb) (fun p hp => hp.1) _ g.2.1 i x x' h)`. Conclude with `Grp.meas_map_of hcU hS μ (g * ·) (continuous_mul_left g) (fun i x x' h => Grp.dep_left (P := PU s.sum) (fun p hp => hp) _ g.2 i x x' h)`. Establish `h1 : MeasurePreserving (Grp.homeo hcL).toMeasurableEquiv (Measure.pi fun _ => μ) (Grp.meas hcL μ)` using `⟨(Grp.homeo hcL).toMeasurableEquiv.measurable, rfl⟩`. Establish `h2 : MeasurePreserving (Grp.homeo hcU).toMeasurableEquiv (Measure.pi fun _ => μ) (Grp.meas hcU μ)` using `⟨(Grp.homeo hcU).toMeasurableEquiv.measurable, rfl⟩`. Establish `h3` using `h1.prod h2`.

Rewrite using `[← h3.integral_comp' (f := (Grp.homeo hcL).toMeasurableEquiv.prodCongr (Grp.homeo hcU).toMeasurableEquiv)]`. Both sides reduce to the same expression.
-/
theorem grp (hS : TriangularShearMeasurePreserving) : UnipotentProductMeasureInvariant := by
  intro K _ _ _ _ _ _ μ _ _ R hR s t sb hsb
  have hcL := Grp.isCoord_low (K := K) s t sb hsb
  have hcU := Grp.isCoord_up (K := K) s.sum
  haveI : SFinite (Grp.meas hcL μ) := by
    first
      | (unfold Grp.meas
         infer_instance)
      | exact inferInstanceAs (SFinite ((Measure.pi fun _ => μ).map (Grp.homeo hcL).toMeasurableEquiv))
  haveI : SFinite (Grp.meas hcU μ) := by
    first
      | (unfold Grp.meas
         infer_instance)
      | exact inferInstanceAs (SFinite ((Measure.pi fun _ => μ).map (Grp.homeo hcU).toMeasurableEquiv))
  refine ⟨Grp.meas hcL μ, Grp.meas hcU μ, ⟨fun g => ?_⟩, ⟨fun g => ?_⟩, inferInstance, inferInstance,
    Grp.meas_int hcL μ R hR, Grp.meas_int hcU μ R hR, fun G => ?_⟩
  · exact Grp.meas_map_of hcL hS μ (· * g) (continuous_mul_right g)
      (fun i x x' h => Grp.dep_right (P := PW sb) (fun p hp => hp.1) _ g.2.1 i x x' h)
  · exact Grp.meas_map_of hcU hS μ (g * ·) (continuous_mul_left g)
      (fun i x x' h => Grp.dep_left (P := PU s.sum) (fun p hp => hp) _ g.2 i x x' h)
  · have h1 : MeasurePreserving (Grp.homeo hcL).toMeasurableEquiv (Measure.pi fun _ => μ) (Grp.meas hcL μ) :=
      ⟨(Grp.homeo hcL).toMeasurableEquiv.measurable, rfl⟩
    have h2 : MeasurePreserving (Grp.homeo hcU).toMeasurableEquiv (Measure.pi fun _ => μ) (Grp.meas hcU μ) :=
      ⟨(Grp.homeo hcU).toMeasurableEquiv.measurable, rfl⟩
    have h3 := h1.prod h2
    rw [← h3.integral_comp' (f := (Grp.homeo hcL).toMeasurableEquiv.prodCongr (Grp.homeo hcU).toMeasurableEquiv)]
    rfl

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Dec

section Alg

variable {K : Type} [CommRing K] {n : ℕ}

def rk (p : Fin n × Fin n) : ℕ := ((p.1 : ℕ) - (p.2 : ℕ)) + ((p.2 : ℕ) - (p.1 : ℕ))

structure Tri (P : Fin n × Fin n → Prop) : Prop where
  irr : ∀ a, ¬ P (a, a)
  trans : ∀ a c b, P (a, c) → P (c, b) → P (a, b)
  rk1 : ∀ a c b, P (a, c) → P (c, b) → rk (a, c) < rk (a, b)
  rk2 : ∀ a c b, P (a, c) → P (c, b) → rk (c, b) < rk (a, b)

/- English proof (translation)
The claim follows from `lt_irrefl a trans a c b h1 h2 := lt_trans h2 h1 rk1 a c b h1 h2 := by have h1' : (c : ℕ) < a := h1 have h2' : (b : ℕ) < c := h2 simp only [rk]; omega rk2 a c b h1 h2 := by have h1' : (c : ℕ) < a := h1 have h2' : (b : ℕ) < c := h2 simp only [rk]; omega`.
-/
theorem tri_PL : Tri (PL n) where
  irr a := lt_irrefl a
  trans a c b h1 h2 := lt_trans h2 h1
  rk1 a c b h1 h2 := by
    have h1' : (c : ℕ) < a := h1
    have h2' : (b : ℕ) < c := h2
    simp only [rk]; omega
  rk2 a c b h1 h2 := by
    have h1' : (c : ℕ) < a := h1
    have h2' : (b : ℕ) < c := h2
    simp only [rk]; omega

/- English proof (translation)
The claim follows from `lt_irrefl a trans a c b h1 h2 := lt_trans h1 h2 rk1 a c b h1 h2 := by have h1' : (a : ℕ) < c := h1 have h2' : (c : ℕ) < b := h2 simp only [rk]; omega rk2 a c b h1 h2 := by have h1' : (a : ℕ) < c := h1 have h2' : (c : ℕ) < b := h2 simp only [rk]; omega`.
-/
theorem tri_PU : Tri (PU n) where
  irr a := lt_irrefl a
  trans a c b h1 h2 := lt_trans h1 h2
  rk1 a c b h1 h2 := by
    have h1' : (a : ℕ) < c := h1
    have h2' : (c : ℕ) < b := h2
    simp only [rk]; omega
  rk2 a c b h1 h2 := by
    have h1' : (a : ℕ) < c := h1
    have h2' : (c : ℕ) < b := h2
    simp only [rk]; omega

/- English proof (translation)
Simplify using `[mk]`.
-/
theorem mk_self (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) (a : Fin n) :
    mk P x a a = 1 := by
  simp [mk]

/- English proof (translation)
Simplify using `[mk, hab, h]`.
-/
theorem mk_of (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hab : a ≠ b) (h : P (a, b)) : mk P x a b = x ⟨(a, b), h⟩ := by
  simp [mk, hab, h]

/- English proof (translation)
Simplify using `[mk, hab, h]`.
-/
theorem mk_zero (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hab : a ≠ b) (h : ¬ P (a, b)) : mk P x a b = 0 := by
  simp [mk, hab, h]

variable {P Q₁ Q₂ : Fin n × Fin n → Prop} [DecidablePred P] [DecidablePred Q₁] [DecidablePred Q₂]

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `hP.irr a h`.
-/
theorem Tri.ne (hP : Tri P) {a b : Fin n} (h : P (a, b)) : a ≠ b := by
  rintro rfl
  exact hP.irr a h

/- English proof (translation)
Rewrite `h` using `[not_and_or]`. Break down `h with h | h` into its components or cases. Rewrite `h` using `[not_or]`. Rewrite using `[mk_zero Q₁ x h.1 (fun hq => h.2 (h₁ _ hq)), zero_mul]`. Rewrite `h` using `[not_or]`.

Rewrite using `[mk_zero Q₂ y h.1 (fun hq => h.2 (h₂ _ hq)), mul_zero]`.
-/
theorem term_zero (h₁ : ∀ p, Q₁ p → P p) (h₂ : ∀ p, Q₂ p → P p)
    (x : {p // Q₁ p} → K) (y : {p // Q₂ p} → K) {a b c : Fin n}
    (h : ¬ ((a = c ∨ P (a, c)) ∧ (c = b ∨ P (c, b)))) : mk Q₁ x a c * mk Q₂ y c b = 0 := by
  rw [not_and_or] at h
  rcases h with h | h
  · rw [not_or] at h
    rw [mk_zero Q₁ x h.1 (fun hq => h.2 (h₁ _ hq)), zero_mul]
  · rw [not_or] at h
    rw [mk_zero Q₂ y h.1 (fun hq => h.2 (h₂ _ hq)), mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[mk_self, mk_self, one_mul]`. Introduce `c _ hc`. Apply `term_zero h₁ h₂` to reduce the goal to its premises. Introduce and unpack `⟨h1 | h1, h2 | h2⟩`.

Conclude with `hc h1.symm`. Conclude with `hc h1.symm`. Conclude with `hc h2`. Conclude with `hP.irr a (hP.trans a c a h1 h2)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem mul_diag (hP : Tri P) (h₁ : ∀ p, Q₁ p → P p) (h₂ : ∀ p, Q₂ p → P p)
    (x : {p // Q₁ p} → K) (y : {p // Q₂ p} → K) (a : Fin n) :
    (mk Q₁ x * mk Q₂ y) a a = 1 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [mk_self, mk_self, one_mul]
  · intro c _ hc
    apply term_zero h₁ h₂
    rintro ⟨h1 | h1, h2 | h2⟩
    · exact hc h1.symm
    · exact hc h1.symm
    · exact hc h2
    · exact hP.irr a (hP.trans a c a h1 h2)
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => term_zero h₁ h₂ x y ?_` and prove the remaining obligations. Introduce and unpack `⟨rfl | h1, rfl | h2⟩`. Conclude with `hab rfl`. Conclude with `h h2`.

Conclude with `h h1`. Conclude with `h (hP.trans a c b h1 h2)`.
-/
theorem mul_off (hP : Tri P) (h₁ : ∀ p, Q₁ p → P p) (h₂ : ∀ p, Q₂ p → P p)
    (x : {p // Q₁ p} → K) (y : {p // Q₂ p} → K) {a b : Fin n} (hab : a ≠ b) (h : ¬ P (a, b)) :
    (mk Q₁ x * mk Q₂ y) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => term_zero h₁ h₂ x y ?_
  rintro ⟨rfl | h1, rfl | h2⟩
  · exact hab rfl
  · exact h h2
  · exact h h1
  · exact h (hP.trans a c b h1 h2)

def rest (x : {p // Q₁ p} → K) (y : {p // Q₂ p} → K) (a b : Fin n) : K :=
  ∑ c ∈ (Finset.univ.erase a).erase b, mk Q₁ x a c * mk Q₂ y c b

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)]`. Rewrite using `[mk_self, mk_self, one_mul, mul_one, rest]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_on (x : {p // Q₁ p} → K) (y : {p // Q₂ p} → K) {a b : Fin n} (hab : a ≠ b) :
    (mk Q₁ x * mk Q₂ y) a b = mk Q₁ x a b + mk Q₂ y a b + rest x y a b := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)]
  rw [mk_self, mk_self, one_mul, mul_one, rest]
  ring

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[mk_self, h1]`. Distinguish the cases in `h : P (a, b)`.

Rewrite using `[mk_of P _ hab h]`. Rewrite using `[mk_zero P _ hab h, h0 a b hab h]`.
-/
theorem mk_coords (X : Matrix (Fin n) (Fin n) K) (h1 : ∀ a, X a a = 1)
    (h0 : ∀ a b, a ≠ b → ¬ P (a, b) → X a b = 0) : mk P (fun p => X p.1.1 p.1.2) = X := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [mk_self, h1]
  · by_cases h : P (a, b)
    · rw [mk_of P _ hab h]
    · rw [mk_zero P _ hab h, h0 a b hab h]

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_self P x⟩` and prove the remaining obligations. Establish `hij' : i < j` using `hij`. Conclude with `mk_zero P x hij'.ne (fun hp => lt_asymm hij' (h _ hp))`.
-/
theorem isLowUni_mk (h : ∀ p, P p → PL n p) (x : {p // P p} → K) : IsLowUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_self P x⟩
  have hij' : i < j := hij
  exact mk_zero P x hij'.ne (fun hp => lt_asymm hij' (h _ hp))

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_self P x⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Conclude with `mk_zero P x hij'.ne' (fun hp => lt_asymm hij' (h _ hp))`.
-/
theorem isUpUni_mk (h : ∀ p, P p → PU n p) (x : {p // P p} → K) : IsUpUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_self P x⟩
  have hij' : j < i := hij
  exact mk_zero P x hij'.ne' (fun hp => lt_asymm hij' (h _ hp))

end Alg

section Meas

variable {K : Type} [CommRing K] {n : ℕ}
variable {P Q₁ Q₂ : Fin n × Fin n → Prop} [DecidablePred P] [DecidablePred Q₁] [DecidablePred Q₂]

def res (h : ∀ p, Q₁ p → P p) (z : {p // P p} → K) : {p // Q₁ p} → K :=
  fun q => z ⟨q.1, h q.1 q.2⟩

/- English proof (translation)
Simplify using `only [mk]`. Use `split_ifs with h1 h2`. Conclude with `measurable_const`. Conclude with `measurable_pi_apply _`. Conclude with `measurable_const`.
-/
theorem measurable_entry [MeasurableSpace K] (h : ∀ p, Q₁ p → P p) (a c : Fin n) :
    Measurable (fun z : {p // P p} → K => mk Q₁ (res h z) a c) := by
  simp only [mk]
  split_ifs with h1 h2
  · exact measurable_const
  · exact measurable_pi_apply _
  · exact measurable_const

def splitEquiv (h₁ : ∀ p, Q₁ p → P p) (h₂ : ∀ p, Q₂ p → P p) (hor : ∀ p, P p → Q₁ p ∨ Q₂ p)
    (hd : ∀ p, Q₁ p → ¬ Q₂ p) : {p // Q₁ p} ⊕ {p // Q₂ p} ≃ {p // P p} where
  toFun := Sum.elim (fun q => ⟨q.1, h₁ _ q.2⟩) (fun q => ⟨q.1, h₂ _ q.2⟩)
  invFun p := if h : Q₁ p.1 then Sum.inl ⟨p.1, h⟩ else Sum.inr ⟨p.1, (hor _ p.2).resolve_left h⟩
  left_inv := by
    rintro (q | q)
    · simp [q.2]
    · have : ¬ Q₁ q.1 := fun h => hd _ h q.2
      simp [this]
  right_inv := by
    intro p
    by_cases h : Q₁ p.1 <;> simp [h]

/- English proof (translation)
Take `⟨m, hm, hmm⟩` from `hM {p // Q₁ p} {p // Q₂ p} {p // P p} K μ (splitEquiv h₁ h₂ hor hd)`. Set `T : ({p // P p} → K) → ({p // P p} → K)` to `fun z p => (mk Q₁ (res h₁ z) * mk Q₂ (res h₂ z)) p.1.1 p.1.2`. Establish `hT : Measurable T`. Use `measurable_pi_iff.2 fun p => ?_` and prove the remaining obligations. Simplify using `only [T, Matrix.mul_apply]`.

Use `first`. Consider the case `exact Finset.measurable_sum _ fun c _ => (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2)`. Consider the case `exact Finset.measurable_sum' _ fun c _ => (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2)`. Consider the case `(apply Finset.measurable_sum`. Introduce `c _`.

Apply the tactic sequence `exact (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2))`. Establish `hsum : ∀ (z : {p // P p} → K) (a b : Fin n) (hp : P (a, b)), mk Q₁ (res h₁ z) a b + mk Q₂ (res h₂ z) a b = z ⟨(a, b), hp⟩`. Introduce `z a b hp`. Establish `hab : a ≠ b` using `hP.ne hp`. Break down `hor _ hp with hq | hq` into its components or cases.

Apply the tactic sequence `rw [mk_of Q₁ _ hab hq, mk_zero Q₂ _ hab (hd _ hq), add_zero] try rfl`. Apply the tactic sequence `rw [mk_zero Q₁ _ hab (fun h => hd _ h hq), mk_of Q₂ _ hab hq, zero_add] try rfl`. Establish `hrest : ∀ (z : {p // P p} → K) (a b : Fin n) (hp : P (a, b)), T z ⟨(a, b), hp⟩ - z ⟨(a, b), hp⟩ = rest (res h₁ z) (res h₂ z) a b`. Introduce `z a b hp`. Establish `hab : a ≠ b` using `hP.ne hp`.

Use `show (mk Q₁ (res h₁ z) * mk Q₂ (res h₂ z)) a b - z ⟨(a, b), hp⟩ = _`. Rewrite using `[mul_on _ _ hab, ← hsum z a b hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdep : ∀ (i : {p // P p}) (z z' : {p // P p} → K), (∀ j : {p // P p}, rk j.1 < rk i.1 → z j = z' j) → T z i - z i = T z' i - z' i`. Introduce and unpack `⟨⟨a, b⟩, hp⟩ z z' h`.

Rewrite using `[hrest z a b hp, hrest z' a b hp]`. Unfold `rest`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hcb : c ≠ b` using `(Finset.mem_erase.1 hc).1`. Establish `hca : c ≠ a` using `(Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1`.

Distinguish the cases in `h1 : Q₁ (a, c)`. Distinguish the cases in `h2 : Q₂ (c, b)`. Rewrite using `[mk_of Q₁ _ (Ne.symm hca) h1, mk_of Q₁ _ (Ne.symm hca) h1, mk_of Q₂ _ hcb h2, mk_of Q₂ _ hcb h2]`. Establish `r1` using `hP.rk1 a c b (h₁ _ h1) (h₂ _ h2)`. Establish `r2` using `hP.rk2 a c b (h₁ _ h1) (h₂ _ h2)`.

Use `show z ⟨(a, c), h₁ _ h1⟩ * z ⟨(c, b), h₂ _ h2⟩ = z' ⟨(a, c), h₁ _ h1⟩ * z' ⟨(c, b), h₂ _ h2⟩`. Rewrite using `[h ⟨(a, c), h₁ _ h1⟩ r1, h ⟨(c, b), h₂ _ h2⟩ r2]`. Rewrite using `[mk_zero Q₂ _ hcb h2, mk_zero Q₂ _ hcb h2, mul_zero, mul_zero]`. Rewrite using `[mk_zero Q₁ _ (Ne.symm hca) h1, mk_zero Q₁ _ (Ne.symm hca) h1, zero_mul, zero_mul]`. Take `⟨e, he, hme⟩` from `hS {p // P p} K μ (fun p => rk p.1) (fun z => T z - z) (hT.sub measurable_id) (fun i z z' h => hdep i z z' h)`.

Use `⟨m.trans e, hme.comp hmm, fun x y => ?_⟩` and prove the remaining obligations. Establish `hres1 : res h₁ (m (x, y)) = x`. Use function extensionality and compare the values at `q`. Use `show m (x, y) ⟨q.1, h₁ _ q.2⟩ = x q`. Rewrite using `[hm]`.

Establish `hs : (splitEquiv h₁ h₂ hor hd).symm ⟨q.1, h₁ _ q.2⟩ = Sum.inl q` using `by first`. Consider the case `simp [splitEquiv, q.2]`. Consider the case `(show (if h : Q₁ q.1 then Sum.inl ⟨q.1, h⟩ else Sum.inr ⟨q.1, _⟩) = Sum.inl q`. Rewrite using `[dif_pos q.2])`. Rewrite using `[hs]`.

Apply the tactic sequence `try rfl`. Establish `hres2 : res h₂ (m (x, y)) = y`. Use function extensionality and compare the values at `q`. Use `show m (x, y) ⟨q.1, h₂ _ q.2⟩ = y q`. Rewrite using `[hm]`.

Establish `hn : ¬ Q₁ q.1` using `fun h => hd _ h q.2`. Establish `hs : (splitEquiv h₁ h₂ hor hd).symm ⟨q.1, h₂ _ q.2⟩ = Sum.inr q` using `by first`. Consider the case `simp [splitEquiv, hn]`. Consider the case `(show (if h : Q₁ q.1 then Sum.inl ⟨q.1, h⟩ else Sum.inr ⟨q.1, _⟩) = Sum.inr q`. Rewrite using `[dif_neg hn])`.

Rewrite using `[hs]`. Apply the tactic sequence `try rfl`. Establish `hx : (m.trans e) (x, y) = T (m (x, y))`. Simplify using `only [MeasurableEquiv.trans_apply, he]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hx]`. Use `show mk P (fun p => (mk Q₁ (res h₁ (m (x, y))) * mk Q₂ (res h₂ (m (x, y)))) p.1.1 p.1.2) = _`. Rewrite using `[hres1, hres2]`. Conclude with `mk_coords _ (mul_diag hP h₁ h₂ x y) (fun a b hab h => mul_off hP h₁ h₂ x y hab h)`.
-/
theorem prodEquiv [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (hS : TriangularShearMeasurePreserving) (hM : CoordinateMergeMeasurable) (μ : Measure K)
    [SigmaFinite μ] [μ.IsAddLeftInvariant] (hP : Tri P) (h₁ : ∀ p, Q₁ p → P p)
    (h₂ : ∀ p, Q₂ p → P p) (hor : ∀ p, P p → Q₁ p ∨ Q₂ p) (hd : ∀ p, Q₁ p → ¬ Q₂ p) :
    ∃ a : (({p // Q₁ p} → K) × ({p // Q₂ p} → K)) ≃ᵐ ({p // P p} → K),
      MeasurePreserving a ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
        (Measure.pi fun _ => μ) ∧
      ∀ x y, mk P (a (x, y)) = mk Q₁ x * mk Q₂ y := by
  obtain ⟨m, hm, hmm⟩ := hM {p // Q₁ p} {p // Q₂ p} {p // P p} K μ (splitEquiv h₁ h₂ hor hd)
  let T : ({p // P p} → K) → ({p // P p} → K) :=
    fun z p => (mk Q₁ (res h₁ z) * mk Q₂ (res h₂ z)) p.1.1 p.1.2
  have hT : Measurable T := by
    refine measurable_pi_iff.2 fun p => ?_
    simp only [T, Matrix.mul_apply]
    first
      | exact Finset.measurable_sum _ fun c _ => (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2)
      | exact Finset.measurable_sum' _ fun c _ => (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2)
      | (apply Finset.measurable_sum
         intro c _
         exact (measurable_entry h₁ p.1.1 c).mul (measurable_entry h₂ c p.1.2))
  have hsum : ∀ (z : {p // P p} → K) (a b : Fin n) (hp : P (a, b)),
      mk Q₁ (res h₁ z) a b + mk Q₂ (res h₂ z) a b = z ⟨(a, b), hp⟩ := by
    intro z a b hp
    have hab : a ≠ b := hP.ne hp
    rcases hor _ hp with hq | hq
    · rw [mk_of Q₁ _ hab hq, mk_zero Q₂ _ hab (hd _ hq), add_zero]
      try rfl
    · rw [mk_zero Q₁ _ hab (fun h => hd _ h hq), mk_of Q₂ _ hab hq, zero_add]
      try rfl
  have hrest : ∀ (z : {p // P p} → K) (a b : Fin n) (hp : P (a, b)),
      T z ⟨(a, b), hp⟩ - z ⟨(a, b), hp⟩ = rest (res h₁ z) (res h₂ z) a b := by
    intro z a b hp
    have hab : a ≠ b := hP.ne hp
    show (mk Q₁ (res h₁ z) * mk Q₂ (res h₂ z)) a b - z ⟨(a, b), hp⟩ = _
    rw [mul_on _ _ hab, ← hsum z a b hp]
    ring
  have hdep : ∀ (i : {p // P p}) (z z' : {p // P p} → K), (∀ j : {p // P p}, rk j.1 < rk i.1 → z j = z' j) →
      T z i - z i = T z' i - z' i := by
    rintro ⟨⟨a, b⟩, hp⟩ z z' h
    rw [hrest z a b hp, hrest z' a b hp]
    unfold rest
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcb : c ≠ b := (Finset.mem_erase.1 hc).1
    have hca : c ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
    by_cases h1 : Q₁ (a, c)
    · by_cases h2 : Q₂ (c, b)
      · rw [mk_of Q₁ _ (Ne.symm hca) h1, mk_of Q₁ _ (Ne.symm hca) h1, mk_of Q₂ _ hcb h2, mk_of Q₂ _ hcb h2]
        have r1 := hP.rk1 a c b (h₁ _ h1) (h₂ _ h2)
        have r2 := hP.rk2 a c b (h₁ _ h1) (h₂ _ h2)
        show z ⟨(a, c), h₁ _ h1⟩ * z ⟨(c, b), h₂ _ h2⟩ = z' ⟨(a, c), h₁ _ h1⟩ * z' ⟨(c, b), h₂ _ h2⟩
        rw [h ⟨(a, c), h₁ _ h1⟩ r1, h ⟨(c, b), h₂ _ h2⟩ r2]
      · rw [mk_zero Q₂ _ hcb h2, mk_zero Q₂ _ hcb h2, mul_zero, mul_zero]
    · rw [mk_zero Q₁ _ (Ne.symm hca) h1, mk_zero Q₁ _ (Ne.symm hca) h1, zero_mul, zero_mul]
  obtain ⟨e, he, hme⟩ := hS {p // P p} K μ (fun p => rk p.1) (fun z => T z - z) (hT.sub measurable_id)
    (fun i z z' h => hdep i z z' h)
  refine ⟨m.trans e, hme.comp hmm, fun x y => ?_⟩
  have hres1 : res h₁ (m (x, y)) = x := by
    funext q
    show m (x, y) ⟨q.1, h₁ _ q.2⟩ = x q
    rw [hm]
    have hs : (splitEquiv h₁ h₂ hor hd).symm ⟨q.1, h₁ _ q.2⟩ = Sum.inl q := by
      first
        | simp [splitEquiv, q.2]
        | (show (if h : Q₁ q.1 then Sum.inl ⟨q.1, h⟩ else Sum.inr ⟨q.1, _⟩) = Sum.inl q
           rw [dif_pos q.2])
    rw [hs]
    try rfl
  have hres2 : res h₂ (m (x, y)) = y := by
    funext q
    show m (x, y) ⟨q.1, h₂ _ q.2⟩ = y q
    rw [hm]
    have hn : ¬ Q₁ q.1 := fun h => hd _ h q.2
    have hs : (splitEquiv h₁ h₂ hor hd).symm ⟨q.1, h₂ _ q.2⟩ = Sum.inr q := by
      first
        | simp [splitEquiv, hn]
        | (show (if h : Q₁ q.1 then Sum.inl ⟨q.1, h⟩ else Sum.inr ⟨q.1, _⟩) = Sum.inr q
           rw [dif_neg hn])
    rw [hs]
    try rfl
  have hx : (m.trans e) (x, y) = T (m (x, y)) := by
    simp only [MeasurableEquiv.trans_apply, he]
    abel
  rw [hx]
  show mk P (fun p => (mk Q₁ (res h₁ (m (x, y))) * mk Q₂ (res h₂ (m (x, y)))) p.1.1 p.1.2) = _
  rw [hres1, hres2]
  exact mk_coords _ (mul_diag hP h₁ h₂ x y) (fun a b hab h => mul_off hP h₁ h₂ x y hab h)

end Meas

section Main

open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase

variable {K : Type} [CommRing K]

abbrev PUV {n : ℕ} (sb : Fin n → Fin n → Bool) : Fin n × Fin n → Prop :=
  fun p => p.1 < p.2 ∧ sb p.1 p.2 = true

variable {s : List ℕ} {sb : Fin s.sum → Fin s.sum → Bool}

def revEquiv (hsb : ∀ a b, sb a b = true ↔ blk s a = blk s b) :
    {p // PV sb p} ≃ {p // PUV sb p} where
  toFun q := ⟨(revF s q.1.1, revF s q.1.2),
    revF_lt_of_blk_eq s ((hsb _ _).1 q.2.2).symm q.2.1,
    (hsb _ _).2 (by rw [blk_revF, blk_revF]; exact (hsb _ _).1 q.2.2)⟩
  invFun q := ⟨(revF s q.1.1, revF s q.1.2),
    revF_lt_of_blk_eq s ((hsb _ _).1 q.2.2) q.2.1,
    (hsb _ _).2 (by rw [blk_revF, blk_revF]; exact (hsb _ _).1 q.2.2)⟩
  left_inv q := Subtype.ext (Prod.ext (revF_revF s _) (revF_revF s _))
  right_inv q := Subtype.ext (Prod.ext (revF_revF s _) (revF_revF s _))

/- English proof (translation)
Use extensionality with `a c`. Rewrite using `[conj_apply]`. Establish `key : ∀ q : {p // PV sb p}, (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) x) (revEquiv hsb q) = x q`. Introduce `q`. Use `first`.

Consider the case `exact Equiv.piCongrLeft_apply_apply _ _ _`. Consider the case `simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Rewrite using `[mk_self, mk_self, mul_one]`.

Simplify using the standard rewrite rules. Establish `hrac : revF s a ≠ revF s c` using `fun e => hac (by simpa using congrArg (revF s) e)`. Distinguish the cases in `h : PUV sb (a, c)`. Establish `hb : blk s a = blk s c` using `(hsb a c).1 h.2`. Establish `h' : PV sb (revF s a, revF s c)` using `⟨revF_lt_of_blk_eq s hb h.1, (hsb _ _).2 (by rw [blk_revF, blk_revF]; exact hb)⟩`.

Rewrite using `[mk_of _ _ hrac h', mk_of _ _ hac h]`. Establish `hq : (⟨(a, c), h⟩ : {p // PUV sb p}) = revEquiv hsb ⟨(revF s a, revF s c), h'⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[revEquiv]`. Rewrite using `[hq, key, hb, mul_right_comm, Units.inv_mul, one_mul]`.

Rewrite using `[mk_zero _ _ hac h]`. Establish `h'' : ¬ PV sb (revF s a, revF s c)`. Introduce and unpack `⟨h1, h2⟩`. Establish `hb' : blk s (revF s a) = blk s (revF s c)` using `(hsb _ _).1 h2`. Rewrite `hb'` using `[blk_revF, blk_revF]`.

Apply `h` to reduce the goal to its premises. Use `⟨?_, (hsb a c).2 hb'⟩` and prove the remaining obligations. Use `revF_lt_of_blk_eq s (by rw [blk_revF, blk_revF]; exact hb'.symm) h1` as an intermediate fact. Simplify using `using this`. Rewrite using `[mk_zero _ _ hrac h'']`.

Simplify using the standard rewrite rules.
-/
theorem conj_mk [MeasurableSpace K] (hsb : ∀ a b, sb a b = true ↔ blk s a = blk s b) (t : ℕ → Kˣ)
    (x : {p // PV sb p} → K) :
    ptI s t * mk (PV sb) x * pt s t =
      mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) x) := by
  ext a c
  rw [conj_apply]
  have key : ∀ q : {p // PV sb p},
      (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) x) (revEquiv hsb q) = x q := by
    intro q
    first
      | exact Equiv.piCongrLeft_apply_apply _ _ _
      | simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]
  by_cases hac : a = c
  · subst hac
    rw [mk_self, mk_self, mul_one]
    simp
  · have hrac : revF s a ≠ revF s c := fun e => hac (by simpa using congrArg (revF s) e)
    by_cases h : PUV sb (a, c)
    · have hb : blk s a = blk s c := (hsb a c).1 h.2
      have h' : PV sb (revF s a, revF s c) :=
        ⟨revF_lt_of_blk_eq s hb h.1, (hsb _ _).2 (by rw [blk_revF, blk_revF]; exact hb)⟩
      rw [mk_of _ _ hrac h', mk_of _ _ hac h]
      have hq : (⟨(a, c), h⟩ : {p // PUV sb p}) = revEquiv hsb ⟨(revF s a, revF s c), h'⟩ := by
        apply Subtype.ext
        simp [revEquiv]
      rw [hq, key, hb, mul_right_comm, Units.inv_mul, one_mul]
    · rw [mk_zero _ _ hac h]
      have h'' : ¬ PV sb (revF s a, revF s c) := by
        rintro ⟨h1, h2⟩
        have hb' : blk s (revF s a) = blk s (revF s c) := (hsb _ _).1 h2
        rw [blk_revF, blk_revF] at hb'
        apply h
        refine ⟨?_, (hsb a c).2 hb'⟩
        have := revF_lt_of_blk_eq s (by rw [blk_revF, blk_revF]; exact hb'.symm) h1
        simpa using this
      rw [mk_zero _ _ hrac h'']
      simp

/- English proof (translation)
Unfold `sUp`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`. Introduce `e`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Both sides reduce to the same expression.
-/
theorem sUp_one {n : ℕ} : sUp (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  unfold sUp
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    have := congrArg Fin.val e
    simp at this
  · rfl

/- English proof (translation)
Establish `h1 : V * pt s t * (ptI s t * V * pt s t)⁻¹ = pt s t`. Establish `: V * pt s t = pt s t * (ptI s t * V * pt s t)`. Simplify using `only [← Matrix.mul_assoc, pt_mul_ptI, Matrix.one_mul]`. Rewrite using `[this, Matrix.mul_assoc, mul_inv_one_up hU, Matrix.mul_one]`. Establish `h2` using `phaseWellDef K s t V _ hV (isUpUni_inv K hU) h1`.

Establish `h3` using `(simpleAdd K s.sum (ptI s t * V * pt s t) (ptI s t * V * pt s t)⁻¹).2 hU (isUpUni_inv K hU)`. Rewrite `h3` using `[mul_inv_one_up hU, sUp_one]`. Take the linear combination `h2 + h3`.
-/
theorem sLow_eq_sUp_conj (t : ℕ → Kˣ) {V : Matrix (Fin s.sum) (Fin s.sum) K} (hV : IsLowUni V)
    (hU : IsUpUni (ptI s t * V * pt s t)) : sLow V = sUp (ptI s t * V * pt s t) := by
  have h1 : V * pt s t * (ptI s t * V * pt s t)⁻¹ = pt s t := by
    have : V * pt s t = pt s t * (ptI s t * V * pt s t) := by
      simp only [← Matrix.mul_assoc, pt_mul_ptI, Matrix.one_mul]
    rw [this, Matrix.mul_assoc, mul_inv_one_up hU, Matrix.mul_one]
  have h2 := phaseWellDef K s t V _ hV (isUpUni_inv K hU) h1
  have h3 := (simpleAdd K s.sum (ptI s t * V * pt s t) (ptI s t * V * pt s t)⁻¹).2 hU
    (isUpUni_inv K hU)
  rw [mul_inv_one_up hU, sUp_one] at h3
  linear_combination h2 + h3

end Main

/- English proof (translation)
Introduce `K _ _ _ _ _ _ μ _ _ s t sb hsb G`. Establish `hor1 : ∀ p : Fin s.sum × Fin s.sum, PL s.sum p → PW sb p ∨ PV sb p`. Introduce `p hp`. Consider the cases of `h : sb p.1 p.2`. Conclude with `Or.inl ⟨hp, h⟩`.

Conclude with `Or.inr ⟨hp, h⟩`. Establish `hd1 : ∀ p : Fin s.sum × Fin s.sum, PW sb p → ¬ PV sb p` using `fun p h1 h2 => Bool.false_ne_true (h1.2.symm.trans h2.2)`. Establish `hor2 : ∀ p : Fin s.sum × Fin s.sum, PU s.sum p → PUV sb p ∨ PN sb p`. Introduce `p hp`. Consider the cases of `h : sb p.1 p.2`.

Conclude with `Or.inr ⟨hp, h⟩`. Conclude with `Or.inl ⟨hp, h⟩`. Establish `hd2 : ∀ p : Fin s.sum × Fin s.sum, PUV sb p → ¬ PN sb p` using `fun p h1 h2 => Bool.false_ne_true (h2.2.symm.trans h1.2)`. Take `⟨a, ham, ha⟩` from `prodEquiv (P := PL s.sum) (Q₁ := PW sb) (Q₂ := PV sb) hS hM μ tri_PL (fun p hp => hp.1) (fun p hp => hp.1) hor1 hd1`. Take `⟨b, hbm, hb⟩` from `prodEquiv (P := PU s.sum) (Q₁ := PUV sb) (Q₂ := PN sb) hS hM μ tri_PU (fun p hp => hp.1) (fun p hp => hp.1) hor2 hd2`.

Establish `hR : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb)) (Measure.pi fun _ : {p // PV sb p} => μ) (Measure.pi fun _ : {p // PUV sb p} => μ)` using `by first`. Consider the case `exact measurePreserving_piCongrLeft (fun _ : {p // PUV sb p} => μ) (revEquiv hsb)`. Consider the case `exact measurePreserving_piCongrLeft (fun _ => K) (fun _ : {p // PUV sb p} => μ) (revEquiv hsb)`. Establish `hB2 : MeasurePreserving (((MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb)).prodCongr (MeasurableEquiv.refl ({p // PN sb p} → K))).trans b) ((Measure.pi fun _ : {p // PV sb p} => μ).prod (Measure.pi fun _ : {p // PN sb p} => μ)) (Measure.pi fun _ : {p // PU s.sum p} => μ)` using `hbm.comp (hR.prod (MeasurePreserving.id _))`. Establish `hΞ : MeasurePreserving (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl ({p // PW sb p} → K)).prodCongr (((MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb)).prodCongr (MeasurableEquiv.refl ({p // PN sb p} → K))).trans b))) (((Measure.pi fun _ : {p // PW sb p} => μ). …` using `((MeasurePreserving.id _).prod hB2).comp (measurePreserving_prodAssoc _ _ _)`.

Establish `hΨ : MeasurePreserving (a.prodCongr (MeasurableEquiv.refl ({p // PN sb p} → K))) (((Measure.pi fun _ : {p // PW sb p} => μ).prod (Measure.pi fun _ : {p // PV sb p} => μ)).prod (Measure.pi fun _ : {p // PN sb p} => μ)) ((Measure.pi fun _ : {p // PL s.sum p} => μ).prod (Measure.pi …` using `ham.prod (MeasurePreserving.id _)`. Establish `hsl : ∀ A X : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni A → IsLowUni X → sLow (A * X) = sLow A + sLow X`. Introduce `A X hA hX`. Unfold `sLow`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_add j ⟨j.val + 1, h⟩]`. Rewrite using `[hX.2 j, mul_one, hA.2 ⟨j.val + 1, h⟩, one_mul]`. Introduce `hh`.

Use `congrArg Fin.val hh` as an intermediate fact. Simplify using `at this`. Introduce and unpack `k _ ⟨hk1, hk2⟩`. Break down `lt_or_gt_of_ne hk1 with hlt | hgt` into its components or cases. Rewrite using `[hX.1 hlt, mul_zero]`.

Establish `h1 : (j : ℕ) < k` using `hgt`. Establish `h2 : (k : ℕ) ≠ j.val + 1` using `fun e => hk2 (Fin.ext e)`. Establish `h3 : (⟨j.val + 1, h⟩ : Fin s.sum) < k` using `Fin.lt_def.2 (show j.val + 1 < k.val by omega)`. Rewrite using `[hA.1 h3, zero_mul]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hsu : ∀ Y B : Matrix (Fin s.sum) (Fin s.sum) K, IsUpUni Y → IsUpUni B → sUp (Y * B) = sUp Y + sUp B`. Introduce `Y B hY hB`. Unfold `sUp`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_add j ⟨j.val + 1, h⟩]`. Rewrite using `[hY.2 j, one_mul, hB.2 ⟨j.val + 1, h⟩, mul_one, add_comm]`.

Introduce `hh`. Use `congrArg Fin.val hh` as an intermediate fact. Simplify using `at this`. Introduce and unpack `k _ ⟨hk1, hk2⟩`. Break down `lt_or_gt_of_ne hk1 with hlt | hgt` into its components or cases.

Rewrite using `[hY.1 hlt, zero_mul]`. Establish `h1 : (j : ℕ) < k` using `hgt`. Establish `h2 : (k : ℕ) ≠ j.val + 1` using `fun e => hk2 (Fin.ext e)`. Establish `h3 : (⟨j.val + 1, h⟩ : Fin s.sum) < k` using `Fin.lt_def.2 (show j.val + 1 < k.val by omega)`. Rewrite using `[hB.1 h3, mul_zero]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[← hΨ.integral_comp', ← hΞ.integral_comp']`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Take `⟨⟨x, v⟩, y⟩` from `w`. Use `show G (mk (PL s.sum) (a (x, v)) * pt s t * mk (PN sb) y) (sLow (mk (PL s.sum) (a (x, v))) + sUp (mk (PN sb) y)) = G (mk (PW sb) x * pt s t * mk (PU s.sum) (b (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v, y))) (sLow (mk (PW sb) x) + sUp (mk (PU s.sum) (b (Measurable …`. Rewrite using `[ha x v, hb _ y]`. Establish `hc : mk (PV sb) v * pt s t = pt s t * mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v)`.

Rewrite using `[← conj_mk hsb t v, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI, Matrix.one_mul]`. Establish `hlowV : IsLowUni (mk (PV sb) v)` using `isLowUni_mk (P := PV sb) (fun p hp => hp.1) v`. Establish `hupU : IsUpUni (mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v))` using `isUpUni_mk (P := PUV sb) (fun p hp => hp.1) _`. Establish `hph : sLow (mk (PV sb) v) = sUp (mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v))`. Rewrite using `[sLow_eq_sUp_conj t hlowV (by rw [conj_mk hsb t v]; exact hupU), conj_mk hsb t v]`.

Use `congr 1`. Rewrite using `[Matrix.mul_assoc (mk (PW sb) x) (mk (PV sb) v), hc]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hsl _ _ (isLowUni_mk (P := PW sb) (fun p hp => hp.1) x) hlowV, hsu _ _ hupU (isUpUni_mk (P := PN sb) (fun p hp => hp.1) y), hph]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main (hS : TriangularShearMeasurePreserving) (hM : CoordinateMergeMeasurable) : OrbitParametrisationsAgree := by
  intro K _ _ _ _ _ _ μ _ _ s t sb hsb G
  have hor1 : ∀ p : Fin s.sum × Fin s.sum, PL s.sum p → PW sb p ∨ PV sb p := by
    intro p hp
    cases h : sb p.1 p.2
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  have hd1 : ∀ p : Fin s.sum × Fin s.sum, PW sb p → ¬ PV sb p := fun p h1 h2 =>
    Bool.false_ne_true (h1.2.symm.trans h2.2)
  have hor2 : ∀ p : Fin s.sum × Fin s.sum, PU s.sum p → PUV sb p ∨ PN sb p := by
    intro p hp
    cases h : sb p.1 p.2
    · exact Or.inr ⟨hp, h⟩
    · exact Or.inl ⟨hp, h⟩
  have hd2 : ∀ p : Fin s.sum × Fin s.sum, PUV sb p → ¬ PN sb p := fun p h1 h2 =>
    Bool.false_ne_true (h2.2.symm.trans h1.2)
  obtain ⟨a, ham, ha⟩ := prodEquiv (P := PL s.sum) (Q₁ := PW sb) (Q₂ := PV sb) hS hM μ tri_PL
    (fun p hp => hp.1) (fun p hp => hp.1) hor1 hd1
  obtain ⟨b, hbm, hb⟩ := prodEquiv (P := PU s.sum) (Q₁ := PUV sb) (Q₂ := PN sb) hS hM μ tri_PU
    (fun p hp => hp.1) (fun p hp => hp.1) hor2 hd2
  have hR : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb))
      (Measure.pi fun _ : {p // PV sb p} => μ) (Measure.pi fun _ : {p // PUV sb p} => μ) := by
    first
      | exact measurePreserving_piCongrLeft (fun _ : {p // PUV sb p} => μ) (revEquiv hsb)
      | exact measurePreserving_piCongrLeft (fun _ => K) (fun _ : {p // PUV sb p} => μ) (revEquiv hsb)
  have hB2 : MeasurePreserving (((MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb)).prodCongr
        (MeasurableEquiv.refl ({p // PN sb p} → K))).trans b)
      ((Measure.pi fun _ : {p // PV sb p} => μ).prod (Measure.pi fun _ : {p // PN sb p} => μ))
      (Measure.pi fun _ : {p // PU s.sum p} => μ) :=
    hbm.comp (hR.prod (MeasurePreserving.id _))
  have hΞ : MeasurePreserving (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.refl ({p // PW sb p} → K)).prodCongr
          (((MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb)).prodCongr
            (MeasurableEquiv.refl ({p // PN sb p} → K))).trans b)))
      (((Measure.pi fun _ : {p // PW sb p} => μ).prod (Measure.pi fun _ : {p // PV sb p} => μ)).prod
        (Measure.pi fun _ : {p // PN sb p} => μ))
      ((Measure.pi fun _ : {p // PW sb p} => μ).prod (Measure.pi fun _ : {p // PU s.sum p} => μ)) :=
    ((MeasurePreserving.id _).prod hB2).comp (measurePreserving_prodAssoc _ _ _)
  have hΨ : MeasurePreserving (a.prodCongr (MeasurableEquiv.refl ({p // PN sb p} → K)))
      (((Measure.pi fun _ : {p // PW sb p} => μ).prod (Measure.pi fun _ : {p // PV sb p} => μ)).prod
        (Measure.pi fun _ : {p // PN sb p} => μ))
      ((Measure.pi fun _ : {p // PL s.sum p} => μ).prod (Measure.pi fun _ : {p // PN sb p} => μ)) :=
    ham.prod (MeasurePreserving.id _)
  have hsl : ∀ A X : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni A → IsLowUni X →
      sLow (A * X) = sLow A + sLow X := by
    intro A X hA hX
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j.val + 1, h⟩]
      · rw [hX.2 j, mul_one, hA.2 ⟨j.val + 1, h⟩, one_mul]
      · intro hh
        have := congrArg Fin.val hh
        simp at this
      · rintro k _ ⟨hk1, hk2⟩
        rcases lt_or_gt_of_ne hk1 with hlt | hgt
        · rw [hX.1 hlt, mul_zero]
        · have h1 : (j : ℕ) < k := hgt
          have h2 : (k : ℕ) ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
          have h3 : (⟨j.val + 1, h⟩ : Fin s.sum) < k := Fin.lt_def.2 (show j.val + 1 < k.val by omega)
          rw [hA.1 h3, zero_mul]
      · simp
      · simp
    · simp
  have hsu : ∀ Y B : Matrix (Fin s.sum) (Fin s.sum) K, IsUpUni Y → IsUpUni B →
      sUp (Y * B) = sUp Y + sUp B := by
    intro Y B hY hB
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j.val + 1, h⟩]
      · rw [hY.2 j, one_mul, hB.2 ⟨j.val + 1, h⟩, mul_one, add_comm]
      · intro hh
        have := congrArg Fin.val hh
        simp at this
      · rintro k _ ⟨hk1, hk2⟩
        rcases lt_or_gt_of_ne hk1 with hlt | hgt
        · rw [hY.1 hlt, zero_mul]
        · have h1 : (j : ℕ) < k := hgt
          have h2 : (k : ℕ) ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
          have h3 : (⟨j.val + 1, h⟩ : Fin s.sum) < k := Fin.lt_def.2 (show j.val + 1 < k.val by omega)
          rw [hB.1 h3, mul_zero]
      · simp
      · simp
    · simp
  rw [← hΨ.integral_comp', ← hΞ.integral_comp']
  congr 1
  funext w
  obtain ⟨⟨x, v⟩, y⟩ := w
  show G (mk (PL s.sum) (a (x, v)) * pt s t * mk (PN sb) y)
      (sLow (mk (PL s.sum) (a (x, v))) + sUp (mk (PN sb) y)) =
    G (mk (PW sb) x * pt s t * mk (PU s.sum) (b (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v, y)))
      (sLow (mk (PW sb) x) + sUp (mk (PU s.sum) (b (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v, y))))
  rw [ha x v, hb _ y]
  have hc : mk (PV sb) v * pt s t =
      pt s t * mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v) := by
    rw [← conj_mk hsb t v, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI, Matrix.one_mul]
  have hlowV : IsLowUni (mk (PV sb) v) := isLowUni_mk (P := PV sb) (fun p hp => hp.1) v
  have hupU : IsUpUni (mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v)) :=
    isUpUni_mk (P := PUV sb) (fun p hp => hp.1) _
  have hph : sLow (mk (PV sb) v) =
      sUp (mk (PUV sb) (MeasurableEquiv.piCongrLeft (fun _ => K) (revEquiv hsb) v)) := by
    rw [sLow_eq_sUp_conj t hlowV (by rw [conj_mk hsb t v]; exact hupU), conj_mk hsb t v]
  congr 1
  · rw [Matrix.mul_assoc (mk (PW sb) x) (mk (PV sb) v), hc]
    simp only [Matrix.mul_assoc]
  · rw [hsl _ _ (isLowUni_mk (P := PW sb) (fun p hp => hp.1) x) hlowV,
      hsu _ _ hupU (isUpUni_mk (P := PN sb) (fun p hp => hp.1) y), hph]
    ring

end Dec

/- English proof (translation)
Conclude with `Dec.main hS hM`.
-/
theorem dec (hS : TriangularShearMeasurePreserving) (hM : CoordinateMergeMeasurable) : OrbitParametrisationsAgree := by
  exact Dec.main hS hM

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt

namespace Formalism.MainNotions.LocalOrbitGerms

def InvariantUnipotentMeasuresExist : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    [IsTopologicalRing E] (M : Model F E), M.OK → ∀ (n : ℕ) (w : Pt E n),
    ∃ (μ₁ : Measure (lowW E (tr w).1 (tr w).2)) (μ₂ : Measure (upUniG E (tr w).1.sum)),
      μ₁.IsMulRightInvariant ∧ μ₂.IsMulLeftInvariant ∧ SFinite μ₁ ∧ SFinite μ₂ ∧
      μ₁ (intSub M.R (lowW E (tr w).1 (tr w).2) : Set (lowW E (tr w).1 (tr w).2)) = 1 ∧
      μ₂ (intSub M.R (upUniG E (tr w).1.sum) : Set (upUniG E (tr w).1.sum)) = 1 ∧
      ∀ G : Matrix (Fin n) (Fin n) E → E → ℂ,
        ∫ xy : (IL n → E) × (IN w → E), G (uLow xy.1 * w.mat * uUp w xy.2)
            (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))
            ∂((Measure.pi fun _ : IL n => M.mu).prod (Measure.pi fun _ : IN w => M.mu)) =
          ∫ p, G ((A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm))
            (sLow ((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) +
              sUp ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E))
            ∂(μ₁.prod μ₂)

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.FourierDecayAlt Formalism.MainNotions.LocalModelPeriodLattices
open scoped ComplexConjugate

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Cls

section Comb

variable {E : Type} [CommRing E]

/- English proof (translation)
The claim follows from `| [], a, b, h, _ => by simp at h | (t, s) :: bs, a, b, ha, hb => by simp only [List.map_cons, List.sum_cons] at ha hb simp only [sameBlock, List.map_cons, blk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] by_cases h1 : a < (s : ℕ) · by_cases h2 : b < (s : ℕ) · simp [h1, …`.
-/
theorem sameBlock_iff : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    b < (bs.map (fun b => (b.2 : ℕ))).sum →
    (sameBlock bs a b = true ↔ blk (bs.map (fun b => (b.2 : ℕ))) a = blk (bs.map (fun b => (b.2 : ℕ))) b)
  | [], a, b, h, _ => by simp at h
  | (t, s) :: bs, a, b, ha, hb => by
    simp only [List.map_cons, List.sum_cons] at ha hb
    simp only [sameBlock, List.map_cons, blk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : a < (s : ℕ)
    · by_cases h2 : b < (s : ℕ)
      · simp [h1, h2]
      · have h3 : ¬ ((s : ℕ) ≤ a) := by omega
        simp only [h1, h2, h3, and_false, false_and, or_self, if_true, if_false, false_iff]
        omega
    · by_cases h2 : b < (s : ℕ)
      · have h3 : ¬ ((s : ℕ) ≤ b) := by omega
        simp only [h1, h2, h3, and_false, false_and, or_self, if_true, if_false, false_iff]
        omega
      · have h3 : (s : ℕ) ≤ a := by omega
        have h4 : (s : ℕ) ≤ b := by omega
        have := sameBlock_iff bs (a - s) (b - s) (by omega) (by omega)
        simp [h1, h2, h3, h4, this]

/- English proof (translation)
Unfold `simpleLow sLow`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨b.val + 1, h⟩]`.

Simplify using the standard rewrite rules. Introduce `a _ ha`. Rewrite using `[if_neg]`. Introduce `hab`. Conclude with `ha (Fin.ext hab)`.

Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hab`. Use `a.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem simpleLow_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : simpleLow A = sLow A := by
  unfold simpleLow sLow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨b.val + 1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg]
      intro hab
      exact ha (Fin.ext hab)
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    intro hab
    have := a.isLt
    omega

/- English proof (translation)
Unfold `simpleUp sUp`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a.val + 1, h⟩]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `hab`. Conclude with `hb (Fin.ext hab)`. Simplify using the standard rewrite rules.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hab`. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem simpleUp_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : simpleUp A = sUp A := by
  unfold simpleUp sUp
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val + 1, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hab
      exact hb (Fin.ext hab)
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hab
    have := b.isLt
    omega

end Comb

section Transfer

variable {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Take `⟨bs, rfl⟩` from `w`. Establish `hsb : ∀ a b : Fin (tr (⟨bs, rfl⟩ : Pt E _)).1.sum, (fun a b : Fin (tr (⟨bs, rfl⟩ : Pt E _)).1.sum => sameBlock bs a b) a b = true ↔ blk (tr (⟨bs, rfl⟩ : Pt E _)).1 a = blk (tr (⟨bs, rfl⟩ : Pt E _)).1 b` using `fun a b => sameBlock_iff bs a b a.2 b.2`. Take `⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, hint⟩` from `hG E μ R hR (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 _ hsb`. Use `⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, fun G => ?_⟩` and prove the remaining obligations. Establish `h1` using `hD E μ (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 _ hsb G`.

Establish `h2` using `hint (fun A B => G (A * pt (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 * B) (sLow A + sUp B))`. Establish `hm : (⟨bs, rfl⟩ : Pt E _).mat = pt (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2`. Rewrite using `[mat_eq]`. Both sides reduce to the same expression. Simplify using `only [simpleLow_eq, simpleUp_eq, hm]`.

Conclude with `h1.trans h2.symm`.
-/
theorem transferPt (hG : UnipotentProductMeasureInvariant) (hD : OrbitParametrisationsAgree) (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (R : Subring E) (hR : μ (R : Set E) = 1) {n : ℕ} (w : Pt E n) :
    ∃ (μ₁ : Measure (lowW E (tr w).1 (tr w).2)) (μ₂ : Measure (upUniG E (tr w).1.sum)),
      μ₁.IsMulRightInvariant ∧ μ₂.IsMulLeftInvariant ∧ SFinite μ₁ ∧ SFinite μ₂ ∧
      μ₁ (intSub R (lowW E (tr w).1 (tr w).2) : Set (lowW E (tr w).1 (tr w).2)) = 1 ∧
      μ₂ (intSub R (upUniG E (tr w).1.sum) : Set (upUniG E (tr w).1.sum)) = 1 ∧
      ∀ G : Matrix (Fin n) (Fin n) E → E → ℂ,
        ∫ xy : (IL n → E) × (IN w → E), G (uLow xy.1 * w.mat * uUp w xy.2)
            (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))
            ∂((Measure.pi fun _ : IL n => μ).prod (Measure.pi fun _ : IN w => μ)) =
          ∫ p, G ((A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm))
            (sLow ((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) +
              sUp ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E))
            ∂(μ₁.prod μ₂) := by
  obtain ⟨bs, rfl⟩ := w
  have hsb : ∀ a b : Fin (tr (⟨bs, rfl⟩ : Pt E _)).1.sum,
      (fun a b : Fin (tr (⟨bs, rfl⟩ : Pt E _)).1.sum => sameBlock bs a b) a b = true ↔
        blk (tr (⟨bs, rfl⟩ : Pt E _)).1 a = blk (tr (⟨bs, rfl⟩ : Pt E _)).1 b :=
    fun a b => sameBlock_iff bs a b a.2 b.2
  obtain ⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, hint⟩ := hG E μ R hR (tr (⟨bs, rfl⟩ : Pt E _)).1
    (tr (⟨bs, rfl⟩ : Pt E _)).2 _ hsb
  refine ⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, fun G => ?_⟩
  have h1 := hD E μ (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 _ hsb G
  have h2 := hint (fun A B => G (A * pt (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 * B)
    (sLow A + sUp B))
  have hm : (⟨bs, rfl⟩ : Pt E _).mat = pt (tr (⟨bs, rfl⟩ : Pt E _)).1 (tr (⟨bs, rfl⟩ : Pt E _)).2 := by
    rw [mat_eq]; rfl
  simp only [simpleLow_eq, simpleUp_eq, hm]
  exact h1.trans h2.symm

end Transfer

section Iso

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def lamK (M : Model F E) {m : ℕ} (Z0 : M.Mat (m + 1)) : M.Cok Z0 →ₗ[M.R] KR M.R := M.lam Z0

def toMat (M : Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) (h1 : ∀ a b, Z a b ∈ M.R)
    (h2 : IsUnit Z.det) : M.Mat n := ⟨Matrix.of fun a b => ⟨Z a b, h1 a b⟩, h2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toMat_map (M : Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) (h1 : ∀ a b, Z a b ∈ M.R)
    (h2 : IsUnit Z.det) : (toMat M Z h1 h2).Z.map M.R.subtype = Z := rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [eLast]`. Distinguish the cases in `h : j = Fin.last m`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.single_eq_of_ne h, if_neg]`. Introduce `hj`. Conclude with `h (Fin.ext (by rw [Fin.val_last]; omega))`.
-/
theorem eLast_eq (R : Subring E) (m : ℕ) : (eLast R : Fin (m + 1) → R) = Pi.single (Fin.last m) 1 := by
  funext j
  simp only [eLast]
  by_cases h : j = Fin.last m
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg]
    intro hj
    exact h (Fin.ext (by rw [Fin.val_last]; omega))

/- English proof (translation)
Use `first`. Consider the case `(simp only [lastCoord, LinearMap.coeFn_sum, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last m)]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[if_neg]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `hj (Fin.ext (by rw [Fin.val_last]; omega))`. Use the proof step `simp)`.

Consider the case `(simp only [lastCoord]`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single (Fin.last m)]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg]`.

Simplify using the standard rewrite rules. Introduce `h`. Conclude with `hj (Fin.ext (by rw [Fin.val_last]; omega))`. Use the proof step `simp)`.
-/
theorem lastCoord_eq (R : Subring E) (m : ℕ) (x : Fin (m + 1) → E) :
    lastCoord R x = x (Fin.last m) := by
  first
    | (simp only [lastCoord, LinearMap.coeFn_sum, Finset.sum_apply]
       rw [Finset.sum_eq_single (Fin.last m)]
       · simp
       · intro j _ hj
         rw [if_neg]
         · simp
         · intro h
           exact hj (Fin.ext (by rw [Fin.val_last]; omega))
       · simp)
    | (simp only [lastCoord]
       rw [LinearMap.sum_apply, Finset.sum_eq_single (Fin.last m)]
       · simp
       · intro j _ hj
         rw [if_neg]
         · simp
         · intro h
           exact hj (Fin.ext (by rw [Fin.val_last]; omega))
       · simp)

/- English proof (translation)
Establish `h1 : lamK M ZZ (Submodule.Quotient.mk v) = M.lamRaw ZZ v` using `rfl`. Rewrite using `[h1]`. Simplify using `only [lamLin, Model.lamRaw, LinearMap.coe_comp, Function.comp_apply, lastCoord_eq, LinearMap.proj_apply]`. Both sides reduce to the same expression.
-/
theorem lamLin_eq (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    lamLin M.R (ZZ.Z.map M.R.subtype) v = lamK M ZZ (Submodule.Quotient.mk v) := by
  have h1 : lamK M ZZ (Submodule.Quotient.mk v) = M.lamRaw ZZ v := rfl
  rw [h1]
  simp only [lamLin, Model.lamRaw, LinearMap.coe_comp, Function.comp_apply, lastCoord_eq,
    LinearMap.proj_apply]
  rfl

def isoEquiv (M : Model F E) {m : ℕ} (ZZ Z0 : M.Mat (m + 1)) :
    M.Iso ZZ Z0 ≃ isoSet M.R (ZZ.Z.map M.R.subtype) (M.Cok Z0) (M.eCls Z0) (lamK M Z0) :=
  Equiv.subtypeEquiv
    { toFun := fun φ => (Submodule.quotEquivOfEq _ _ (latZ_eq M ZZ)).trans φ
      invFun := fun ψ => (Submodule.quotEquivOfEq _ _ (latZ_eq M ZZ)).symm.trans ψ
      left_inv := fun φ => LinearEquiv.ext fun x => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      right_inv := fun ψ => LinearEquiv.ext fun x => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] }
    (fun φ => by
      simp only [isoSet, Equiv.coe_fn_mk, Set.mem_ofPred_eq, LinearEquiv.trans_apply, eZ,
        Submodule.quotEquivOfEq_mk, eLast_eq, lamLin_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun v => h2 _⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun v => ?_⟩
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
        exact h2 v)

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : Z.submatrix (finCongr rfl.symm) (finCongr rfl.symm) = Z`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `⟨Iff.rfl, ⟨Equiv.refl _⟩⟩`.
-/
theorem reindex {n n' : ℕ} (h : n' = n) (R : Subring E) (Z : Matrix (Fin n') (Fin n') E)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    (IsInt R (Z.submatrix (finCongr h.symm) (finCongr h.symm)) ↔ IsInt R Z) ∧
      Nonempty (isoSet R (Z.submatrix (finCongr h.symm) (finCongr h.symm)) C e lam ≃
        isoSet R Z C e lam) := by
  subst h
  have e : Z.submatrix (finCongr rfl.symm) (finCongr rfl.symm) = Z := by
    ext i j
    simp
  rw [e]
  exact ⟨Iff.rfl, ⟨Equiv.refl _⟩⟩

/- English proof (translation)
Unfold `A5.orbZ`. Rewrite using `[Matrix.det_mul, Matrix.det_mul]`. Establish `h1 : ((p.1 : GL (Fin w.1.sum) E) : Matrix (Fin w.1.sum) (Fin w.1.sum) E).det = 1` using `by first`. Consider the case `(rw [Matrix.det_of_lowerTriangular _ p.1.2.1.1]`. Simplify using `[p.1.2.1.2])`.

Consider the case `(rw [Matrix.det_of_lowerTriangular p.1.2.1.1]`. Simplify using `[p.1.2.1.2])`. Establish `h2 : ((p.2 : GL (Fin w.1.sum) E) : Matrix (Fin w.1.sum) (Fin w.1.sum) E).det = 1` using `by first`. Consider the case `(rw [Matrix.det_of_upperTriangular p.2.2.1]`. Simplify using `[p.2.2.2])`.

Consider the case `(rw [Matrix.det_of_upperTriangular _ p.2.2.1]`. Simplify using `[p.2.2.2])`. Rewrite using `[h1, h2, one_mul, mul_one]`.
-/
theorem det_orbZ (w : A5.Point E) (p : lowW E w.1 w.2 × upUniG E w.1.sum) :
    (A5.orbZ w p).det = (pt w.1 w.2).det := by
  unfold A5.orbZ
  rw [Matrix.det_mul, Matrix.det_mul]
  have h1 : ((p.1 : GL (Fin w.1.sum) E) : Matrix (Fin w.1.sum) (Fin w.1.sum) E).det = 1 := by
    first
      | (rw [Matrix.det_of_lowerTriangular _ p.1.2.1.1]
         simp [p.1.2.1.2])
      | (rw [Matrix.det_of_lowerTriangular p.1.2.1.1]
         simp [p.1.2.1.2])
  have h2 : ((p.2 : GL (Fin w.1.sum) E) : Matrix (Fin w.1.sum) (Fin w.1.sum) E).det = 1 := by
    first
      | (rw [Matrix.det_of_upperTriangular p.2.2.1]
         simp [p.2.2.2])
      | (rw [Matrix.det_of_upperTriangular _ p.2.2.1]
         simp [p.2.2.2])
  rw [h1, h2, one_mul, mul_one]

/- English proof (translation)
Rewrite using `[Matrix.det_submatrix_equiv_self, det_orbZ]`. Conclude with `Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI _ _)`.
-/
theorem isUnit_det_sub {n : ℕ} (w : Pt E n) (p : lowW E (tr w).1 (tr w).2 × upUniG E (tr w).1.sum) :
    IsUnit ((A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm)).det := by
  rw [Matrix.det_submatrix_equiv_self, det_orbZ]
  exact Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI _ _)

open scoped Classical in

def GG (M : Model F E) {m : ℕ} (c : M.Cls m) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (a : E) : ℂ :=
  if h : (∀ a b, Z a b ∈ M.R) ∧ IsUnit Z.det then
    (M.nIso (toMat M Z h.1 h.2) (Quotient.out c) : ℂ) * M.psiR a
  else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bbIntegrand_eq (M : Model F E) {m : ℕ} (w : Pt E (m + 1)) (c : M.Cls m)
    (xy : (IL (m + 1) → E) × (IN w → E)) :
    M.bbIntegrand w c xy = GG M c (uLow xy.1 * w.mat * uUp w xy.2)
      (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2)) := rfl

variable [IsTopologicalRing E]

/- English proof (translation)
Take `⟨hi, ⟨eq⟩⟩` from `reindex (tr_sum w) M.R (A5.orbZ (tr w) p) (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c)) (lamK M (Quotient.out c))`. Distinguish the cases in `hI : IsInt M.R (A5.orbZ (tr w) p)`. Establish `h1` using `hi.2 hI`. Establish `hI' : IsInt M.R (((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) * pt (tr w).1 (tr w).2 * ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E))` using `hI`. Rewrite using `[GG, dif_pos ⟨h1, isUnit_det_sub w p⟩, phi, if_pos hI']`.

Use `congr 2`. Conclude with `Nat.card_congr ((isoEquiv M _ _).trans eq)`. Establish `hI' : ¬ IsInt M.R (((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) * pt (tr w).1 (tr w).2 * ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E))` using `hI`. Rewrite using `[GG, dif_neg (fun h => hI (hi.1 h.1)), phi, if_neg hI', zero_mul]`.
-/
theorem GG_eq_phi (M : Model F E) {m : ℕ} (w : Pt E (m + 1)) (c : M.Cls m)
    (p : lowW E (tr w).1 (tr w).2 × upUniG E (tr w).1.sum) :
    GG M c ((A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm))
      (sLow ((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) +
        sUp ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E)) =
      phi M.R (tr w).1 (tr w).2 M.psiR (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c))
        (lamK M (Quotient.out c)) p := by
  obtain ⟨hi, ⟨eq⟩⟩ := reindex (tr_sum w) M.R (A5.orbZ (tr w) p) (M.Cok (Quotient.out c))
    (M.eCls (Quotient.out c)) (lamK M (Quotient.out c))
  by_cases hI : IsInt M.R (A5.orbZ (tr w) p)
  · have h1 := hi.2 hI
    have hI' : IsInt M.R (((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) *
      pt (tr w).1 (tr w).2 * ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E)) := hI
    rw [GG, dif_pos ⟨h1, isUnit_det_sub w p⟩, phi, if_pos hI']
    congr 2
    exact Nat.card_congr ((isoEquiv M _ _).trans eq)
  · have hI' : ¬ IsInt M.R (((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) *
      pt (tr w).1 (tr w).2 * ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E)) := hI
    rw [GG, dif_neg (fun h => hI (hi.1 h.1)), phi, if_neg hI', zero_mul]

/- English proof (translation)
Unfold `Model.BB BB`. Simplify using `only [bbIntegrand_eq]`. Rewrite using `[hint (GG M c)]`. Simplify using `only [GG_eq_phi]`.
-/
theorem BB_eq (M : Model F E) {m : ℕ} (w : Pt E (m + 1))
    (μ₁ : Measure (lowW E (tr w).1 (tr w).2)) (μ₂ : Measure (upUniG E (tr w).1.sum))
    (hint : ∀ G : Matrix (Fin (m + 1)) (Fin (m + 1)) E → E → ℂ,
        ∫ xy : (IL (m + 1) → E) × (IN w → E), G (uLow xy.1 * w.mat * uUp w xy.2)
            (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))
            ∂((Measure.pi fun _ : IL (m + 1) => M.mu).prod (Measure.pi fun _ : IN w => M.mu)) =
          ∫ p, G ((A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm))
            (sLow ((p.1 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E) +
              sUp ((p.2 : GL (Fin (tr w).1.sum) E) : Matrix (Fin (tr w).1.sum) (Fin (tr w).1.sum) E))
            ∂(μ₁.prod μ₂)) (c : M.Cls m) :
    M.BB w c = BB M.R (tr w).1 (tr w).2 M.psiR (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c))
      (lamK M (Quotient.out c)) μ₁ μ₂ := by
  unfold Model.BB BB
  simp only [bbIntegrand_eq]
  rw [hint (GG M c)]
  simp only [GG_eq_phi]

end Iso

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Distinguish the cases in `h : d ∈ M.R`. Use `(finite_classes M hOK m ⟨d, h⟩ hd).subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨ZZ, h1, h2⟩`. Conclude with `⟨ZZ, Subtype.ext h1, h2⟩`. Use `Set.finite_empty.subset ?_` and prove the remaining obligations.

Introduce and unpack `c ⟨ZZ, h1, -⟩`. Conclude with `absurd (h1 ▸ ZZ.Z.det.2) h`.
-/
theorem finite_S (M : Model F E) (hOK : M.OK) (m : ℕ) (d : E) (hd : IsUnit d) :
    {c : M.Cls m | ∃ ZZ : M.Mat (m + 1), ((ZZ.Z.det : M.R) : E) = d ∧
      Quotient.mk (M.isoSetoid m) ZZ = c}.Finite := by
  by_cases h : d ∈ M.R
  · refine (finite_classes M hOK m ⟨d, h⟩ hd).subset ?_
    rintro c ⟨ZZ, h1, h2⟩
    exact ⟨ZZ, Subtype.ext h1, h2⟩
  · refine Set.finite_empty.subset ?_
    rintro c ⟨ZZ, h1, -⟩
    exact absurd (h1 ▸ ZZ.Z.det.2) h

/- English proof (translation)
Establish `h` using `RingHom.map_det M.R.subtype (toMat M Z h1 h2).Z`. Rewrite `h` using `[show M.R.subtype.mapMatrix (toMat M Z h1 h2).Z = Z from toMat_map M Z h1 h2]`. Conclude with `h`.
-/
theorem toMat_det (M : Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) (h1 : ∀ a b, Z a b ∈ M.R)
    (h2 : IsUnit Z.det) : (((toMat M Z h1 h2).Z.det : M.R) : E) = Z.det := by
  have h := RingHom.map_det M.R.subtype (toMat M Z h1 h2).Z
  rw [show M.R.subtype.mapMatrix (toMat M Z h1 h2).Z = Z from toMat_map M Z h1 h2] at h
  exact h

/- English proof (translation)
Take `⟨-, ⟨eq⟩⟩` from `reindex (tr_sum w) M.R (A5.orbZ (tr w) p) (M.Cok Z0) (M.eCls Z0) (lamK M Z0)`. Establish `e1` using `isoEquiv M (toMat M _ hi (isUnit_det_sub w p)) Z0`. Rewrite `e1` using `[toMat_map]`. Conclude with `Set.nonempty_coe_sort.1 ⟨eq (e1 φ)⟩`.
-/
theorem isoSet_nonempty (M : Model F E) {m : ℕ} (w : Pt E (m + 1))
    (p : lowW E (tr w).1 (tr w).2 × upUniG E (tr w).1.sum)
    (hi : ∀ a b, (A5.orbZ (tr w) p).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm) a b ∈ M.R)
    (Z0 : M.Mat (m + 1)) (φ : M.Iso (toMat M _ hi (isUnit_det_sub w p)) Z0) :
    (isoSet M.R (A5.orbZ (tr w) p) (M.Cok Z0) (M.eCls Z0) (lamK M Z0)).Nonempty := by
  obtain ⟨-, ⟨eq⟩⟩ := reindex (tr_sum w) M.R (A5.orbZ (tr w) p) (M.Cok Z0) (M.eCls Z0) (lamK M Z0)
  have e1 := isoEquiv M (toMat M _ hi (isUnit_det_sub w p)) Z0
  rw [toMat_map] at e1
  exact Set.nonempty_coe_sort.1 ⟨eq (e1 φ)⟩

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ _ M hOK n w`. Use `hSC F E M hOK` as an intermediate fact. Use `hOK.borel` as an intermediate fact. Use `hOK.haar.haar` as an intermediate fact. Use `hOK.haar.sf` as an intermediate fact.

Conclude with `transferPt hG hD M.mu M.R hOK.haar.volR w`.
-/
theorem ct (hSC : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] (E : Type) [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      SecondCountableTopology E) (hG : UnipotentProductMeasureInvariant) (hD : OrbitParametrisationsAgree) : InvariantUnipotentMeasuresExist := by
  intro F _ _ _ E _ _ _ _ _ M hOK n w
  have := hSC F E M hOK
  have := hOK.borel
  have := hOK.haar.haar
  have := hOK.haar.sf
  exact transferPt hG hD M.mu M.R hOK.haar.volR w

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK n w w'`. Use `top_of_OK M hOK` as an intermediate fact. Establish `hL` using `datum_of_OK M hOK`. Consider the cases of `n with`. Consider the case `zero`.

Establish `hψ : ∀ r ∈ M.R, M.psiR r = 1` using `fun r hr => by`. Use `(hL.selfDual 1).2 M.R.one_mem r hr` as an intermediate fact. Simplify using `using this`. Establish `hI : ∀ v : Pt E 0, A5.InGLR M.R (tr v)` using `fun v => ⟨fun a => (Fin.cast (tr_sum v) a).elim0, fun a => (Fin.cast (tr_sum v) a).elim0⟩`. Conclude with `(Formalism.FourierDecayAlt.P.zero_kernel_all_ones E M.R M.psiR hψ (tr w) (tr w') (by rw [tr_sum, tr_sum]) (hI w) (hI w')).symm`.

Consider the case `succ m`. Take `⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, hint⟩` from `hCT F E M hOK (m + 1) w`. Take `⟨μ₁', μ₂', i1', i2', i3', i4', v1', v2', hint'⟩` from `hCT F E M hOK (m + 1) w'`. Establish `hdet : IsUnit w.mat.det`. Rewrite using `[det_eq]`.

Conclude with `Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit (tr w)`. Establish `hfin` using `finite_S M hOK m w.mat.det hdet`. Establish `hzero : ∀ c ∉ hfin.toFinset, M.BB w c * conj (M.BB w' c) / (M.nAut c : ℂ) = 0`. Introduce `c hc`. Establish `h0 : M.BB w c = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hc (hfin.mem_toFinset.2 (exists_mat_of_BB_ne M w c hne))`. Rewrite using `[h0, zero_mul, zero_div]`. Rewrite using `[Model.Kk_succ, tsum_eq_sum hzero, ← Finset.sum_coe_sort hfin.toFinset]`. Establish `hne : ∀ a b : {c // c ∈ hfin.toFinset}, a ≠ b → ¬ ∃ φ : M.Cok (Quotient.out a.1) ≃ₗ[M.R] M.Cok (Quotient.out b.1), φ (M.eCls (Quotient.out a.1)) = M.eCls (Quotient.out b.1) ∧ ∀ c, lamK M (Quotient.out b.1) (φ c) = lamK M (Quotient.out a.1) c`.

Introduce and unpack `a b hab ⟨φ, he, hl⟩`. Apply `hab` to reduce the goal to its premises. Establish `h1 : Nonempty (M.Iso (Quotient.out a.1) (Quotient.out b.1))` using `⟨⟨φ, he, hl⟩⟩`. Establish `h2` using `Quotient.sound (s := M.isoSetoid m) h1`. Conclude with `Subtype.ext ((Quotient.out_eq a.1).symm.trans (h2.trans (Quotient.out_eq b.1)))`.

Establish `hex : ∀ p, IsInt M.R (A5.orbZ (tr w) p) → ∃ a : {c // c ∈ hfin.toFinset}, (isoSet M.R (A5.orbZ (tr w) p) (M.Cok (Quotient.out a.1)) (M.eCls (Quotient.out a.1)) (lamK M (Quotient.out a.1))).Nonempty`. Introduce `p hp`. Establish `hi` using `(reindex (tr_sum w) M.R (A5.orbZ (tr w) p) PUnit 0 0).1.2 hp`. Establish `hc : Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p)) ∈ hfin.toFinset`. Use `hfin.mem_toFinset.2 ⟨_, ?_, rfl⟩` and prove the remaining obligations.

Use `(toMat_det M _ hi _).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_submatrix_equiv_self, det_orbZ, det_eq]`. Use `⟨⟨_, hc⟩, ?_⟩` and prove the remaining obligations. Take `⟨φ⟩ : Nonempty (M.Iso (toMat M _ hi (isUnit_det_sub w p)) (Quotient.out (Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p)))))` from `Quotient.exact (s := M.isoSetoid m) (Quotient.out_eq (Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p)))).symm`. Conclude with `isoSet_nonempty M w p hi _ φ`.

Establish `key` using `Formalism.FourierDecayAlt.P.gram_kernel_identity E M.R M.psiR hL (tr w) (tr w') μ₁ μ₂ μ₁' μ₂' v1 v2 v1' v2' {c // c ∈ hfin.toFinset} (fun a => M.Cok (Quotient.out a.1)) (fun a => M.eCls (Quotient.out a.1)) (fun a => lamK M (Quotient.out a.1)) hne hex`. Rewrite using `[← key]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[BB_eq M w μ₁ μ₂ hint, BB_eq M w' μ₁' μ₂' hint']`. Both sides reduce to the same expression.
-/
theorem kk_of_ct (hCT : InvariantUnipotentMeasuresExist) : KKAll := by
  intro F _ _ _ E _ _ _ _ M hOK n w w'
  have := top_of_OK M hOK
  have hL := datum_of_OK M hOK
  cases n with
  | zero =>
    have hψ : ∀ r ∈ M.R, M.psiR r = 1 := fun r hr => by
      have := (hL.selfDual 1).2 M.R.one_mem r hr
      simpa using this
    have hI : ∀ v : Pt E 0, A5.InGLR M.R (tr v) := fun v =>
      ⟨fun a => (Fin.cast (tr_sum v) a).elim0, fun a => (Fin.cast (tr_sum v) a).elim0⟩
    exact (Formalism.FourierDecayAlt.P.zero_kernel_all_ones E M.R M.psiR hψ (tr w) (tr w')
      (by rw [tr_sum, tr_sum]) (hI w) (hI w')).symm
  | succ m =>
    obtain ⟨μ₁, μ₂, i1, i2, i3, i4, v1, v2, hint⟩ := hCT F E M hOK (m + 1) w
    obtain ⟨μ₁', μ₂', i1', i2', i3', i4', v1', v2', hint'⟩ := hCT F E M hOK (m + 1) w'
    have hdet : IsUnit w.mat.det := by
      rw [det_eq]; exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit (tr w)
    have hfin := finite_S M hOK m w.mat.det hdet
    have hzero : ∀ c ∉ hfin.toFinset, M.BB w c * conj (M.BB w' c) / (M.nAut c : ℂ) = 0 := by
      intro c hc
      have h0 : M.BB w c = 0 := by
        by_contra hne
        exact hc (hfin.mem_toFinset.2 (exists_mat_of_BB_ne M w c hne))
      rw [h0, zero_mul, zero_div]
    rw [Model.Kk_succ, tsum_eq_sum hzero, ← Finset.sum_coe_sort hfin.toFinset]
    have hne : ∀ a b : {c // c ∈ hfin.toFinset}, a ≠ b →
        ¬ ∃ φ : M.Cok (Quotient.out a.1) ≃ₗ[M.R] M.Cok (Quotient.out b.1),
          φ (M.eCls (Quotient.out a.1)) = M.eCls (Quotient.out b.1) ∧
            ∀ c, lamK M (Quotient.out b.1) (φ c) = lamK M (Quotient.out a.1) c := by
      rintro a b hab ⟨φ, he, hl⟩
      apply hab
      have h1 : Nonempty (M.Iso (Quotient.out a.1) (Quotient.out b.1)) := ⟨⟨φ, he, hl⟩⟩
      have h2 := Quotient.sound (s := M.isoSetoid m) h1
      exact Subtype.ext ((Quotient.out_eq a.1).symm.trans (h2.trans (Quotient.out_eq b.1)))
    have hex : ∀ p, IsInt M.R (A5.orbZ (tr w) p) → ∃ a : {c // c ∈ hfin.toFinset},
        (isoSet M.R (A5.orbZ (tr w) p) (M.Cok (Quotient.out a.1)) (M.eCls (Quotient.out a.1))
          (lamK M (Quotient.out a.1))).Nonempty := by
      intro p hp
      have hi := (reindex (tr_sum w) M.R (A5.orbZ (tr w) p) PUnit 0 0).1.2 hp
      have hc : Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p)) ∈ hfin.toFinset := by
        refine hfin.mem_toFinset.2 ⟨_, ?_, rfl⟩
        refine (toMat_det M _ hi _).trans ?_
        rw [Matrix.det_submatrix_equiv_self, det_orbZ, det_eq]
      refine ⟨⟨_, hc⟩, ?_⟩
      obtain ⟨φ⟩ : Nonempty (M.Iso (toMat M _ hi (isUnit_det_sub w p))
          (Quotient.out (Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p))))) :=
        Quotient.exact (s := M.isoSetoid m) (Quotient.out_eq
          (Quotient.mk (M.isoSetoid m) (toMat M _ hi (isUnit_det_sub w p)))).symm
      exact isoSet_nonempty M w p hi _ φ
    have key := Formalism.FourierDecayAlt.P.gram_kernel_identity E M.R M.psiR hL (tr w) (tr w') μ₁ μ₂ μ₁' μ₂'
      v1 v2 v1' v2' {c // c ∈ hfin.toFinset} (fun a => M.Cok (Quotient.out a.1))
      (fun a => M.eCls (Quotient.out a.1)) (fun a => lamK M (Quotient.out a.1)) hne hex
    rw [← key]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [BB_eq M w μ₁ μ₂ hint, BB_eq M w' μ₁' μ₂' hint']
    rfl

end Main

end Cls

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Mk

variable {K : Type} [CommRing K] {n : ℕ}

/- English proof (translation)
Simplify using `[mk]`.
-/
theorem mk_diag (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) (a : Fin n) :
    mk P x a a = 1 := by
  simp [mk]

/- English proof (translation)
Simplify using `[mk, hab, h]`.
-/
theorem mk_pos (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hab : a ≠ b) (h : P (a, b)) : mk P x a b = x ⟨(a, b), h⟩ := by
  simp [mk, hab, h]

/- English proof (translation)
Simplify using `[mk, hab, h]`.
-/
theorem mk_neg (P : Fin n × Fin n → Prop) [DecidablePred P] (x : {p // P p} → K) {a b : Fin n}
    (hab : a ≠ b) (h : ¬ P (a, b)) : mk P x a b = 0 := by
  simp [mk, hab, h]

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[mk_diag, h1]`. Distinguish the cases in `h : P (a, b)`.

Rewrite using `[mk_pos P _ hab h]`. Rewrite using `[mk_neg P _ hab h, h0 a b hab h]`.
-/
theorem mk_coords (P : Fin n × Fin n → Prop) [DecidablePred P] (A : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ a, A a a = 1) (h0 : ∀ a b, a ≠ b → ¬ P (a, b) → A a b = 0) :
    mk P (fun p : {p // P p} => A p.1.1 p.1.2) = A := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [mk_diag, h1]
  · by_cases h : P (a, b)
    · rw [mk_pos P _ hab h]
    · rw [mk_neg P _ hab h, h0 a b hab h]

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_diag P x⟩` and prove the remaining obligations. Establish `hij' : i < j` using `hij`. Conclude with `mk_neg P x hij'.ne (fun hp => lt_asymm hij' (hP (i, j) hp))`.
-/
theorem isLowUni_mk (P : Fin n × Fin n → Prop) [DecidablePred P] (hP : ∀ p, P p → p.2 < p.1)
    (x : {p // P p} → K) : IsLowUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_diag P x⟩
  have hij' : i < j := hij
  exact mk_neg P x hij'.ne (fun hp => lt_asymm hij' (hP (i, j) hp))

/- English proof (translation)
Use `⟨fun i j hij => ?_, mk_diag P x⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Conclude with `mk_neg P x hij'.ne' (fun hp => lt_asymm hij' (hP (i, j) hp))`.
-/
theorem isUpUni_mk (P : Fin n × Fin n → Prop) [DecidablePred P] (hP : ∀ p, P p → p.1 < p.2)
    (x : {p // P p} → K) : IsUpUni (mk P x) := by
  refine ⟨fun i j hij => ?_, mk_diag P x⟩
  have hij' : j < i := hij
  exact mk_neg P x hij'.ne' (fun hp => lt_asymm hij' (hP (i, j) hp))

end Mk

section Trans

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant] {n : ℕ}

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [mk]`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`.
-/
theorem continuous_mk (P : Fin n × Fin n → Prop) [DecidablePred P] :
    Continuous (fun x : {p // P p} → K => mk P x) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [mk]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

end Trans

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Shapes

variable {K : Type} [CommRing K] {n : ℕ}

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Use `first`. Consider the case `exact L.smul_mem (⟨A i k, hA i k⟩ : R) (hY k j)`.

Consider the case `(have h := L.smul_mem (⟨A i k, hA i k⟩ : R) (hY k j); simpa [Subring.smul_def] using h)`.
-/
theorem mul_mem_left (R : Subring K) (L : Submodule R K) {A Y : Matrix (Fin n) (Fin n) K} (hA : IsInt R A)
    (hY : ∀ i j, Y i j ∈ L) : ∀ i j, (A * Y) i j ∈ L := by
  intro i j
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  first
    | exact L.smul_mem (⟨A i k, hA i k⟩ : R) (hY k j)
    | (have h := L.smul_mem (⟨A i k, hA i k⟩ : R) (hY k j); simpa [Subring.smul_def] using h)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `first`.

Consider the case `exact L.smul_mem (⟨A k j, hA k j⟩ : R) (hY i k)`. Consider the case `(have h := L.smul_mem (⟨A k j, hA k j⟩ : R) (hY i k); simpa [Subring.smul_def] using h)`.
-/
theorem mul_mem_right (R : Subring K) (L : Submodule R K) {A Y : Matrix (Fin n) (Fin n) K} (hA : IsInt R A)
    (hY : ∀ i j, Y i j ∈ L) : ∀ i j, (Y * A) i j ∈ L := by
  intro i j
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  rw [mul_comm]
  first
    | exact L.smul_mem (⟨A k j, hA k j⟩ : R) (hY i k)
    | (have h := L.smul_mem (⟨A k j, hA k j⟩ : R) (hY i k); simpa [Subring.smul_def] using h)

end Shapes

section Avg

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant] (R : Subring K) {n : ℕ}

def nu0 (n : ℕ) : Measure (({p // PL n p} → K) × ({p // PU n p} → K)) :=
  (Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)

def SR (n : ℕ) : Set (({p // PL n p} → K) × ({p // PU n p} → K)) :=
  {xy | (∀ p, xy.1 p ∈ R) ∧ ∀ p, xy.2 p ∈ R}

def avg (Φ : Matrix (Fin n) (Fin n) K → ℂ) (Z : Matrix (Fin n) (Fin n) K) : ℂ :=
  ∫ xy in SR R n, Φ (mk (PL n) xy.1 * Z * mk (PU n) xy.2) ∂(nu0 μ n)

end Avg

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Orb

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant] (R : Subring K)
  (ψ : AddChar K ℂ) (s : List ℕ) (t : ℕ → Kˣ) (sb : Fin s.sum → Fin s.sum → Bool)

def I1 (H : Matrix (Fin s.sum) (Fin s.sum) K → ℂ) : ℂ :=
  ∫ xy : ({p // PL s.sum p} → K) × ({p // PN sb p} → K),
    H (mk (PL s.sum) xy.1 * pt s t * mk (PN sb) xy.2) *
      ψ (sLow (mk (PL s.sum) xy.1) + sUp (mk (PN sb) xy.2))
    ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

def I2 (H : Matrix (Fin s.sum) (Fin s.sum) K → ℂ) : ℂ :=
  ∫ xy : ({p // PW sb p} → K) × ({p // PU s.sum p} → K),
    H (mk (PW sb) xy.1 * pt s t * mk (PU s.sum) xy.2) *
      ψ (sLow (mk (PW sb) xy.1) + sUp (mk (PU s.sum) xy.2))
    ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

variable {sb}

end Orb

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Fub

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [SigmaFinite μ] [μ.IsAddLeftInvariant] (R : Subring K)
  (ψ : AddChar K ℂ) (s : List ℕ) (t : ℕ → Kˣ) {sb : Fin s.sum → Fin s.sum → Bool}

instance unipotentProductMeasureLocallyFinite [IsLocallyFiniteMeasure μ] (n : ℕ) :
    IsLocallyFiniteMeasure (nu0 μ n : Measure (({p // PL n p} → K) × ({p // PU n p} → K))) := by
  unfold nu0; infer_instance

instance unipotentProductMeasureSFinite (n : ℕ) : SFinite (nu0 μ n : Measure (({p // PL n p} → K) × ({p // PU n p} → K))) := by
  unfold nu0; infer_instance

end Fub

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Core

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

end Core

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

def fam {E : Type} {n : ℕ} (Φ : Matrix (Fin n) (Fin n) E → ℂ) : ∀ k : ℕ, Matrix (Fin k) (Fin k) E → ℂ :=
  fun k Z => if h : k = n then Φ (Z.submatrix (finCongr h.symm) (finCongr h.symm)) else 0

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

end Loc

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def rhs (M : Model F E) (m : ℕ) (ga : Eˣ → ℂ) (Φ : Matrix (Fin (m + 2)) (Fin (m + 2)) E → ℂ) (t c : Eˣ) : ℂ :=
  ((M.modK (t : E) ^ (-(((m : ℝ) + 1) ^ 2 / 2)) * M.modK ((m : E) + 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑ᶠ (z : Eˣ) (_ : (z : E) ^ (m + 2) = (-1) ^ (m + 1) * ((c : E) * (t : E) ^ (m + 1))),
      ((M.modK (z : E) ^ (((m : ℝ) + 1) ^ 2 / 2) : ℝ) : ℂ) * ga (z * t) *
        M.psiR (((m : E) + 2) * (z : E) * ((t⁻¹ : Eˣ) : E)) * Formalism.MainNotions.ThinScalesBound.Om M Φ (Formalism.MainNotions.ThinScalesBound.ptZ m z)

end Loc

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def AvgAt (M : Model F E) : Prop :=
  ∀ (n : ℕ) (Φ : Matrix (Fin n) (Fin n) E → ℂ) (Ω : Set E) (L₀ Λ₀ : Submodule M.R E),
    A6.IsLat L₀.toAddSubgroup → A6.IsLat Λ₀.toAddSubgroup →
    (∀ Z, Φ Z ≠ 0 → ∀ i j, Z i j ∈ L₀) →
    (∀ Z Y : Matrix (Fin n) (Fin n) E, (Z.det ∈ Ω ∨ -Z.det ∈ Ω) → (∀ i j, Y i j ∈ Λ₀) → Φ (Z + Y) = Φ Z) →
    ∃ Φ' : Matrix (Fin n) (Fin n) E → ℂ,
      (∀ Z a b : Matrix (Fin n) (Fin n) E, IsLowUni a → IsInt M.R a → IsUpUni b → IsInt M.R b →
        Φ' (a * Z * b) = Φ' Z) ∧
      (∀ Z, Φ' Z ≠ 0 → ∀ i j, Z i j ∈ L₀) ∧
      (∀ Z Y : Matrix (Fin n) (Fin n) E, (Z.det ∈ Ω ∨ -Z.det ∈ Ω) → (∀ i j, Y i j ∈ Λ₀) → Φ' (Z + Y) = Φ' Z) ∧
      ∀ w : Pt E n, (w.mat.det ∈ Ω ∨ -w.mat.det ∈ Ω) → Formalism.MainNotions.ThinScalesBound.Om M Φ' w = Formalism.MainNotions.ThinScalesBound.Om M Φ w

end Loc

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.MainNotions.S.Loc Formalism.MainNotions.LocalModelPeriodLattices Formalism.FourierDecayAlt
open scoped Topology

namespace Formalism.MainNotions.LocalOrbitGerms

namespace Germ

section Comb

variable {E : Type} [CommRing E]

/- English proof (translation)
The claim follows from `| [], a, b, h, _ => by simp at h | (t, s) :: bs, a, b, ha, hb => by simp only [List.map_cons, List.sum_cons] at ha hb simp only [sameBlock, List.map_cons, blk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] by_cases h1 : a < (s : ℕ) · by_cases h2 : b < (s : ℕ) · simp [h1, …`.
-/
theorem sameBlock_iff : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    b < (bs.map (fun b => (b.2 : ℕ))).sum →
    (sameBlock bs a b = true ↔ blk (bs.map (fun b => (b.2 : ℕ))) a = blk (bs.map (fun b => (b.2 : ℕ))) b)
  | [], a, b, h, _ => by simp at h
  | (t, s) :: bs, a, b, ha, hb => by
    simp only [List.map_cons, List.sum_cons] at ha hb
    simp only [sameBlock, List.map_cons, blk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : a < (s : ℕ)
    · by_cases h2 : b < (s : ℕ)
      · simp [h1, h2]
      · have h3 : ¬ ((s : ℕ) ≤ a) := by omega
        simp only [h1, h2, h3, and_false, false_and, or_self, if_true, if_false, false_iff]
        omega
    · by_cases h2 : b < (s : ℕ)
      · have h3 : ¬ ((s : ℕ) ≤ b) := by omega
        simp only [h1, h2, h3, and_false, false_and, or_self, if_true, if_false, false_iff]
        omega
      · have h3 : (s : ℕ) ≤ a := by omega
        have h4 : (s : ℕ) ≤ b := by omega
        have := sameBlock_iff bs (a - s) (b - s) (by omega) (by omega)
        simp [h1, h2, h3, h4, this]

/- English proof (translation)
Conclude with `Cls.simpleLow_eq A`.
-/
theorem simpleLow_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : simpleLow A = sLow A := by
  exact Cls.simpleLow_eq A

/- English proof (translation)
Conclude with `Cls.simpleUp_eq A`.
-/
theorem simpleUp_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : simpleUp A = sUp A := by
  exact Cls.simpleUp_eq A

end Comb

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

abbrev szL (bl : List (Eˣ × ℕ+)) : List ℕ := bl.map (fun b : Eˣ × ℕ+ => (b.2 : ℕ))

abbrev scL (bl : List (Eˣ × ℕ+)) : ℕ → Eˣ := fun i => (bl.map Prod.fst).getD i 1

end Loc

end Germ

end Formalism.MainNotions.LocalOrbitGerms

end

noncomputable section

namespace Formalism.MainNotions.LocalOrbitGerms

open Formalism.MainNotions.LocalModelPeriodLattices

/- English proof (translation)
Conclude with `Cls.ct (@fun F _ _ _ E _ _ _ _ M hOK => secondCountable_of_OK M hOK) (grp shear) (dec shear merge)`.
-/
theorem ctAll : InvariantUnipotentMeasuresExist := by
  exact Cls.ct (@fun F _ _ _ E _ _ _ _ M hOK => secondCountable_of_OK M hOK) (grp shear) (dec shear merge)

/- English proof (translation)
Conclude with `Cls.kk_of_ct ctAll`.
-/
theorem KKAll_proved : KKAll := by
  exact Cls.kk_of_ct ctAll

end Formalism.MainNotions.LocalOrbitGerms

end
