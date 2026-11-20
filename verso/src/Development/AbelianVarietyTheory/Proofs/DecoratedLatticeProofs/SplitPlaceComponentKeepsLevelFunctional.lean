import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountIdx
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralVectorsComponentIffIntegralFrameCoordStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDivStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.StabFnLev

open Formalism.UG

section Abstract

variable {A R N : Type} [CommRing A] [CommRing R] [Algebra R A] {_ : AddCommGroup N} {_ : Module R N} {n : Type} [Fintype n]
  [DecidableEq n]

/- English proof (translation)
Establish `hmap : ∀ h : GL n A, (∀ y ∈ Λ, (h : Matrix n n A) *ᵥ y - y ∈ Λ₀) → ∀ y ∈ Λ, (h : Matrix n n A) *ᵥ y ∈ Λ`. Introduce `h hh y hy`. Use `Λ.add_mem (h0 (hh y hy)) hy` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hg : g ∈ stabGL Λ`.

Introduce `y`. Use `⟨hmap g h1 y, fun hy => ?_⟩` and prove the remaining obligations. Use `hmap g⁻¹ h2 _ hy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Use `⟨hg, fun x => ?_⟩` and prove the remaining obligations.

Establish `hd` using `hf ⟨(g : Matrix n n A) *ᵥ (x : n → A) - x, Λ.sub_mem (hmap g h1 x x.2) x.2⟩ (h1 x x.2)`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Use `hd using 2` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext rfl`.
-/
theorem mem_stabFun_of_sub (Λ₀ Λ : Submodule R (n → A)) (f : Λ →ₗ[R] N)
    (hf : ∀ x : Λ, (x : n → A) ∈ Λ₀ → f x = 0) (h0 : Λ₀ ≤ Λ) (g : GL n A)
    (h1 : ∀ y ∈ Λ, (g : Matrix n n A) *ᵥ y - y ∈ Λ₀)
    (h2 : ∀ y ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ y - y ∈ Λ₀) :
    g ∈ stabFun Λ f := by
  have hmap : ∀ h : GL n A, (∀ y ∈ Λ, (h : Matrix n n A) *ᵥ y - y ∈ Λ₀) → ∀ y ∈ Λ, (h : Matrix n n A) *ᵥ y ∈ Λ := by
    intro h hh y hy
    have := Λ.add_mem (h0 (hh y hy)) hy
    rwa [sub_add_cancel] at this
  have hg : g ∈ stabGL Λ := by
    intro y
    refine ⟨hmap g h1 y, fun hy => ?_⟩
    have := hmap g⁻¹ h2 _ hy
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  refine ⟨hg, fun x => ?_⟩
  have hd := hf ⟨(g : Matrix n n A) *ᵥ (x : n → A) - x, Λ.sub_mem (hmap g h1 x x.2) x.2⟩ (h1 x x.2)
  rw [← sub_eq_zero, ← map_sub]
  convert hd using 2
  exact Subtype.ext rfl

end Abstract

section Alg

variable {Rg : Type} [CommRing Rg] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem mulVec_single_apply (M : Matrix ι ι Rg) (j : ι) (t : Rg) (r : ι) : (M *ᵥ Pi.single j t) r = M r j * t := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/- English proof (translation)
Establish `hsingle : ∀ (s : ι) (t : Rg), t ∈ S → (s = i0 → ∃ c ∈ S, t = π * c) → (∀ r, (Pi.single s t : ι → Rg) r ∈ S) ∧ ∃ c ∈ S, (Pi.single s t : ι → Rg) i0 = π * c`. Introduce `s t ht hs`. Use `⟨fun r => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hr : r = s`. Substitute `hr` using the available equality.

Simplify using `using ht`. Rewrite using `[Pi.single_eq_of_ne hr]`. Conclude with `S.zero_mem`. Distinguish the cases in `hs' : i0 = s`. Substitute `hs'` using the available equality.

Simplify using `using hs rfl`. Conclude with `⟨0, S.zero_mem, by rw [Pi.single_eq_of_ne hs', mul_zero]⟩`. Introduce `r s`. Distinguish the cases in `hs : s = i0`. Substitute `hs` using the available equality.

Distinguish the cases in `hr : r = s`. Substitute `hr` using the available equality. Take `⟨-, c, hc, he⟩` from `hM _ ((hsingle r π hπ (fun _ => ⟨1, S.one_mem, (mul_one π).symm⟩)).1) ((hsingle r π hπ (fun _ => ⟨1, S.one_mem, (mul_one π).symm⟩)).2)`. Rewrite `he` using `[mulVec_single_apply]`. Establish `: (M : Matrix ι ι Rg) r r = c`.

Establish `he' : π * (M : Matrix ι ι Rg) r r = π * c` using `by rw [← he]; ring`. Conclude with `hπu.mul_left_cancel he'`. Rewrite using `[this]`. Conclude with `hc`. Establish `h1` using `(hMi _ ((hsingle r 1 S.one_mem (fun h => absurd h hr)).1) ((hsingle r 1 S.one_mem (fun h => absurd h hr)).2)).1 s`.

Rewrite `h1` using `[mulVec_single_apply, mul_one]`. Rewrite using `[hU' r s]`. Conclude with `hτ _ h1`. Establish `h1` using `(hM _ ((hsingle s 1 S.one_mem (fun h => absurd h hs)).1) ((hsingle s 1 S.one_mem (fun h => absurd h hs)).2)).1 r`. Rewrite `h1` using `[mulVec_single_apply, mul_one]`. Then use the resulting hypothesis.
-/
theorem alg_int (τ : Rg →+* Rg) (S : Subring Rg) (π : Rg) (i0 : ι) (M : GL ι Rg)
    (hU' : ∀ r s, (M : Matrix ι ι Rg) r s = τ (((M⁻¹ : GL ι Rg) : Matrix ι ι Rg) s r))
    (hτ : ∀ x ∈ S, τ x ∈ S) (hπ : π ∈ S) (hπu : IsUnit π)
    (hM : ∀ y : ι → Rg, (∀ r, y r ∈ S) → (∃ c ∈ S, y i0 = π * c) →
      (∀ r, ((M : Matrix ι ι Rg) *ᵥ y) r ∈ S) ∧ ∃ c ∈ S, ((M : Matrix ι ι Rg) *ᵥ y) i0 = π * c)
    (hMi : ∀ y : ι → Rg, (∀ r, y r ∈ S) → (∃ c ∈ S, y i0 = π * c) →
      (∀ r, (((M⁻¹ : GL ι Rg) : Matrix ι ι Rg) *ᵥ y) r ∈ S) ∧ ∃ c ∈ S, (((M⁻¹ : GL ι Rg) : Matrix ι ι Rg) *ᵥ y) i0 = π * c) :
    ∀ r s, (M : Matrix ι ι Rg) r s ∈ S := by
  have hsingle : ∀ (s : ι) (t : Rg), t ∈ S → (s = i0 → ∃ c ∈ S, t = π * c) →
      (∀ r, (Pi.single s t : ι → Rg) r ∈ S) ∧ ∃ c ∈ S, (Pi.single s t : ι → Rg) i0 = π * c := by
    intro s t ht hs
    refine ⟨fun r => ?_, ?_⟩
    · by_cases hr : r = s
      · subst hr; simpa using ht
      · rw [Pi.single_eq_of_ne hr]; exact S.zero_mem
    · by_cases hs' : i0 = s
      · subst hs'; simpa using hs rfl
      · exact ⟨0, S.zero_mem, by rw [Pi.single_eq_of_ne hs', mul_zero]⟩
  intro r s
  by_cases hs : s = i0
  · subst hs
    by_cases hr : r = s
    · subst hr
      obtain ⟨-, c, hc, he⟩ := hM _ ((hsingle r π hπ (fun _ => ⟨1, S.one_mem, (mul_one π).symm⟩)).1)
        ((hsingle r π hπ (fun _ => ⟨1, S.one_mem, (mul_one π).symm⟩)).2)
      rw [mulVec_single_apply] at he
      have : (M : Matrix ι ι Rg) r r = c := by
        have he' : π * (M : Matrix ι ι Rg) r r = π * c := by rw [← he]; ring
        exact hπu.mul_left_cancel he'
      rw [this]; exact hc
    · have h1 := (hMi _ ((hsingle r 1 S.one_mem (fun h => absurd h hr)).1)
        ((hsingle r 1 S.one_mem (fun h => absurd h hr)).2)).1 s
      rw [mulVec_single_apply, mul_one] at h1
      rw [hU' r s]
      exact hτ _ h1
  · have h1 := (hM _ ((hsingle s 1 S.one_mem (fun h => absurd h hs)).1)
      ((hsingle s 1 S.one_mem (fun h => absurd h hs)).2)).1 r
    rwa [mulVec_single_apply, mul_one] at h1

/- English proof (translation)
Use `set Mm : Matrix ι ι Rg := (M : Matrix ι ι Rg)`. Use `set Mi : Matrix ι ι Rg := ((M⁻¹ : GL ι Rg) : Matrix ι ι Rg)`. Establish `hMi : Mm * Mi = 1` using `by simp [Mm, Mi]`. Establish `hiint : ∀ r s, Mi r s ∈ S` using `fun r s => by rw [hU]; exact hτ _ (hint s r)`. Use `choose c hcS hc using hrow`.

Establish `hrowi : ∀ s, Mi i0 s - (1 : Matrix ι ι Rg) i0 s = π * (-∑ b, c b * Mi b s)`. Introduce `s`. Establish `e : Mi - 1 = (1 - Mm) * Mi` using `by rw [sub_mul, one_mul, hMi]`. Establish `e2` using `congrFun (congrFun e i0) s`. Rewrite `e2` using `[Matrix.sub_apply]`.

Rewrite using `[e2, Matrix.mul_apply, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hb` using `hc b`. Rewrite using `[Matrix.sub_apply]`. Rewrite using `[show (1 : Matrix ι ι Rg) i0 b - Mm i0 b = -(Mm i0 b - (1 : Matrix ι ι Rg) i0 b) by ring, hb]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hci : ∀ s, -∑ b, c b * Mi b s ∈ S` using `fun s => S.neg_mem (S.sum_mem fun b _ => S.mul_mem (hcS b) (hiint b s))`. Establish `hcol : ∀ r, Mm r i0 - (1 : Matrix ι ι Rg) r i0 = π' * τ (-∑ b, c b * Mi b r)`. Introduce `r`. Establish `e` using `congrArg τ (hrowi r)`.

Rewrite `e` using `[map_sub, map_mul, hτπ, ← hU' r i0]`. Rewrite using `[← e]`. Use `congr 1`. Distinguish the cases in `hr : r = i0`. Substitute `hr` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hr, Matrix.one_apply_ne (Ne.symm hr), map_zero]`. Use `set d' : ι → Rg := fun r => τ (-∑ b, c b * Mi b r) with hd'`. Establish `hd'S : ∀ r, d' r ∈ S` using `fun r => hτ _ (hci r)`. Use `set y' : ι → Rg := Function.update y i0 0 with hy'`.

Establish `hy'S : ∀ r, y' r ∈ S`. Introduce `r`. Distinguish the cases in `hr : r = i0`. Substitute `hr` using the available equality. Simplify using `[y', S.zero_mem]`.

Rewrite using `[hy', Function.update_of_ne hr]`. Conclude with `hy r hr`. Establish `hyd : y = y' + Pi.single i0 (y i0)`. Use function extensionality and compare the values at `r`. Distinguish the cases in `hr : r = i0`.

Substitute `hr` using the available equality. Simplify using `[y']`. Simplify using `[y', Function.update_of_ne hr, Pi.single_eq_of_ne hr]`. Establish `hsplit : Mm *ᵥ y - y = (Mm - 1) *ᵥ y' + fun r => (Mm r i0 - (1 : Matrix ι ι Rg) r i0) * y i0`. Use function extensionality and compare the values at `r`.

Use `conv_lhs => rw [hyd]`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_add, mulVec_single_apply, Matrix.sub_mulVec, Matrix.one_mulVec]`. Rewrite using `[show (Pi.single i0 (y i0) : ι → Rg) r = (1 : Matrix ι ι Rg) r i0 * y i0 by`. Rewrite using `[← mulVec_single_apply, Matrix.one_mulVec]]`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `have hA : ∀ r, ((Mm - 1) *ᵥ y') r ∈ S := fun r => S.sum_mem fun b _ => S.mul_mem (S.sub_mem (hint r b) (by by_cases h : r = b <;> simp [Matrix.one_apply, h, S.one_mem, S.zero_mem])) (hy'S b)`. Establish `hB : ∀ r, (Mm r i0 - (1 : Matrix ι ι Rg) r i0) * y i0 = d' r * (π' * y i0)`. Introduce `r`. Rewrite using `[hcol r]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun r => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit, Pi.add_apply, hB r]`. Conclude with `S.add_mem (hA r) (S.mul_mem (hd'S r) hy0)`. Take `⟨cc, hcc, dd, hdd, hcd⟩` from `hcop`. Establish `hA0 : ((Mm - 1) *ᵥ y') i0 = π * ∑ b, c b * y' b`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, hc b]`. Expand and normalize the polynomial expressions, which then agree. Use `set t := (Mm i0 i0 - (1 : Matrix ι ι Rg) i0 i0) * y i0 with ht`.

Establish `ht1 : t = d' i0 * (π' * y i0)` using `hB i0`. Establish `ht2 : t = π * (c i0 * y i0)` using `by rw [ht, hc i0]; ring`. Establish `ht3 : t = π * (t * cc + dd * c i0 * (π' * y i0))`. Combine the equalities or inequalities in the displayed calculation. Use `⟨∑ b, c b * y' b + (t * cc + dd * c i0 * (π' * y i0)), ?_, ?_⟩` and prove the remaining obligations.

Use `S.add_mem (S.sum_mem fun b _ => S.mul_mem (hcS b) (hy'S b)) ?_` and prove the remaining obligations. Use `S.add_mem (S.mul_mem ?_ hcc) (S.mul_mem (S.mul_mem hdd (hcS i0)) hy0)` and prove the remaining obligations. Rewrite using `[ht1]`. Conclude with `S.mul_mem (hd'S i0) hy0`. Rewrite using `[hsplit, Pi.add_apply, hA0] show π * _ + t = _ conv_lhs => rw [ht3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem alg_sub (τ : Rg →+* Rg) (S : Subring Rg) (π π' : Rg) (i0 : ι) (M : GL ι Rg)
    (hU : ∀ r s, ((M⁻¹ : GL ι Rg) : Matrix ι ι Rg) r s = τ ((M : Matrix ι ι Rg) s r))
    (hU' : ∀ r s, (M : Matrix ι ι Rg) r s = τ (((M⁻¹ : GL ι Rg) : Matrix ι ι Rg) s r))
    (hτ : ∀ x ∈ S, τ x ∈ S) (hτπ : τ π = π') (hint : ∀ r s, (M : Matrix ι ι Rg) r s ∈ S)
    (hcop : ∃ c ∈ S, ∃ d ∈ S, π * c + π' * d = 1)
    (hrow : ∀ s, ∃ c ∈ S, (M : Matrix ι ι Rg) i0 s - (1 : Matrix ι ι Rg) i0 s = π * c)
    (y : ι → Rg) (hy : ∀ r, r ≠ i0 → y r ∈ S) (hy0 : π' * y i0 ∈ S) :
    (∀ r, ((M : Matrix ι ι Rg) *ᵥ y - y) r ∈ S) ∧ ∃ c ∈ S, ((M : Matrix ι ι Rg) *ᵥ y - y) i0 = π * c := by
  set Mm : Matrix ι ι Rg := (M : Matrix ι ι Rg)
  set Mi : Matrix ι ι Rg := ((M⁻¹ : GL ι Rg) : Matrix ι ι Rg)
  have hMi : Mm * Mi = 1 := by simp [Mm, Mi]
  have hiint : ∀ r s, Mi r s ∈ S := fun r s => by rw [hU]; exact hτ _ (hint s r)
  choose c hcS hc using hrow

  have hrowi : ∀ s, Mi i0 s - (1 : Matrix ι ι Rg) i0 s = π * (-∑ b, c b * Mi b s) := by
    intro s
    have e : Mi - 1 = (1 - Mm) * Mi := by rw [sub_mul, one_mul, hMi]
    have e2 := congrFun (congrFun e i0) s
    rw [Matrix.sub_apply] at e2
    rw [e2, Matrix.mul_apply, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb := hc b
    rw [Matrix.sub_apply]
    rw [show (1 : Matrix ι ι Rg) i0 b - Mm i0 b = -(Mm i0 b - (1 : Matrix ι ι Rg) i0 b) by ring, hb]
    ring
  have hci : ∀ s, -∑ b, c b * Mi b s ∈ S := fun s =>
    S.neg_mem (S.sum_mem fun b _ => S.mul_mem (hcS b) (hiint b s))

  have hcol : ∀ r, Mm r i0 - (1 : Matrix ι ι Rg) r i0 = π' * τ (-∑ b, c b * Mi b r) := by
    intro r
    have e := congrArg τ (hrowi r)
    rw [map_sub, map_mul, hτπ, ← hU' r i0] at e
    rw [← e]
    congr 1
    by_cases hr : r = i0
    · subst hr; simp
    · rw [Matrix.one_apply_ne hr, Matrix.one_apply_ne (Ne.symm hr), map_zero]
  set d' : ι → Rg := fun r => τ (-∑ b, c b * Mi b r) with hd'
  have hd'S : ∀ r, d' r ∈ S := fun r => hτ _ (hci r)

  set y' : ι → Rg := Function.update y i0 0 with hy'
  have hy'S : ∀ r, y' r ∈ S := by
    intro r
    by_cases hr : r = i0
    · subst hr; simp [y', S.zero_mem]
    · rw [hy', Function.update_of_ne hr]; exact hy r hr
  have hyd : y = y' + Pi.single i0 (y i0) := by
    funext r
    by_cases hr : r = i0
    · subst hr; simp [y']
    · simp [y', Function.update_of_ne hr, Pi.single_eq_of_ne hr]
  have hsplit : Mm *ᵥ y - y = (Mm - 1) *ᵥ y' + fun r => (Mm r i0 - (1 : Matrix ι ι Rg) r i0) * y i0 := by
    funext r
    conv_lhs => rw [hyd]
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_add, mulVec_single_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [show (Pi.single i0 (y i0) : ι → Rg) r = (1 : Matrix ι ι Rg) r i0 * y i0 by
      rw [← mulVec_single_apply, Matrix.one_mulVec]]
    ring
  have hA : ∀ r, ((Mm - 1) *ᵥ y') r ∈ S := fun r =>
    S.sum_mem fun b _ => S.mul_mem (S.sub_mem (hint r b) (by by_cases h : r = b <;> simp [Matrix.one_apply, h, S.one_mem, S.zero_mem])) (hy'S b)
  have hB : ∀ r, (Mm r i0 - (1 : Matrix ι ι Rg) r i0) * y i0 = d' r * (π' * y i0) := by
    intro r; rw [hcol r]; ring
  refine ⟨fun r => ?_, ?_⟩
  · rw [hsplit, Pi.add_apply, hB r]
    exact S.add_mem (hA r) (S.mul_mem (hd'S r) hy0)
  · obtain ⟨cc, hcc, dd, hdd, hcd⟩ := hcop
    have hA0 : ((Mm - 1) *ᵥ y') i0 = π * ∑ b, c b * y' b := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.sub_apply, hc b]; ring
    set t := (Mm i0 i0 - (1 : Matrix ι ι Rg) i0 i0) * y i0 with ht
    have ht1 : t = d' i0 * (π' * y i0) := hB i0
    have ht2 : t = π * (c i0 * y i0) := by rw [ht, hc i0]; ring
    have ht3 : t = π * (t * cc + dd * c i0 * (π' * y i0)) := by
      calc t = t * (π * cc + π' * dd) := by rw [hcd, mul_one]
        _ = π * (t * cc) + dd * (π' * t) := by ring
        _ = π * (t * cc + dd * c i0 * (π' * y i0)) := by rw [ht2]; ring
    refine ⟨∑ b, c b * y' b + (t * cc + dd * c i0 * (π' * y i0)), ?_, ?_⟩
    · refine S.add_mem (S.sum_mem fun b _ => S.mul_mem (hcS b) (hy'S b)) ?_
      refine S.add_mem (S.mul_mem ?_ hcc) (S.mul_mem (S.mul_mem hdd (hcS i0)) hy0)
      rw [ht1]; exact S.mul_mem (hd'S i0) hy0
    · rw [hsplit, Pi.add_apply, hA0]
      show π * _ + t = _
      conv_lhs => rw [ht3]
      ring

end Alg

end GlobalTheory.StabFnLev

namespace GlobalTheory.StabFnLev

open Formalism.UG Formalism.BasicNotions NumberField IsDedekindDomain
open scoped TensorProduct

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[hLb, Formalism.MainNotions.Gaps.LevGap.mem_latT]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, fun r hr => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, hd⟩` from `h i0`. Take `⟨c, rfl⟩` from `hd hi0`. Conclude with `⟨c, by rw [hs]; push_cast; ring⟩`. Take `⟨s, hs, -⟩` from `h r`. Conclude with `⟨s, hs.symm⟩`.

Introduce and unpack `⟨⟨c, hc⟩, h⟩ r`. Distinguish the cases in `hr : r = i0`. Substitute `hr` using the available equality. Conclude with `⟨t * c, by rw [hc]; push_cast; ring, fun _ => dvd_mul_right _ _⟩`. Take `⟨s, hs⟩` from `h r hr`.

Use `⟨s, hs.symm, fun h' => absurd (Fin.ext (by omega)) hr⟩` and prove the remaining obligations.
-/
theorem lb_eq_latT {n : ℕ} (i0 : Fin n) (hi0 : i0.1 + 1 = n) (t : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ r : Fin n, ∃ s : 𝓞 E, x r = (s : E) ∧ (r.1 + 1 = n → t ∣ s)) :
    Lb = Formalism.MainNotions.Gaps.LevGap.latT i0 t := by
  ext x
  rw [hLb, Formalism.MainNotions.Gaps.LevGap.mem_latT]
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_⟩
    · obtain ⟨s, hs, hd⟩ := h i0
      obtain ⟨c, rfl⟩ := hd hi0
      exact ⟨c, by rw [hs]; push_cast; ring⟩
    · obtain ⟨s, hs, -⟩ := h r
      exact ⟨s, hs.symm⟩
  · rintro ⟨⟨c, hc⟩, h⟩ r
    by_cases hr : r = i0
    · subst hr
      exact ⟨t * c, by rw [hc]; push_cast; ring, fun _ => dvd_mul_right _ _⟩
    · obtain ⟨s, hs⟩ := h r hr
      refine ⟨s, hs.symm, fun h' => absurd (Fin.ext (by omega)) hr⟩

/- English proof (translation)
Rewrite using `[lb_eq_latT i0 hi0 t Lb hLb]`. Use `show y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.MainNotions.Gaps.LevGap.diagLat (Formalism.MainNotions.Gaps.LevGap.vecAt i0 (t : E))) ↔ _`. Rewrite using `[Formalism.MainNotions.Gaps.LG.fm_mem_latS]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨fun r => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h r`. Rewrite using `[hc]`. Distinguish the cases in `hr : r = i0`. Substitute `hr` using the available equality.

Rewrite using `[Formalism.MainNotions.Gaps.LevGap.vecAt_same]`. Conclude with `(intV E v).mul_mem (Formalism.MainNotions.Gaps.LG.fm_incl_mem v t) c.2`. Rewrite using `[Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]`. Conclude with `c.2`. Take `⟨c, hc⟩` from `h i0`.

Conclude with `⟨c, c.2, by rw [hc, Formalism.MainNotions.Gaps.LevGap.vecAt_same]⟩`. Introduce and unpack `⟨h, c, hc, he⟩ r`. Distinguish the cases in `hr : r = i0`. Substitute `hr; exact ⟨⟨c, hc⟩, by rw [he, Formalism.MainNotions.Gaps.LevGap.vecAt_same]⟩` using the available equality. Conclude with `⟨⟨y r, h r⟩, by rw [Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]⟩`.
-/
theorem mem_latS_lb {n : ℕ} (i0 : Fin n) (hi0 : i0.1 + 1 = n) (t : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ r : Fin n, ∃ s : 𝓞 E, x r = (s : E) ∧ (r.1 + 1 = n → t ∣ s))
    (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb ↔
      (∀ r, y r ∈ intV E v) ∧ ∃ c ∈ intV E v, y i0 = inclE (F := F) (v.adicCompletion F) (t : E) * c := by
  rw [lb_eq_latT i0 hi0 t Lb hLb]
  show y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.MainNotions.Gaps.LevGap.diagLat (Formalism.MainNotions.Gaps.LevGap.vecAt i0 (t : E))) ↔ _
  rw [Formalism.MainNotions.Gaps.LG.fm_mem_latS]
  constructor
  · intro h
    refine ⟨fun r => ?_, ?_⟩
    · obtain ⟨c, hc⟩ := h r
      rw [hc]
      by_cases hr : r = i0
      · subst hr; rw [Formalism.MainNotions.Gaps.LevGap.vecAt_same]; exact (intV E v).mul_mem (Formalism.MainNotions.Gaps.LG.fm_incl_mem v t) c.2
      · rw [Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]; exact c.2
    · obtain ⟨c, hc⟩ := h i0
      exact ⟨c, c.2, by rw [hc, Formalism.MainNotions.Gaps.LevGap.vecAt_same]⟩
  · rintro ⟨h, c, hc, he⟩ r
    by_cases hr : r = i0
    · subst hr; exact ⟨⟨c, hc⟩, by rw [he, Formalism.MainNotions.Gaps.LevGap.vecAt_same]⟩
    · exact ⟨⟨y r, h r⟩, by rw [Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]⟩

/- English proof (translation)
Establish `hs0 : σ (t : E) ≠ 0` using `(map_ne_zero _).2 ht`. Establish `hinv : inclE (F` using `F) (v.adicCompletion F) (σ (t : E)) * inclE (F := F) (v.adicCompletion F) (σ (t : E))⁻¹ = 1 := by`. Rewrite using `[← map_mul, mul_inv_cancel₀ hs0, map_one]`. Rewrite using `[hJ, lb_eq_latT i0 hi0 t Lb hLb, Formalism.MainNotions.Gaps.LevGap.span_dualSet_latT (σ : E →+* E) ht, Formalism.MainNotions.Gaps.LG.fm_mem_latS]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun r hr => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h r`. Rewrite using `[hc, Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]`. Conclude with `c.2`.

Take `⟨c, hc⟩` from `h i0`. Rewrite using `[hc, Formalism.MainNotions.Gaps.LevGap.vecAt_same]`. Use `show inclE (F := F) (v.adicCompletion F) (σ (t : E)) * (inclE (F := F) (v.adicCompletion F) ((σ : E →+* E) (t : E))⁻¹ * _) ∈ _`. Rewrite using `[← mul_assoc]`. Use `erw [hinv]`.

Rewrite using `[one_mul]`. Conclude with `c.2`. Introduce and unpack `⟨h, h0⟩ r`. Distinguish the cases in `hr : r = i0`. Substitute `hr` using the available equality.

Use `⟨⟨_, h0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.MainNotions.Gaps.LevGap.vecAt_same]`. Use `show _ = inclE (F := F) (v.adicCompletion F) ((σ (t : E))⁻¹) * (inclE (F := F) (v.adicCompletion F) (σ (t : E)) * y r)`. Rewrite using `[← mul_assoc, mul_comm (inclE (F := F) (v.adicCompletion F) (σ (t : E))⁻¹), hinv, one_mul]`. Conclude with `⟨⟨y r, h r hr⟩, by rw [Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]⟩`.
-/
theorem mem_latS_ld {n : ℕ} (i0 : Fin n) (hi0 : i0.1 + 1 = n) (t : 𝓞 E) (ht : (t : E) ≠ 0) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ r : Fin n, ∃ s : 𝓞 E, x r = (s : E) ∧ (r.1 + 1 = n → t ∣ s))
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) ↔
      (∀ r, r ≠ i0 → y r ∈ intV E v) ∧ inclE (F := F) (v.adicCompletion F) (σ (t : E)) * y i0 ∈ intV E v := by
  have hs0 : σ (t : E) ≠ 0 := (map_ne_zero _).2 ht
  have hinv : inclE (F := F) (v.adicCompletion F) (σ (t : E)) * inclE (F := F) (v.adicCompletion F) (σ (t : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
  rw [hJ, lb_eq_latT i0 hi0 t Lb hLb, Formalism.MainNotions.Gaps.LevGap.span_dualSet_latT (σ : E →+* E) ht, Formalism.MainNotions.Gaps.LG.fm_mem_latS]
  constructor
  · intro h
    refine ⟨fun r hr => ?_, ?_⟩
    · obtain ⟨c, hc⟩ := h r
      rw [hc, Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]; exact c.2
    · obtain ⟨c, hc⟩ := h i0
      rw [hc, Formalism.MainNotions.Gaps.LevGap.vecAt_same]
      show inclE (F := F) (v.adicCompletion F) (σ (t : E)) * (inclE (F := F) (v.adicCompletion F) ((σ : E →+* E) (t : E))⁻¹ * _) ∈ _
      rw [← mul_assoc]
      erw [hinv]; rw [one_mul]; exact c.2
  · rintro ⟨h, h0⟩ r
    by_cases hr : r = i0
    · subst hr
      refine ⟨⟨_, h0⟩, ?_⟩
      rw [Formalism.MainNotions.Gaps.LevGap.vecAt_same]
      show _ = inclE (F := F) (v.adicCompletion F) ((σ (t : E))⁻¹) * (inclE (F := F) (v.adicCompletion F) (σ (t : E)) * y r)
      rw [← mul_assoc, mul_comm (inclE (F := F) (v.adicCompletion F) (σ (t : E))⁻¹), hinv, one_mul]
    · exact ⟨⟨y r, h r hr⟩, by rw [Formalism.MainNotions.Gaps.LevGap.vecAt_ne hr, map_one, one_mul]⟩

/- English proof (translation)
Use `⟨inclE (F := F) (v.adicCompletion F) (ca : E), Formalism.MainNotions.Gaps.LG.fm_incl_mem v ca, inclE (F := F) (v.adicCompletion F) (cb : E), Formalism.MainNotions.Gaps.LG.fm_incl_mem v cb, ?_⟩` and prove the remaining obligations. Establish `e : (t : E) * ca + (t' : E) * cb = 1`. Use `congrArg ((↑) : 𝓞 E → E) h` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.

Establish `e2` using `congrArg (inclE (F := F) (E := E) (v.adicCompletion F)) e`. Rewrite `e2` using `[RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_one]`. Rewrite using `[← ht']`. Conclude with `e2`.
-/
theorem cop_local (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (t t' ca cb : 𝓞 E) (ht' : (t' : E) = σ (t : E))
    (h : ca * t + cb * t' = 1) : ∃ c ∈ intV E v, ∃ d ∈ intV E v,
      inclE (F := F) (v.adicCompletion F) (t : E) * c + inclE (F := F) (v.adicCompletion F) (σ (t : E)) * d = 1 := by
  refine ⟨inclE (F := F) (v.adicCompletion F) (ca : E), Formalism.MainNotions.Gaps.LG.fm_incl_mem v ca,
    inclE (F := F) (v.adicCompletion F) (cb : E), Formalism.MainNotions.Gaps.LG.fm_incl_mem v cb, ?_⟩
  have e : (t : E) * ca + (t' : E) * cb = 1 := by
    have := congrArg ((↑) : 𝓞 E → E) h
    push_cast at this
    linear_combination this
  have e2 := congrArg (inclE (F := F) (E := E) (v.adicCompletion F)) e
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_one] at e2
  rw [← ht']
  exact e2

/- English proof (translation)
Establish `hle : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F))` using `by show tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤ _`. Unfold `tensInt`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨s, c, rfl⟩, rfl⟩ | ⟨⟨s, hs⟩, rfl⟩)`. Use `show sigR σ (v.adicCompletion F) (((algebraMap (𝓞 E) E) c) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ intV E v`.

Establish `e : sigR σ (v.adicCompletion F) (((algebraMap (𝓞 E) E) c) ⊗ₜ[F] (1 : v.adicCompletion F)) = inclE (F` using `F) (v.adicCompletion F) ((RingOfIntegers.mapRingHom (σ : E →+* E) c : 𝓞 E) : E) := rfl`. Rewrite using `[e]`. Conclude with `Formalism.MainNotions.Gaps.LG.fm_incl_mem v _`. Use `show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] s) ∈ intV E v`. Establish `e : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] s) = (1 : E) ⊗ₜ[F] s` using `by show (Algebra.TensorProduct.map σ (AlgHom.id F (v.adicCompletion F))) ((1 : E) ⊗ₜ[F] s) = _`.

Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Formalism.MainNotions.Gaps.LG.fm_one_tmul_mem v ⟨s, hs⟩`. Conclude with `hle hx`.
-/
theorem sigR_mem_intV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) :
    sigR σ (v.adicCompletion F) x ∈ intV E v := by
  have hle : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    show tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤ _
    unfold tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, c, rfl⟩, rfl⟩ | ⟨⟨s, hs⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (((algebraMap (𝓞 E) E) c) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ intV E v
      have e : sigR σ (v.adicCompletion F) (((algebraMap (𝓞 E) E) c) ⊗ₜ[F] (1 : v.adicCompletion F)) =
          inclE (F := F) (v.adicCompletion F) ((RingOfIntegers.mapRingHom (σ : E →+* E) c : 𝓞 E) : E) := rfl
      rw [e]; exact Formalism.MainNotions.Gaps.LG.fm_incl_mem v _
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] s) ∈ intV E v
      have e : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] s) = (1 : E) ⊗ₜ[F] s := by
        show (Algebra.TensorProduct.map σ (AlgHom.id F (v.adicCompletion F))) ((1 : E) ⊗ₜ[F] s) = _
        rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
      rw [e]; exact Formalism.MainNotions.Gaps.LG.fm_one_tmul_mem v ⟨s, hs⟩
  exact hle hx

end Lat

end GlobalTheory.StabFnLev

namespace GlobalTheory.StabFnLev

/- English proof (translation)
Substitute `hm` using the available equality. Simplify using `only [finCongr_refl, Matrix.reindex_refl_refl]`. Establish `hb' : ∀ u : Fin m' → k, b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u)`. Introduce `u`. Express the relevant statement in the definitionally equal form `_ = g.val *ᵥ (b' *ᵥ u)`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]`. Establish `hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k]`. Introduce `u`. Rewrite using `[hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]`. Establish `hu : ∀ j, (Pi.single s 1 : Fin m' → k) j ∈ 𝒪[k]` using `fun j => by`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Take `⟨s1, hs1, hv1⟩` from `hval _ hu r hr`. Establish `h1` using `hv1.gl_smul g`.

Rewrite `h1` using `[hg, ← hb']`. Take `⟨s2, hs2, hv2⟩` from `hval _ ((hlat _).1 h1.mem) r hr`. Use `(GlobalTheory.PairKeep.res_zero_iff c τ q hτ hc _ (s2 - s1) ?_).1 (by rw [map_sub, hv2.unique h1, sub_self])` and prove the remaining obligations. Rewrite using `[AddSubgroupClass.coe_sub, hs1, hs2, mulVec_single_apply, mul_one, Matrix.one_apply, Pi.single_apply, mul_sub]`.
-/
theorem pair_lastRow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k) (hbb : b * b' = 1) (hb'b : b' * b = 1)
    (P : Pair k (Fin m')) (hP : ∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k])
    (c τ : k) (q : Unif k) (hτ : valuation k τ = valuation k ((q.1 : 𝒪[k]) : k)) (hc : valuation k c = 1)
    (hval : ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s))
    (g : GL (Fin m') k) (hg : g • P = P) (r s : Fin m) (hr : r.1 + 1 = m) :
    ∃ t ∈ 𝒪[k], (b * g.val * b').reindex (finCongr hm) (finCongr hm) r s - (1 : Matrix (Fin m) (Fin m) k) r s = τ * t := by
  subst hm
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hb' : ∀ u : Fin m' → k, b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u) := by
    intro u
    change _ = g.val *ᵥ (b' *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]
  have hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    rw [hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  have hu : ∀ j, (Pi.single s 1 : Fin m' → k) j ∈ 𝒪[k] := fun j => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨s1, hs1, hv1⟩ := hval _ hu r hr
  have h1 := hv1.gl_smul g
  rw [hg, ← hb'] at h1
  obtain ⟨s2, hs2, hv2⟩ := hval _ ((hlat _).1 h1.mem) r hr
  refine (GlobalTheory.PairKeep.res_zero_iff c τ q hτ hc _ (s2 - s1) ?_).1 (by rw [map_sub, hv2.unique h1, sub_self])
  rw [AddSubgroupClass.coe_sub, hs1, hs2, mulVec_single_apply, mul_one, Matrix.one_apply, Pi.single_apply, mul_sub]

/- English proof (translation)
Rewrite using `[lev.UlocAlt v h]`. Use `⟨hlev, ?_⟩` and prove the remaining obligations. Substitute `hJ` using the available equality. Take `⟨ca, cb, hab⟩` from `hcp`. Set `i0 : Fin m` to `⟨m - 1, by omega⟩`.

Establish `hi0 : i0.1 + 1 = m` using `by simp only [i0]; omega`. Establish `htE : (t : E) ≠ 0` using `fun h0 => ht (RingOfIntegers.ext h0)`. Establish `hπS : Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (t : E) ∈ intV E v := Formalism.MainNotions.Gaps.LG.fm_incl_mem v t`. Establish `hπu : IsUnit (Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (t : E)) := (isUnit_iff_ne_zero.2 htE).map _`. Take `⟨hUJ, hst⟩` from `Subgroup.mem_inf.1 hlev`.

Establish `hU1 : M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1`. Rewrite `hUJ` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Then use the resulting hypothesis. Establish `hU` using `Formalism.MainNotions.Gaps.CC.Idx.t_unit_inv _ M hU1`. Establish `hU' : ∀ r s, M.val r s = Formalism.UG.sigR σ (v.adicCompletion F) ((M⁻¹).val s r)`. Introduce `r s`.

Use `Formalism.MainNotions.Gaps.CC.Idx.t_unit_inv _ M⁻¹ (inv_mem hU1) r s` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hτ` using `sigR_mem_intV σ v`. Establish `hLbV` using `mem_latS_lb i0 hi0 t lev.Lb hLb v`. Establish `hLdV` using `mem_latS_ld i0 hi0 t htE lev.Lb hLb σ 1 rfl v`.

Establish `hint` using `alg_int _ (intV E v) _ i0 M hU' hτ hπS hπu (fun y hy hy0 => (hLbV _).1 ((hst y).1 ((hLbV y).2 ⟨hy, hy0⟩))) (fun y hy hy0 => (hLbV _).1 (((inv_mem hst : M⁻¹ ∈ _) y).1 ((hLbV y).2 ⟨hy, hy0⟩)))`. Establish `hrow : ∀ s, ∃ c ∈ intV E v, M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s = Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (t : E) * c := by`. Introduce `s`. Establish `hz : M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s ∈ intV E v` using `sub_mem (hint i0 s) (by`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Use `exacts [one_mem _, zero_mem _])`. Take `⟨c0, hc0, he0⟩` from `hrow0 i0 s hi0`. Establish `hφz : φ (M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s) = φ (Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (t : E)) * c0 := by`. Rewrite using `[← he0, ← hH, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]`.

Use `split_ifs`. Use `exacts [by rw [map_one], by rw [map_zero]]`. Take `⟨c, hc⟩` from `hπu.dvd (a := M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s)`. Use `⟨c, (hφ c).2 ⟨?_, ?_⟩, hc⟩` and prove the remaining obligations. Rewrite `hφz` using `[hc, map_mul]`.

Rewrite using `[(hπu.map φ).mul_left_cancel hφz]`. Conclude with `hc0`. Establish `h2` using `((hφ _).1 hz).2`. Rewrite `h2` using `[hc, map_mul, map_mul, Valuation.mem_integer_iff, map_mul, hq', one_mul]`. Conclude with `(Valuation.mem_integer_iff _ _).2 h2`.

Establish `hsub` using `alg_sub _ (intV E v) _ _ i0 M hU hU' hτ rfl hint (cop_local σ v t t' ca cb ht' hab) hrow`. Establish `h1 : ∀ y ∈ Formalism.UG.latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) 1 lev.Lb)), M.val *ᵥ y - y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) lev.Lb := by`. Introduce `y hy`. Take `⟨hy1, hy2⟩` from `(hLdV y).1 hy`. Conclude with `(hLbV _).2 (hsub y hy1 hy2)`.

Use `mem_stabFun_of_sub _ _ _ (lev.fT_L v h) (Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))) M h1 fun y hy => ?_` and prove the remaining obligations. Establish `hz` using `neg_mem (h1 y hy)`. Establish `e : (M⁻¹).val *ᵥ y - y = (M⁻¹).val *ᵥ (-(M.val *ᵥ y - y))`. Rewrite using `[neg_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[e]`.

Conclude with `((inv_mem hst : M⁻¹ ∈ _) _).1 hz`.
-/
theorem mem_Uloc_of_row (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k)
    (hφ : ∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k])
    (m : ℕ) (hm : 0 < m) (J : Matrix (Fin m) (Fin m) E) (hJ : J = 1) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (lev : Formalism.L2.Forms.StepLevel F E σ J T f bad) (t t' : 𝓞 E) (ht : t ≠ 0) (ht' : (t' : E) = σ (t : E)) (hcp : IsCoprime t t')
    (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (hq' : valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1)
    (M : GL (Fin m) (E ⊗[F] v.adicCompletion F)) (H : Matrix (Fin m) (Fin m) k) (hH : M.val.map φ = H)
    (hrow0 : ∀ r s : Fin m, r.1 + 1 = m → ∃ c ∈ 𝒪[k], H r s - (1 : Matrix (Fin m) (Fin m) k) r s =
      φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * c)
    (h : (T : 𝓞 F) ∈ v.asIdeal) (hlev : M ∈ Formalism.UG.levelVL σ J v lev.Lb) : M ∈ lev.Uloc v := by
  rw [lev.UlocAlt v h]
  refine ⟨hlev, ?_⟩
  subst hJ
  obtain ⟨ca, cb, hab⟩ := hcp
  let i0 : Fin m := ⟨m - 1, by omega⟩
  have hi0 : i0.1 + 1 = m := by simp only [i0]; omega
  have htE : (t : E) ≠ 0 := fun h0 => ht (RingOfIntegers.ext h0)
  have hπS : Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) ∈ intV E v := Formalism.MainNotions.Gaps.LG.fm_incl_mem v t
  have hπu : IsUnit (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) := (isUnit_iff_ne_zero.2 htE).map _
  obtain ⟨hUJ, hst⟩ := Subgroup.mem_inf.1 hlev
  have hU1 : M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 := by
    rwa [Matrix.map_one _ (map_zero _) (map_one _)] at hUJ
  have hU := Formalism.MainNotions.Gaps.CC.Idx.t_unit_inv _ M hU1
  have hU' : ∀ r s, M.val r s = Formalism.UG.sigR σ (v.adicCompletion F) ((M⁻¹).val s r) := by
    intro r s
    have := Formalism.MainNotions.Gaps.CC.Idx.t_unit_inv _ M⁻¹ (inv_mem hU1) r s
    rwa [inv_inv] at this
  have hτ := sigR_mem_intV σ v
  have hLbV := mem_latS_lb i0 hi0 t lev.Lb hLb v
  have hLdV := mem_latS_ld i0 hi0 t htE lev.Lb hLb σ 1 rfl v
  have hint := alg_int _ (intV E v) _ i0 M hU' hτ hπS hπu
    (fun y hy hy0 => (hLbV _).1 ((hst y).1 ((hLbV y).2 ⟨hy, hy0⟩)))
    (fun y hy hy0 => (hLbV _).1 (((inv_mem hst : M⁻¹ ∈ _) y).1 ((hLbV y).2 ⟨hy, hy0⟩)))
  have hrow : ∀ s, ∃ c ∈ intV E v, M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) * c := by
    intro s
    have hz : M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s ∈ intV E v :=
      sub_mem (hint i0 s) (by
        rw [Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _])
    obtain ⟨c0, hc0, he0⟩ := hrow0 i0 s hi0
    have hφz : φ (M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s) =
        φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * c0 := by
      rw [← he0, ← hH, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      exacts [by rw [map_one], by rw [map_zero]]
    obtain ⟨c, hc⟩ := hπu.dvd (a := M.val i0 s - (1 : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) i0 s)
    refine ⟨c, (hφ c).2 ⟨?_, ?_⟩, hc⟩
    · rw [hc, map_mul] at hφz
      rw [(hπu.map φ).mul_left_cancel hφz]
      exact hc0
    · have h2 := ((hφ _).1 hz).2
      rw [hc, map_mul, map_mul, Valuation.mem_integer_iff, map_mul, hq', one_mul] at h2
      exact (Valuation.mem_integer_iff _ _).2 h2
  have hsub := alg_sub _ (intV E v) _ _ i0 M hU hU' hτ rfl hint (cop_local σ v t t' ca cb ht' hab) hrow
  have h1 : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) 1 lev.Lb)),
      M.val *ᵥ y - y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) lev.Lb := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := (hLdV y).1 hy
    exact (hLbV _).2 (hsub y hy1 hy2)
  refine mem_stabFun_of_sub _ _ _ (lev.fT_L v h)
    (Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))) M h1 fun y hy => ?_
  have hz := neg_mem (h1 y hy)
  have e : (M⁻¹).val *ᵥ y - y = (M⁻¹).val *ᵥ (-(M.val *ᵥ y - y)) := by
    rw [neg_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact ((inv_mem hst : M⁻¹ ∈ _) _).1 hz

end GlobalTheory.StabFnLev

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `B X I hI hP l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg x hx hT hlev`. Take `⟨⟨e, he⟩, hS2⟩` from `hS`. Take `⟨hL, hS3⟩` from `hS2 j hj`. Take `⟨hLat, hVal⟩` from `hS3 i`. Take `⟨hX, hPr, -⟩` from `GlobalTheory.Mem.Col2.base_fields_primes_ok B X`.

Establish `hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u))` using `hPr.piT_cop u`. Establish `hne : X.piT u ≠ 0`. Introduce `h0`. Rewrite `hcop` using `[h0, map_zero, isCoprime_zero_left]`. Conclude with `not_isUnit_zero hcop`.

Establish `hmem : X.piT u ∈ (e i).1.asIdeal` using `(Formalism.L2.Col.mem_divs hne _).1 (e i).2`. Establish `hsq : X.piT u ∉ (e i).1.asIdeal ^ 2` using `hPr.piT_notMem_sq hX u (e i).2`. Establish `hconj : B.fields.conjO (X.piT u) ∉ (e i).1.asIdeal` using `fun h => by`. Take `⟨s, t, hst⟩` from `hcop`. Establish `: (1 : 𝓞 B.fields.E) ∈ (e i).1.asIdeal`.

Rewrite using `[← hst]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h)`. Conclude with `(e i).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)`. Take `⟨φ, hφ1, hφ2, hφ3, hφ4⟩` from `GlobalTheory.T.exists_splitPlace_component_ringHom_integral _ k (p i) (e i).1 (he i)`. Take `⟨⟨q, hq⟩, hc⟩` from `GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime _ k (p i) (e i).1 (he i) (X.piT u) (B.fields.conjO (X.piT u)) hmem hsq hconj`.

Establish `hlat` using `GlobalTheory.T.mem_integralVectors_component_iff_integral_frame_coords _ k (p i) _ _ (β j i) (L j) hL _ hLat`. Establish `hv6` using `GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors _ k (p i) (e i).1 (he i) _ (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat (B.fields.conjO (X.piT u)) (fun z hz r hr => hVal z ((hL z).2 hz) r hr)`. Establish `hn` using `rankN (I.rec7 l Z) j hj`. Establish `hrow` using `GlobalTheory.StabFnLev.pair_lastRow k _ _ hn (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat _ (φ (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F) ((X.piT u : 𝓞 B.fields.E) : B.fields.E))) q ((congrArg (valuation k) (hφ2 _)).tr …`. Establish `hg1 : gramN (I.rec7 l Z) j hj = 1` using `((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1`.

Establish `hM : (Formalism.UG.bc (Formalism.UG.prV (E` using `(I.rec7 l Z).host.E) (p i).v) x.1).val.map φ = ((β j i).b * g.val * (β j i).b').reindex (finCongr hn) (finCongr hn) := by`. Rewrite using `[← (β j i).gl_mat g]`. Use extensionality with `r s`. Simplify using `only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]`. Express the relevant statement in the definitionally equal form `φ (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (x.1.1 r s)) = _`.

Rewrite using `[hx]`. Simplify using `only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]`. Rewrite using `[hφ1]`. Conclude with `GlobalTheory.StabFnLev.mem_Uloc_of_row _ _ (sigD (I.rec7 l Z)) (p i).v k φ hφ4 _ (B.R.N_pos j) _ hg1 _ _ _ (A.K j hj b).lev (X.piT u) (B.fields.conjO (X.piT u)) hne rfl hcop (fun y => (hA.reads j hj).lb b y) ((congrArg (valuation k) (hφ3 _)).trans hc) _ _ hM hrow hT hlev`.
-/
theorem GlobalTheory.StabFnLev.comp_mem_Uloc : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) b i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i →
    ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
    x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal,
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ Formalism.UG.levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v (A.K j hj b).lev.Lb →
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ (A.K j hj b).lev.Uloc (p i).v := by
  intro B X I hI hP l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg x hx hT hlev
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hL, hS3⟩ := hS2 j hj
  obtain ⟨hLat, hVal⟩ := hS3 i
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hsq : X.piT u ∉ (e i).1.asIdeal ^ 2 := hPr.piT_notMem_sq hX u (e i).2
  have hconj : B.fields.conjO (X.piT u) ∉ (e i).1.asIdeal := fun h => by
    obtain ⟨s, t, hst⟩ := hcop
    have : (1 : 𝓞 B.fields.E) ∈ (e i).1.asIdeal := by
      rw [← hst]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h)
    exact (e i).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨φ, hφ1, hφ2, hφ3, hφ4⟩ := GlobalTheory.T.exists_splitPlace_component_ringHom_integral _ k (p i) (e i).1 (he i)
  obtain ⟨⟨q, hq⟩, hc⟩ := GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime _ k (p i) (e i).1 (he i) (X.piT u) (B.fields.conjO (X.piT u)) hmem hsq hconj
  have hlat := GlobalTheory.T.mem_integralVectors_component_iff_integral_frame_coords _ k (p i) _ _ (β j i) (L j) hL _ hLat
  have hv6 := GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors _ k (p i) (e i).1 (he i) _ (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat
    (B.fields.conjO (X.piT u)) (fun z hz r hr => hVal z ((hL z).2 hz) r hr)
  have hn := rankN (I.rec7 l Z) j hj
  have hrow := GlobalTheory.StabFnLev.pair_lastRow k _ _ hn (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat _
    (φ (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F) ((X.piT u : 𝓞 B.fields.E) : B.fields.E)))
    q ((congrArg (valuation k) (hφ2 _)).trans hq) hc hv6 g hg
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
  have hM : (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1).val.map φ =
      ((β j i).b * g.val * (β j i).b').reindex (finCongr hn) (finCongr hn) := by
    rw [← (β j i).gl_mat g]
    ext r s
    simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    change φ (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (x.1.1 r s)) = _
    rw [hx]
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    rw [hφ1]
  exact GlobalTheory.StabFnLev.mem_Uloc_of_row _ _ (sigD (I.rec7 l Z)) (p i).v k φ hφ4 _ (B.R.N_pos j) _ hg1 _ _ _ (A.K j hj b).lev
    (X.piT u) (B.fields.conjO (X.piT u)) hne rfl hcop (fun y => (hA.reads j hj).lb b y)
    ((congrArg (valuation k) (hφ3 _)).trans hc) _ _ hM hrow hT hlev
