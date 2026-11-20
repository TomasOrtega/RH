import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨x, hx, fun _ _ => by simp⟩`. Consider the case `insert s0 T hs0 ih`. Take `⟨y, hy, hyv⟩` from `ih`. Use `⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_insert hs0]`. Simplify using `only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[smul_C, hyv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

/- English proof (translation)
Take `⟨y, hy, hyv⟩` from `exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)`. Use `hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s' i`. Rewrite using `[hyv]`. Distinguish the cases in `e : s' = τ`.

Substitute `e` using the available equality. Simplify using `only [Pi.single_eq_same, smul_vec_apply, diffGen]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]`.

Simplify using `[e]`.
-/
theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

/- English proof (translation)
Rewrite using `[diffGen, Finset.prod_ne_zero_iff]`. Introduce `s hs e`. Conclude with `(Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm`.
-/
theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `v ⟨hH, hK⟩`. Establish `hH' : (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r`. Simplify `hH` using `[eigenSub]`. Establish `hK' : v ∈ filSpace Fil τ`.

Simplify `hK` using `[quotMap, Submodule.Quotient.mk_eq_zero]`. Establish `hle : filSpace Fil τ ≤ clearDen Fil τ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨diffGen a τ, diffGen_ne_zero a ha τ, single_mem_of_mem a Fil hF.stable τ x hx⟩`.

Take `⟨b, hb, hbv⟩` from `hle hK'`. Use `show (Pi.single τ v : S → Fin r → C) ∈ Fil`. Use `hF.saturated _ hH' b hb ?_` and prove the remaining obligations. Use `hbv using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s i`.

Distinguish the cases in `e : s = τ`. Substitute `e` using the available equality. Simplify using `[smul_pi_apply, smul_vec_apply, smul_C]`. Simplify using `[smul_pi_apply, e]`. Introduce `v hv`.

Establish `hv' : (Pi.single τ v : S → Fin r → C) ∈ Fil` using `by simpa [eigenSub] using hv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r`. Conclude with `hF.le hv'`. Use `show quotMap (w := w) (filSpace Fil τ) v = 0`.

Simplify using `only [quotMap, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `Submodule.subset_span ⟨_, hv', ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem ker_eq (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (τ : S) (ha : Function.Injective a) (hF : IsFiltration a Fil) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ⊓
        LinearMap.ker (quotMap (w := w) (filSpace Fil τ)) =
      eigenSub (W := fun _ => Fin r → C) Fil τ := by
  apply le_antisymm
  · rintro v ⟨hH, hK⟩
    have hH' : (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r := by
      simpa [eigenSub] using hH
    have hK' : v ∈ filSpace Fil τ := by
      simpa [quotMap, Submodule.Quotient.mk_eq_zero] using hK
    have hle : filSpace Fil τ ≤ clearDen Fil τ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨diffGen a τ, diffGen_ne_zero a ha τ, single_mem_of_mem a Fil hF.stable τ x hx⟩
    obtain ⟨b, hb, hbv⟩ := hle hK'
    show (Pi.single τ v : S → Fin r → C) ∈ Fil
    refine hF.saturated _ hH' b hb ?_
    convert hbv using 1
    funext s i
    by_cases e : s = τ
    · subst e; simp [smul_pi_apply, smul_vec_apply, smul_C]
    · simp [smul_pi_apply, e]
  · intro v hv
    have hv' : (Pi.single τ v : S → Fin r → C) ∈ Fil := by simpa [eigenSub] using hv
    refine ⟨?_, ?_⟩
    · show (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r
      exact hF.le hv'
    · show quotMap (w := w) (filSpace Fil τ) v = 0
      simp only [quotMap, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      refine Submodule.subset_span ⟨_, hv', ?_⟩
      simp

end GlobalTheory.Div.KerFil

/- English proof (translation)
Introduce `C _ w S _ _ a r Fil τ ha hF` and use `GlobalTheory.Div.KerFil.ker_eq C w S a r Fil τ ha hF`.
-/
theorem GlobalTheory.Div.kerFil : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ ⊓ LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ)) = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) Fil τ :=
  fun C _ w S _ _ a r Fil τ ha hF => GlobalTheory.Div.KerFil.ker_eq C w S a r Fil τ ha hF
