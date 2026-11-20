import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

namespace Rig

/- English proof (translation)
Establish `h` using `congrFun (congrFun hc i) j`. Simplify using `only [Matrix.mul_apply] at h`. Rewrite `h` using `[Finset.sum_eq_single i (fun k _ hk => by rw [hD i k (Ne.symm hk), zero_mul]) (by simp), Finset.sum_eq_single j (fun k _ hk => by rw [hD' k j hk, mul_zero]) (by simp)]`. Then use the resulting hypothesis.
-/
theorem diag_comm_entry {L : Type*} [CommRing L] {n : ℕ} (D D' H : Matrix (Fin n) (Fin n) L)
    (hD : ∀ i j, i ≠ j → D i j = 0) (hD' : ∀ i j, i ≠ j → D' i j = 0) (hc : D * H = H * D') (i j : Fin n) :
    D i i * H i j = H i j * D' j j := by
  have h := congrFun (congrFun hc i) j
  simp only [Matrix.mul_apply] at h
  rwa [Finset.sum_eq_single i (fun k _ hk => by rw [hD i k (Ne.symm hk), zero_mul]) (by simp),
    Finset.sum_eq_single j (fun k _ hk => by rw [hD' k j hk, mul_zero]) (by simp)] at h

/- English proof (translation)
Establish `key : ∀ i j, H i j ≠ 0 → e i = e' j`. Introduce `i j hij`. Establish `h1` using `congrFun (congrFun hc i) j`. Rewrite `h1` using `[diagonal_mul, mul_diagonal]`. Conclude with `mul_right_cancel₀ hij (by rw [h1, mul_comm])`.

Establish `row : ∀ i, ∃ j, H i j ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `hne`. Conclude with `hH (Matrix.det_eq_zero_of_row_eq_zero i fun j => by_contra fun h => hne ⟨j, h⟩)`. Use `choose f hf using row`.

Establish `hfe : ∀ i, e i = e' (f i)` using `fun i => key i (f i) (hf i)`. Establish `hmono : StrictMono f`. Introduce `i j hij`. Establish `h1 : (ν ∘ e) j < (ν ∘ e) i` using `he hij`. Simplify using `only [Function.comp_apply, hfe] at h1`.

Conclude with `lt_of_not_ge fun hge => absurd h1 (not_lt.mpr (he'.antitone hge))`. Establish `hid : ∀ i, f i = i` using `fun i => le_antisymm hmono.apply_le hmono.le_apply`. Establish `hee : e = e'` using `funext fun i => by rw [hfe i, hid i]`. Use `⟨hee, fun i j hij => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h2` using `key i j hne`. Rewrite `h2` using `[hee]`. Conclude with `hij (he'.injective (by simp only [Function.comp_apply, h2]))`.
-/
theorem rig_mat {L : Type*} [Field L] {n : ℕ} (ν : L → ℤ) (e e' : Fin n → L) (H : Matrix (Fin n) (Fin n) L)
    (hH : H.det ≠ 0) (hc : diagonal e * H = H * diagonal e')
    (he : StrictAnti (ν ∘ e)) (he' : StrictAnti (ν ∘ e')) :
    e = e' ∧ ∀ i j, i ≠ j → H i j = 0 := by
  have key : ∀ i j, H i j ≠ 0 → e i = e' j := by
    intro i j hij
    have h1 := congrFun (congrFun hc i) j
    rw [diagonal_mul, mul_diagonal] at h1
    exact mul_right_cancel₀ hij (by rw [h1, mul_comm])
  have row : ∀ i, ∃ j, H i j ≠ 0 := by
    intro i
    by_contra hne
    exact hH (Matrix.det_eq_zero_of_row_eq_zero i fun j => by_contra fun h => hne ⟨j, h⟩)
  choose f hf using row
  have hfe : ∀ i, e i = e' (f i) := fun i => key i (f i) (hf i)
  have hmono : StrictMono f := by
    intro i j hij
    have h1 : (ν ∘ e) j < (ν ∘ e) i := he hij
    simp only [Function.comp_apply, hfe] at h1
    exact lt_of_not_ge fun hge => absurd h1 (not_lt.mpr (he'.antitone hge))
  have hid : ∀ i, f i = i := fun i => le_antisymm hmono.apply_le hmono.le_apply
  have hee : e = e' := funext fun i => by rw [hfe i, hid i]
  refine ⟨hee, fun i j hij => ?_⟩
  by_contra hne
  have h2 := key i j hne
  rw [hee] at h2
  exact hij (he'.injective (by simp only [Function.comp_apply, h2]))

/- English proof (translation)
Establish `hc' : d * h = h * d'` using `by rw [← hc]; group`. Establish `hm : diagonal e * h.val = h.val * diagonal e'`. Rewrite using `[← hd, ← hd', ← Units.val_mul, ← Units.val_mul, hc']`. Establish `hdet : h.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero`. Take `⟨hee, hoff⟩` from `rig_mat ν e e' h.val hdet hm he he'`.

Conclude with `⟨Units.ext (by rw [hd, hd', hee]), hoff⟩`.
-/
theorem rig_GL {L : Type*} [Field L] {n : ℕ} (ν : L → ℤ) (e e' : Fin n → L) (d d' h : GL (Fin n) L)
    (hd : d.val = diagonal e) (hd' : d'.val = diagonal e') (hc : h⁻¹ * d * h = d')
    (he : StrictAnti (ν ∘ e)) (he' : StrictAnti (ν ∘ e')) :
    d = d' ∧ ∀ i j, i ≠ j → h.val i j = 0 := by
  have hc' : d * h = h * d' := by rw [← hc]; group
  have hm : diagonal e * h.val = h.val * diagonal e' := by
    rw [← hd, ← hd', ← Units.val_mul, ← Units.val_mul, hc']
  have hdet : h.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  obtain ⟨hee, hoff⟩ := rig_mat ν e e' h.val hdet hm he he'
  exact ⟨Units.ext (by rw [hd, hd', hee]), hoff⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

/- English proof (translation)
Take `⟨hdd, hoff⟩` from `rig_GL (fun y : w.adicCompletion E => ordL y) (fun i => (e i : w.adicCompletion E)) (fun i => (e' i : w.adicCompletion E)) _ _ h (GlobalTheory.SmGL.val_diagT _ e) (GlobalTheory.SmGL.val_diagT _ e') hc he he'`. Use `⟨funext fun i => Units.ext ?_, hoff⟩` and prove the remaining obligations. Use `congrArg (fun g : GLw n w => g.val i i) hdd` as an intermediate fact. Simplify `this` using `[GlobalTheory.SmGL.val_diagT]`.
-/
theorem rig_diagT (w : Pl E) {n : ℕ} (e e' : Fin n → (w.adicCompletion E)ˣ) (h : GLw n w)
    (he : StrictAnti fun i => ordL (e i : w.adicCompletion E))
    (he' : StrictAnti fun i => ordL (e' i : w.adicCompletion E))
    (hc : h⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) e * h = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) e') :
    e = e' ∧ ∀ i j, i ≠ j → h.val i j = 0 := by
  obtain ⟨hdd, hoff⟩ := rig_GL (fun y : w.adicCompletion E => ordL y) (fun i => (e i : w.adicCompletion E))
    (fun i => (e' i : w.adicCompletion E)) _ _ h (GlobalTheory.SmGL.val_diagT _ e) (GlobalTheory.SmGL.val_diagT _ e') hc he he'
  refine ⟨funext fun i => Units.ext ?_, hoff⟩
  have := congrArg (fun g : GLw n w => g.val i i) hdd
  simpa [GlobalTheory.SmGL.val_diagT] using this

end Rig

open Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

/- English proof (translation)
Take `⟨hd0, hdv⟩` from `hd`. Take `⟨hd'0, hd'v⟩` from `hd'`. Establish `hc : d.val * h.val = h.val * d'.val`. Establish `hm : d * h = h * d'` using `by rw [← hh]; group`. Simplify using `using congrArg Units.val hm`.

Apply the tactic sequence `have he := diag_comm_entry d.val d'.val h.val hd0 hd'0 hc`. Establish `hoff : ∀ i j : Fin n, i ≠ j → h.val i j = 0`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Establish `hq : d.val i i = d'.val j j` using `mul_right_cancel₀ hne (by rw [he i j]; ring)`.

Apply `hij` to reduce the goal to its premises. Apply `hv` to reduce the goal to its premises. Rewrite using `[← hdv i, ← hd'v j, hq]`. Establish `hdiag : ∀ i, h.val i i ≠ 0`. Introduce `i h0`.

Establish `h1 : (h.val * h⁻¹.val) i i = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_zero]`. Conclude with `zero_ne_one h1`.

Introduce `k _`. Distinguish the cases in `hk : i = k`. Substitute `hk` using the available equality. Rewrite using `[h0, zero_mul]`. Rewrite using `[hoff i k hk, zero_mul]`.

Establish `hval : d.val = d'.val`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hq : d.val i i * h.val i i = d'.val i i * h.val i i` using `by rw [he i i]; ring`.

Conclude with `mul_right_cancel₀ (hdiag i) hq`. Rewrite using `[hd0 i j hij, hd'0 i j hij]`. Conclude with `⟨Units.ext hval, hoff⟩`.
-/
theorem diagonal_conj_distinct_valuations_eq (w : Pl E) (n : ℕ) (v : Fin n → ℤ) (hv : Function.Injective v) (d d' h : GLw n w)
    (hd : (∀ i j : Fin n, i ≠ j → d.val i j = 0) ∧ ∀ i, ordL (d.val i i) = v i)
    (hd' : (∀ i j : Fin n, i ≠ j → d'.val i j = 0) ∧ ∀ i, ordL (d'.val i i) = v i)
    (hh : h⁻¹ * d * h = d') : d = d' ∧ ∀ i j : Fin n, i ≠ j → h.val i j = 0 := by
  obtain ⟨hd0, hdv⟩ := hd
  obtain ⟨hd'0, hd'v⟩ := hd'
  have hc : d.val * h.val = h.val * d'.val := by
    have hm : d * h = h * d' := by rw [← hh]; group
    simpa using congrArg Units.val hm
  have he := diag_comm_entry d.val d'.val h.val hd0 hd'0 hc
  have hoff : ∀ i j : Fin n, i ≠ j → h.val i j = 0 := by
    intro i j hij
    by_contra hne
    have hq : d.val i i = d'.val j j := mul_right_cancel₀ hne (by rw [he i j]; ring)
    apply hij
    apply hv
    rw [← hdv i, ← hd'v j, hq]
  have hdiag : ∀ i, h.val i i ≠ 0 := by
    intro i h0
    have h1 : (h.val * h⁻¹.val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [hoff i k hk, zero_mul]
  have hval : d.val = d'.val := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      have hq : d.val i i * h.val i i = d'.val i i * h.val i i := by rw [he i i]; ring
      exact mul_right_cancel₀ (hdiag i) hq
    · rw [hd0 i j hij, hd'0 i j hij]
  exact ⟨Units.ext hval, hoff⟩

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
