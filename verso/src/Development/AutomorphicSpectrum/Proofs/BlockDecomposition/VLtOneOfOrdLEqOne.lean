import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.IwahoriContraction

open PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1]`. Use `show _ ↔ g ∈ PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.adicCompletion E) ∧ _`. Rewrite using `[GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff, and_assoc]`. Simplify using `only [GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff, GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff]`.
-/
theorem mem_iwGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ iwGL n w ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E) := by
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1]
  show _ ↔ g ∈ PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.adicCompletion E) ∧ _
  rw [GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff, and_assoc]
  simp only [GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff, GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff]

omit [IsCMField E] in

/- English proof (translation)
Establish `h0' : Valued.v ϖ ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Take `⟨u, hu⟩` from `WithZero.ne_zero_iff_exists.1 h0'`. Establish `hu1 : Multiplicative.toAdd u = -1`. Use `GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `hx0 : Valued.v x = 0`. Rewrite using `[hx0]`. Conclude with `zero_le`. Take `⟨c, hc⟩` from `WithZero.ne_zero_iff_exists.1 hx0`. Rewrite using `[← hu, ← hc]`.

Rewrite `hx` using `[← hc]`. Establish `hc1 : c < 1` using `by exact_mod_cast hx`. Establish `hc2 : Multiplicative.toAdd c < 0` using `hc1`. Establish `: c ≤ u` using `by show Multiplicative.toAdd c ≤ Multiplicative.toAdd u`. Use linear arithmetic over natural numbers and integers.

Conclude with `this` after adjusting the coercions.
-/
theorem v_le_of_ordL_eq_one (w : Pl E) {ϖ x : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1)
    (hx : Valued.v x < 1) : Valued.v x ≤ Valued.v ϖ := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  by_cases hx0 : Valued.v x = 0
  · rw [hx0]
    exact zero_le
  obtain ⟨c, hc⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [← hu, ← hc]
  rw [← hc] at hx
  have hc1 : c < 1 := by exact_mod_cast hx
  have hc2 : Multiplicative.toAdd c < 0 := hc1
  have : c ≤ u := by
    show Multiplicative.toAdd c ≤ Multiplicative.toAdd u
    omega
  exact_mod_cast this

omit [IsCMField E] in

/- English proof (translation)
Establish `h0' : Valued.v ϖ ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Take `⟨u, hu⟩` from `WithZero.ne_zero_iff_exists.1 h0'`. Establish `hu1 : Multiplicative.toAdd u = -1`. Use `GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← hu]`. Establish `: u < 1` using `by show Multiplicative.toAdd u < 0`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.
-/
theorem v_lt_one_of_ordL_eq_one (w : Pl E) {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1) :
    Valued.v ϖ < 1 := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  rw [← hu]
  have : u < 1 := by
    show Multiplicative.toAdd u < 0
    omega
  exact_mod_cast this

omit [IsCMField E] in

/- English proof (translation)
Take `⟨hu, hd⟩` from `ht`. Take `⟨h1, h2⟩` from `(GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff t).1 hu`. Use `⟨hd, fun i => ?_⟩` and prove the remaining obligations. Establish `hmul : ((t⁻¹ : GLw n w).val * t.val) i i = 1`. Establish `: (t⁻¹ : GLw n w).val * t.val = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite using `[this, Matrix.one_apply_eq]`. Rewrite `hmul` using `[Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [hd j i hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]`. Establish `ha` using `(GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h1 i i)`. Establish `hb` using `(GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h2 i i)`.

Establish `hv : Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) = 1`. Rewrite using `[← map_mul, hmul, map_one]`. Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem torusO_subset_TO (w : Pl E) (n : ℕ) (t : GLw n w)
    (ht : t ∈ PositivityTheory.Rg.Tf.Loc.torusO (n := n) (w.adicCompletion E)) : t ∈ TO n w := by
  obtain ⟨hu, hd⟩ := ht
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff t).1 hu
  refine ⟨hd, fun i => ?_⟩
  have hmul : ((t⁻¹ : GLw n w).val * t.val) i i = 1 := by
    have : (t⁻¹ : GLw n w).val * t.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [hd j i hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at hmul
  have ha := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h1 i i)
  have hb := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h2 i i)
  have hv : Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) := hv.symm
    _ ≤ 1 * Valued.v (t.val i i) := mul_le_mul' hb le_rfl
    _ = _ := one_mul _

/- English proof (translation)
Introduce `E _ _ _ w ϖ hϖ n y hy δ hδ`. Establish `hδ' : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ y * z`. Assume the negation of the conclusion as `h`. Conclude with `hδ (if_neg h)`. Take `⟨a, ha, b, hb, hab⟩` from `hδ'`.

Take `⟨⟨U, hU⟩, -, hcpt, -⟩` from `GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n`. Establish `hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Establish `hequiv` using `ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v`. Establish `hϖ0 : (ϖ : w.adicCompletion E) ≠ 0` using `ϖ.ne_zero`. Establish `hmap : ∀ g : GL (Fin n) (w.adicCompletion E), Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g`.

Introduce `g`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hρ1 : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1` using `(GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w hϖ0 hϖ.1)`.

Establish `hunif : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 → ValuativeRel.valuation (w.adicCompletion E) x ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E)` using `fun x hx => (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w hϖ0 hϖ.1 ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))`. Set `e : Fin n → w.adicCompletion E` to `fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)`. Establish `he : ∀ i, e i ≠ 0` using `fun i => Units.ne_zero _`. Establish `hc : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) * ValuativeRel.valuation (w.adicCompletion E) (e l)` using `fun i l h => by`. Take `⟨c, hcn⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)`.

Establish `hyi : y i = y l + ((c + 1 : ℕ) : ℤ)` using `by push_cast; omega`. Establish `hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1)` using `by show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _`. Rewrite using `[hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]`. Rewrite using `[hei, map_mul, map_pow, mul_comm]`. Use `mul_le_mul' ?_ le_rfl` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e`. Rewrite using `[tdiag, GlobalTheory.SmGL.val_diagT]`. Establish `hδI : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w)` using `⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩`. Take `⟨m, hm, t, ht, h⟩` from `GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _) (fun _ => rfl) (fun g hg => by rw [hmap]; exact hg) _ hρ1 hunif e he hc _ hx δ hδI`.

Rewrite `h` using `[hmap]`. Conclude with `⟨m, (mem_iwGL_iff w n m).2 hm, t, torusO_subset_TO w n t ht, h⟩`.
-/
theorem contr_id : PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw.P_contr_id := by
  intro E _ _ _ w ϖ hϖ n y hy δ hδ
  have hδ' : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ y * z := by
    by_contra h
    exact hδ (if_neg h)
  obtain ⟨a, ha, b, hb, hab⟩ := hδ'
  obtain ⟨⟨U, hU⟩, -, hcpt, -⟩ := GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n
  have hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hmap : ∀ g : GL (Fin n) (w.adicCompletion E),
      Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hρ1 : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w hϖ0 hϖ.1)
  have hunif : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 →
      ValuativeRel.valuation (w.adicCompletion E) x ≤
        ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := fun x hx =>
    (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w hϖ0 hϖ.1 ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have he : ∀ i, e i ≠ 0 := fun i => Units.ne_zero _
  have hc : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) *
        ValuativeRel.valuation (w.adicCompletion E) (e l) := fun i l h => by
    obtain ⟨c, hcn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((c + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (c + 1)
        ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hρ1.le (Nat.succ_le_succ (Nat.zero_le c))
      _ = _ := pow_one _
  have hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e := by
    rw [tdiag, GlobalTheory.SmGL.val_diagT]
  have hδI : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w) :=
    ⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩
  obtain ⟨m, hm, t, ht, h⟩ := GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _)
    (fun _ => rfl) (fun g hg => by rw [hmap]; exact hg) _ hρ1 hunif e he hc _ hx δ hδI
  rw [hmap] at h
  exact ⟨m, (mem_iwGL_iff w n m).2 hm, t, torusO_subset_TO w n t ht, h⟩

end GlobalTheory.CompanionTheory.IwahoriContraction
