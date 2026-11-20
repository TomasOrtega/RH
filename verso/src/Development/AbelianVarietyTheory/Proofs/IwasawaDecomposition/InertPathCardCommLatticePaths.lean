import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Nat.card_eq_finsetCard]`. Use `Nat.card_congr { toFun := fun e => ⟨e.1.1.N, e.1.2.lat, e.1.2.uni, ?_, ?_⟩ invFun := fun Y => ⟨⟨{ N := Y.1, f := d.1.f, be := d.1.be }, d.2.replN Y.2.1 Y.2.2.1 (fun R => hi_sameAt_inert (hST R) Y.2.2.2.1) (fun w => hi_sameAt_inert (hSG w) Y.2.2.2.1)⟩, ?_⟩ left_inv := ?_ right_inv …` and prove the remaining obligations. Establish `h` using `(Finset.mem_filter.1 e.2).1`. Rewrite `h` using `[DecoSet.mem_inertNb P.ne_bot]`. Conclude with `h.1`.

Establish `h` using `(Finset.mem_filter.1 e.2).2`. Rewrite `h` using `[DecoSet.mem_inertNb P.ne_bot]`. Conclude with `h.1`. Use `Finset.mem_filter.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[DecoSet.mem_inertNb P.ne_bot]`.

Conclude with `⟨Y.2.2.2.1, rfl, rfl⟩`. Rewrite using `[DecoSet.mem_inertNb P.ne_bot]`. Conclude with `⟨Y.2.2.2.2, hf, hbe⟩`. Introduce `e`. Establish `h` using `Finset.mem_filter.1 e.2`.

Rewrite `h` using `[DecoSet.mem_inertNb P.ne_bot, DecoSet.mem_inertNb P.ne_bot]`. Conclude with `Subtype.ext (Subtype.ext (Deco.ext rfl h.1.2.1.symm h.1.2.2.symm))`. Introduce `Y`. Both sides reduce to the same expression.
-/
theorem inertPath_card_eq_natCard {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P) (s t : List ℕ) (d f : DecoSet E n ST SG)
    (hf : f.1.f = d.1.f) (hbe : f.1.be = d.1.be) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      Nat.card {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun e => ⟨e.1.1.N, e.1.2.lat, e.1.2.uni, ?_, ?_⟩
      invFun := fun Y => ⟨⟨{ N := Y.1, f := d.1.f, be := d.1.be },
          d.2.replN Y.2.1 Y.2.2.1 (fun R => hi_sameAt_inert (hST R) Y.2.2.2.1)
            (fun w => hi_sameAt_inert (hSG w) Y.2.2.2.1)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := (Finset.mem_filter.1 e.2).1
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · have h := (Finset.mem_filter.1 e.2).2
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.1, rfl, rfl⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.2, hf, hbe⟩
  · intro e
    have h := Finset.mem_filter.1 e.2
    rw [DecoSet.mem_inertNb P.ne_bot, DecoSet.mem_inertNb P.ne_bot] at h
    exact Subtype.ext (Subtype.ext (Deco.ext rfl h.1.2.1.symm h.1.2.2.symm))
  · intro Y
    rfl

/- English proof (translation)
Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `e he hfe`. Rewrite `he`, `hfe` using `[DecoSet.mem_inertNb P.ne_bot]`. Conclude with `h ⟨hfe.2.1.trans he.2.1, hfe.2.2.trans he.2.2⟩`.
-/
theorem inertPath_card_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (s t : List ℕ)
    (d f : DecoSet E n ST SG) (h : ¬ (f.1.f = d.1.f ∧ f.1.be = d.1.be)) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hfe
  rw [DecoSet.mem_inertNb P.ne_bot] at he hfe
  exact h ⟨hfe.2.1.trans he.2.1, hfe.2.2.trans he.2.2⟩

/- English proof (translation)
Introduce `E _ _ _ n P ST SG hST hSG s t d f ⟨φ⟩`. Distinguish the cases in `hdec : f.1.f = d.1.f ∧ f.1.be = d.1.be`. Rewrite using `[inertPath_card_eq_natCard P hST hSG s t d f hdec.1 hdec.2, inertPath_card_eq_natCard P hST hSG t s d f hdec.1 hdec.2]`. Conclude with `Nat.card_congr φ`. Rewrite using `[inertPath_card_eq_zero P s t d f hdec, inertPath_card_eq_zero P t s d f hdec]`.
-/
theorem inertPath_card_comm : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet E n ST SG),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  intro E _ _ _ n P ST SG hST hSG s t d f ⟨φ⟩
  by_cases hdec : f.1.f = d.1.f ∧ f.1.be = d.1.be
  · rw [inertPath_card_eq_natCard P hST hSG s t d f hdec.1 hdec.2,
      inertPath_card_eq_natCard P hST hSG t s d f hdec.1 hdec.2]
    exact Nat.card_congr φ
  · rw [inertPath_card_eq_zero P s t d f hdec, inertPath_card_eq_zero P t s d f hdec]

end GlobalTheory
