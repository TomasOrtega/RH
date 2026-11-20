import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem local_of_finite (A S : Type) [CommRing A] [HenselianLocalRing A] [CommRing S] [Algebra A S]
    [Module.Finite A S] [Nontrivial S] (hid : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q
  rcases hid e he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · exact (H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.

A detailed English derivation is pending.
-/
theorem isLocal (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  haveI := sub_local A B hid {x}
  let y : Algebra.adjoin A ((({x} : Finset B)) : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin A _).val)
  · exact Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem maxIdeal_comap (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) :
    letI := isLocal A B hid
    letI := sub_local A B hid s
    (maximalIdeal B).comap (Algebra.adjoin A (s : Set B)).val = maximalIdeal (Algebra.adjoin A (s : Set B)) := by
  letI := isLocal A B hid
  letI := sub_local A B hid s
  haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A
  have : ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  exact IsLocalRing.eq_maximalIdeal this

/- English proof (translation)
Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : HenselianLocalRing B := by
  classical
  letI := isLocal A B hid
  refine ⟨fun f hf a0 h0 h1 => ?_⟩
  set s : Finset B := insert a0 f.coeffs
  let S := Algebra.adjoin A (s : Set B)
  letI := sub_local A B hid s
  haveI := sub_finite A B s
  haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc =>
    Algebra.subset_adjoin (by simp [s, hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, Algebra.subset_adjoin (by simp [s])⟩
  have hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B := fun y => by
    rw [← maxIdeal_comap A B hid s]; rfl
  have he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := fun p y => by
    rw [eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]; rfl
  have he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0 := fun p => he' p b0
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b0
    ((hmem _).2 (by rw [he, hgf]; exact h0))
    (by
      rw [← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]
      exact IsLocalRing.notMem_maximalIdeal.2 h1)
  refine ⟨a, ?_, (hmem _).1 ha'⟩
  rw [IsRoot.def, ← hgf, ← he', ha.eq_zero]; rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
