import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

/- English proof (translation)
Take `⟨q, hq⟩` from `Ideal.exists_maximal S`. Use `IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨e, he, H⟩` from `GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q`. Break down `hid e he with h | h` into its components or cases. Conclude with `absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)`.

Conclude with `(H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))`.
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
The claim follows from `Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)`.
-/
theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

/- English proof (translation)
Use `haveI := sub_finite A B s`. Use `local_of_finite A _ fun e he => ?_` and prove the remaining obligations. Break down `hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h` into its components or cases. Conclude with `Or.inl (Subtype.ext h)`. Conclude with `Or.inr (Subtype.ext h)`.
-/
theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/- English proof (translation)
Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Use `haveI := sub_local A B hid {x}`. Set `y : Algebra.adjoin A ((({x} : Finset B)) : Set B)` to `⟨x, Algebra.subset_adjoin (by simp)⟩`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h` into its components or cases. Conclude with `Or.inl (h.map (Algebra.adjoin A _).val)`.

Conclude with `Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)`.
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
Use `letI := isLocal A B hid`. Use `letI := sub_local A B hid s`. Use `haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A`. Establish `: ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _`. Conclude with `IsLocalRing.eq_maximalIdeal this`.
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
Use `letI := isLocal A B hid`. Use `⟨fun f hf a0 h0 h1 => ?_⟩` and prove the remaining obligations. Use `set s : Finset B := insert a0 f.coeffs`. Set `S` to `Algebra.adjoin A (s : Set B)`. Use `letI := sub_local A B hid s`.

Use `haveI := sub_finite A B s`. Use `haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S`. Establish `hc : (↑f.coeffs : Set B) ⊆ S.toSubring` using `fun c hc => Algebra.subset_adjoin (by simp [s, hc])`. Set `g : S[X]` to `f.toSubring S.toSubring hc`. Establish `hgf : g.map S.val.toRingHom = f` using `f.map_toSubring S.toSubring hc`.

Set `b0 : S` to `⟨a0, Algebra.subset_adjoin (by simp [s])⟩`. Establish `hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B` using `fun y => by`. Rewrite using `[← maxIdeal_comap A B hid s]`. Both sides reduce to the same expression. Establish `he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B)` using `fun p y => by`.

Rewrite using `[eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]`. Both sides reduce to the same expression. Establish `he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0` using `fun p => he' p b0`. Establish `hgm : g.Monic`. Rewrite `hf` using `[← hgf]`.

Conclude with `Polynomial.monic_of_injective Subtype.val_injective hf`. Take `⟨a, ha, ha'⟩` from `HenselianLocalRing.is_henselian g hgm b0 ((hmem _).2 (by rw [he, hgf]; exact h0)) (by`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]`. Conclude with `IsLocalRing.notMem_maximalIdeal.2 h1)`. Use `⟨a, ?_, (hmem _).1 ha'⟩` and prove the remaining obligations.

Rewrite using `[IsRoot.def, ← hgf, ← he', ha.eq_zero]`. Both sides reduce to the same expression.
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
Introduce `A B _ _ _ _ f hf hid`. Use `letI : Algebra A B := f.toAlgebra`. Use `haveI : Algebra.IsIntegral A B := ⟨hf⟩`. Conclude with `⟨hens A B hid⟩`.
-/
theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
