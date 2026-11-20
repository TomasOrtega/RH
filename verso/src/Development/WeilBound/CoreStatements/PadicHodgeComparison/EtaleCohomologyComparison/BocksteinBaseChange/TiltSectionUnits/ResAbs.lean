import Mathlib

noncomputable section

open Ideal

namespace CrystallineSemistableComparison

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
  {R : Type*} [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
  [PerfectRing (IsLocalRing.ResidueField R) p]

def redPow (f : R →+* O) (n : ℕ) : R →+* ModP O p :=
  (iterateFrobenius (ModP O p) p n).comp ((Ideal.Quotient.mk _).comp f)

/- English proof (translation)
Rewrite using `[redPow, RingHom.comp_apply, iterateFrobenius_def, RingHom.comp_apply, map_pow]`.
-/
theorem redPow_apply (f : R →+* O) (n : ℕ) (y : R) :
    redPow (p := p) f n y = Ideal.Quotient.mk (span {(p : O)}) (f y ^ p ^ n) := by
  rw [redPow, RingHom.comp_apply, iterateFrobenius_def, RingHom.comp_apply, map_pow]

/- English proof (translation)
Set `ψ : IsLocalRing.ResidueField R →+* ModP O p` to `Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (redPow (p := p) f n) (fun y hy => by`. Rewrite using `[redPow_apply, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hn y hy)`. Set `u` to `(iterateFrobeniusEquiv (IsLocalRing.ResidueField R) p n).symm`. Set `g : IsLocalRing.ResidueField R →+* ModP O p` to `ψ.comp u.toRingHom`.

Set `s : IsLocalRing.ResidueField R →+* PreTilt O p` to `Perfection.lift p _ (ModP O p) g`. Use `⟨s, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `IsLocalRing.residue_surjective (u (IsLocalRing.residue R x))`. Establish `h1 : IsLocalRing.residue R y ^ p ^ n = IsLocalRing.residue R x`. Rewrite using `[hy, ← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv]`.

Conclude with `(iterateFrobeniusEquiv _ p n).apply_symm_apply _`. Establish `hm : y ^ p ^ n - x ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h1, sub_self]`. Establish `h2 : Ideal.Quotient.mk (span {(p : O)}) (PreTilt.untilt (s (IsLocalRing.residue R x))) = Ideal.Quotient.mk (span {(p : O)}) (f y ^ p ^ n)`. Rewrite using `[PreTilt.mk_untilt_eq_coeff_zero, ← redPow_apply]`.

Use `show g (IsLocalRing.residue R x) = _`. Use `show ψ (u (IsLocalRing.residue R x)) = _`. Rewrite using `[← hy]`. Both sides reduce to the same expression. Rewrite `h2` using `[Ideal.Quotient.eq, mem_span_singleton']`.

Take `⟨a, ha⟩` from `h2`. Use `⟨a, y ^ p ^ n - x, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_pow]`. Take the linear combination `-ha`.
-/
theorem exists_tilt_section (f : R →+* O) (n : ℕ)
    (hn : ∀ y ∈ IsLocalRing.maximalIdeal R, f y ^ p ^ n ∈ span {(p : O)}) :
    ∃ s : IsLocalRing.ResidueField R →+* PreTilt O p, ∀ x : R, ∃ (a : O) (m : R),
      m ∈ IsLocalRing.maximalIdeal R ∧ (s (IsLocalRing.residue R x)).untilt - f x = p * a + f m := by
  let ψ : IsLocalRing.ResidueField R →+* ModP O p :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (redPow (p := p) f n) (fun y hy => by
      rw [redPow_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hn y hy)
  let u := (iterateFrobeniusEquiv (IsLocalRing.ResidueField R) p n).symm
  let g : IsLocalRing.ResidueField R →+* ModP O p := ψ.comp u.toRingHom
  let s : IsLocalRing.ResidueField R →+* PreTilt O p := Perfection.lift p _ (ModP O p) g
  refine ⟨s, fun x => ?_⟩
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective (u (IsLocalRing.residue R x))
  have h1 : IsLocalRing.residue R y ^ p ^ n = IsLocalRing.residue R x := by
    rw [hy, ← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv]
    exact (iterateFrobeniusEquiv _ p n).apply_symm_apply _
  have hm : y ^ p ^ n - x ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h1, sub_self]
  have h2 : Ideal.Quotient.mk (span {(p : O)}) (PreTilt.untilt (s (IsLocalRing.residue R x))) =
      Ideal.Quotient.mk (span {(p : O)}) (f y ^ p ^ n) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, ← redPow_apply]
    show g (IsLocalRing.residue R x) = _
    show ψ (u (IsLocalRing.residue R x)) = _
    rw [← hy]
    rfl
  rw [Ideal.Quotient.eq, mem_span_singleton'] at h2
  obtain ⟨a, ha⟩ := h2
  refine ⟨a, y ^ p ^ n - x, hm, ?_⟩
  rw [map_sub, map_pow]
  linear_combination -ha

end CrystallineSemistableComparison
