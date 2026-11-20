import Mathlib
import ReciprocityTheory.DualLattices.CyclicRecursionStatement

noncomputable section

open Ideal

namespace ReciprocityTheory.PGsh

variable {p : ℕ} [hp : Fact p.Prime]

section Untilt

variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_mul, hf, ih]`.
-/
private lemma pow_p_pow_eq (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    f n ^ p ^ n = f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hf, ih]

/- English proof (translation)
Use `show Perfection.teichmuller p (span {(p : O)}) x = f 0`. Conclude with `Perfection.teichmuller_spec fun n => ⟨f n, (hx n).symm, by rw [pow_p_pow_eq f hf n]⟩`.
-/
lemma untilt_eq_of_coeff (x : PreTilt O p) (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n)
    (hx : ∀ n, Perfection.coeff (ModP O p) p n x = Ideal.Quotient.mk (span {(p : O)}) (f n)) :
    x.untilt = f 0 := by
  show Perfection.teichmuller p (span {(p : O)}) x = f 0
  exact Perfection.teichmuller_spec fun n => ⟨f n, (hx n).symm, by rw [pow_p_pow_eq f hf n]⟩

def ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (f n), fun n => by
    show (Ideal.Quotient.mk (span {(p : O)}) (f (n + 1))) ^ p = _
    rw [← map_pow, hf]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma coeff_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (ofRoots f hf) = Ideal.Quotient.mk (span {(p : O)}) (f n) :=
  rfl

/- English proof (translation)
The claim follows from `untilt_eq_of_coeff _ f hf (coeff_ofRoots f hf)`.
-/
lemma untilt_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    (ofRoots f hf).untilt = f 0 :=
  untilt_eq_of_coeff _ f hf (coeff_ofRoots f hf)

/- English proof (translation)
Apply `untilt_eq_of_coeff _ (fun n => f (n + 1)) (fun n => hf (n + 1))` to reduce the goal to its premises. Introduce `n`. Rewrite using `[← PreTilt.coeff_def, PreTilt.coeff_frobeniusEquiv_symm, PreTilt.coeff_def]`. Both sides reduce to the same expression.
-/
lemma untilt_symm_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    ((_root_.frobeniusEquiv (PreTilt O p) p).symm (ofRoots f hf)).untilt = f 1 := by
  apply untilt_eq_of_coeff _ (fun n => f (n + 1)) (fun n => hf (n + 1))
  intro n
  rw [← PreTilt.coeff_def, PreTilt.coeff_frobeniusEquiv_symm, PreTilt.coeff_def]
  rfl

end Untilt

section Roots

variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `h1 : 1 < v z ^ p` using `one_lt_pow₀ hlt hp.out.ne_zero`. Rewrite `h1` using `[← map_pow, h]`. Conclude with `absurd (hv.map_le_one w) (not_le.2 h1)`.
-/
private lemma le_one_of_pow (hv : v.Integers O) {z : C} {w : O} (h : z ^ p = algebraMap O C w) :
    v z ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < v z ^ p := one_lt_pow₀ hlt hp.out.ne_zero
  rw [← map_pow, h] at h1
  exact absurd (hv.map_le_one w) (not_le.2 h1)

/- English proof (translation)
Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos`. Take `⟨y, rfl⟩` from `hv.exists_of_le_one (le_one_of_pow C v O hv hz)`. Conclude with `⟨y, hv.hom_inj (by rw [map_pow, hz])⟩`.
-/
lemma exists_root (hv : v.Integers O) (x : O) : ∃ y : O, y ^ p = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz)
  exact ⟨y, hv.hom_inj (by rw [map_pow, hz])⟩

/- English proof (translation)
Establish `: NeZero (p : C)` using `⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic p C) (ne_of_gt (Polynomial.degree_cyclotomic_pos p C hp.out.pos))`. Establish `hzp : IsPrimitiveRoot z p` using `Polynomial.isRoot_cyclotomic_iff.1 hz`. Establish `hz1 : z ^ p = algebraMap O C 1` using `by rw [hzp.pow_eq_one, map_one]`. Take `⟨y, rfl⟩` from `hv.exists_of_le_one (le_one_of_pow C v O hv hz1)`.

Conclude with `⟨y, (IsPrimitiveRoot.map_iff_of_injective hv.hom_inj).1 hzp⟩`.
-/
lemma exists_primitiveRoot [CharZero C] (hv : v.Integers O) :
    ∃ ζ : O, IsPrimitiveRoot ζ p := by
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p C hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hz1 : z ^ p = algebraMap O C 1 := by rw [hzp.pow_eq_one, map_one]
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz1)
  exact ⟨y, (IsPrimitiveRoot.map_iff_of_injective hv.hom_inj).1 hzp⟩

private def rootSeq (r : O → O) (c : O) : ℕ → O
  | 0 => c
  | n + 1 => r (rootSeq r c n)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Use `choose r hr using exists_root (p := p) C v O hv`. Conclude with `⟨ofRoots (rootSeq O r p) (fun n => hr _), untilt_ofRoots _ _⟩`.
-/
theorem exists_pflat (hv : v.Integers O) : ∃ pflat : PreTilt O p, pflat.untilt = (p : O) := by
  choose r hr using exists_root (p := p) C v O hv
  exact ⟨ofRoots (rootSeq O r p) (fun n => hr _), untilt_ofRoots _ _⟩

/- English proof (translation)
Use `choose r hr using exists_root (p := p) C v O hv`. Take `⟨ζ, hζ⟩` from `exists_primitiveRoot (p := p) C v O hv`. Set `f : ℕ → O` to `fun n => Nat.casesOn n 1 (fun m => rootSeq O r ζ m)`. Establish `hf : ∀ n, f (n + 1) ^ p = f n`. Introduce `n`.

Consider the cases of `n with`. Consider the case `zero => exact hζ.pow_eq_one`. Consider the case `succ m => exact hr _`. Use `⟨ofRoots f hf, ?_⟩` and prove the remaining obligations. Rewrite using `[untilt_symm_ofRoots]`.

Conclude with `hζ`.
-/
theorem exists_eps [CharZero C] (hv : v.Integers O) :
    ∃ ε : PreTilt O p,
      IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p := by
  choose r hr using exists_root (p := p) C v O hv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot (p := p) C v O hv
  let f : ℕ → O := fun n => Nat.casesOn n 1 (fun m => rootSeq O r ζ m)
  have hf : ∀ n, f (n + 1) ^ p = f n := by
    intro n
    cases n with
    | zero => exact hζ.pow_eq_one
    | succ m => exact hr _
  refine ⟨ofRoots f hf, ?_⟩
  rw [untilt_symm_ofRoots]
  exact hζ

end Roots

end ReciprocityTheory.PGsh
