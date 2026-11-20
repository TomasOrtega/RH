import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionComponents
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace SectionComponents

variable {F : Type} [Field F] {n : ℕ}

/- English proof (translation)
Establish `_ : Algebra.FiniteType F (MvPolynomial (Fin n) F ⧸ Q)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) (Ideal.Quotient.mkₐ_surjective F Q)`. Establish `hlt` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top F (A := MvPolynomial (Fin n) F ⧸ Q)`. Establish `hnn` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ Q)`. Consider the cases of `h : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) with`. Consider the case `bot => rw [h] at hnn; exact absurd hnn (by simp)`.

Consider the case `coe y`. Rewrite `hlt` using `[h]`. Establish `: y ≠ ⊤` using `fun hy => by subst hy; exact lt_irrefl _ hlt`. Take `⟨m, rfl⟩` from `ENat.ne_top_iff_exists.mp this`. Conclude with `⟨m, rfl⟩`.
-/
theorem exists_ringKrullDim_quotient_eq (Q : Ideal (MvPolynomial (Fin n) F)) [Q.IsPrime] :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = m := by
  have _ : Algebra.FiniteType F (MvPolynomial (Fin n) F ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) (Ideal.Quotient.mkₐ_surjective F Q)
  have hlt := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top F
    (A := MvPolynomial (Fin n) F ⧸ Q)
  have hnn := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ Q)
  cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) with
  | bot => rw [h] at hnn; exact absurd hnn (by simp)
  | coe y =>
    rw [h] at hlt
    have : y ≠ ⊤ := fun hy => by subst hy; exact lt_irrefl _ hlt
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp this
    exact ⟨m, rfl⟩

/- English proof (translation)
Use `set p : Ideal (MvPolynomial (Fin n) F ⧸ W') := W.map (Ideal.Quotient.mk W')`. Establish `hp : p ≠ ⊥`. Take `⟨x, hxW, hxW'⟩` from `SetLike.exists_of_lt hlt`. Introduce `h`. Apply `hxW'` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk W' x ∈ p` using `Ideal.mem_map_of_mem _ hxW`. Rewrite `this` using `[h, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hquot : ringKrullDim ((MvPolynomial (Fin n) F ⧸ W') ⧸ p) = ringKrullDim (MvPolynomial (Fin n) F ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)`. Use `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le p hp` as an intermediate fact.

Rewrite `this` using `[hquot]`. Then use the resulting hypothesis.
-/
theorem ringKrullDim_quotient_add_one_le_of_lt {W' W : Ideal (MvPolynomial (Fin n) F)}
    [W'.IsPrime] (hlt : W' < W) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W') := by
  set p : Ideal (MvPolynomial (Fin n) F ⧸ W') := W.map (Ideal.Quotient.mk W')
  have hp : p ≠ ⊥ := by
    obtain ⟨x, hxW, hxW'⟩ := SetLike.exists_of_lt hlt
    intro h
    apply hxW'
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk W' x ∈ p := Ideal.mem_map_of_mem _ hxW
    rwa [h, Ideal.mem_bot] at this
  have hquot : ringKrullDim ((MvPolynomial (Fin n) F ⧸ W') ⧸ p) =
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le p hp
  rwa [hquot] at this

/- English proof (translation)
Establish `hWprime : W.IsPrime` using `hW.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hfW : f ∈ W` using `(le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)`. Use `set B := MvPolynomial (Fin n) F ⧸ P`. Establish `_ : Algebra.FiniteType F B` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)`.

Use `set W' : Ideal B := W.map (Ideal.Quotient.mk P)`. Establish `_ : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`. Apply `hf` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk P f ∈ W'` using `Ideal.mem_map_of_mem _ hfW`. Rewrite `this` using `[h, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hht : W'.height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)`.

Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'`. Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`. Rewrite `hform`, `hdrop` using `[hquot]`. Take `⟨m, hm⟩` from `exists_ringKrullDim_quotient_eq W`. Take `⟨k, hk⟩` from `exists_ringKrullDim_quotient_eq P`.

Express the relevant statement in the definitionally equal form `ringKrullDim B = _ at hk`. Rewrite `hform`, `hdrop` using `[hm, hk]`. Rewrite using `[hm]`. Express the relevant statement in the definitionally equal form `_ = ringKrullDim B`. Rewrite using `[hk]`.

Establish `hne : W'.height ≠ ⊤` using `ne_top_of_le_ne_top ENat.one_ne_top hht`. Take `⟨h, hh⟩` from `ENat.ne_top_iff_exists.mp hne`. Rewrite `hform`, `hht` using `[← hh]`. Establish `h1 : h ≤ 1` using `by exact_mod_cast hht`. Establish `h2 : h + m = k` using `by exact_mod_cast hform`.

Establish `h3 : m + 1 ≤ k` using `by exact_mod_cast hdrop`. Establish `: m + 1 = k` using `by omega`. Rewrite using `[← this]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ringKrullDim_quotient_add_one_eq {P W : Ideal (MvPolynomial (Fin n) F)} [P.IsPrime]
    {f : MvPolynomial (Fin n) F} (hf : f ∉ P) (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) F ⧸ P) := by
  have hWprime : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ P
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)
  set W' : Ideal B := W.map (Ideal.Quotient.mk P)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P f ∈ W' := Ideal.mem_map_of_mem _ hfW
    rwa [h, Ideal.mem_bot] at this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W
  obtain ⟨k, hk⟩ := exists_ringKrullDim_quotient_eq P
  change ringKrullDim B = _ at hk
  rw [hm, hk] at hform hdrop
  rw [hm]
  change _ = ringKrullDim B
  rw [hk]
  have hne : W'.height ≠ ⊤ := ne_top_of_le_ne_top ENat.one_ne_top hht
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hh] at hform hht
  have h1 : h ≤ 1 := by exact_mod_cast hht
  have h2 : h + m = k := by exact_mod_cast hform
  have h3 : m + 1 ≤ k := by exact_mod_cast hdrop
  have : m + 1 = k := by omega
  rw [← this]
  push_cast
  rfl

end SectionComponents

open SectionComponents in

/- English proof (translation)
Introduce `F _ n J f hequi hf`. Establish `fwd : ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F), W ∈ (P ⊔ Ideal.span {f}).minimalPrimes → W ∈ (J ⊔ Ideal.span {f}).minimalPrimes`. Introduce `P hP W hW`. Establish `_ : P.IsPrime` using `hP.1.1`. Establish `_ : W.IsPrime` using `hW.1.1`.

Use `⟨⟨hW.1.1, sup_le_sup_right hP.1.2 _ |>.trans hW.1.2⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, hJQ⟩ hQW`. Take `⟨P', hP', hP'Q⟩` from `Ideal.exists_minimalPrimes_le (le_sup_left.trans hJQ)`. Establish `_ : P'.IsPrime` using `hP'.1.1`. Take `⟨W', hW', hW'Q⟩` from `Ideal.exists_minimalPrimes_le (sup_le hP'Q (le_sup_right.trans hJQ) : P' ⊔ Ideal.span {f} ≤ Q)`.

Establish `_ : W'.IsPrime` using `hW'.1.1`. Establish `hW'W : W' ≤ W` using `hW'Q.trans hQW`. It suffices to establish `W' = W by rw [← this]; exact hW'Q`. Assume the negation of the conclusion as `hne`. Establish `hlt` using `ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW'W hne)`.

Rewrite `hlt` using `[ringKrullDim_quotient_add_one_eq (hf P hP) hW, hequi P hP P' hP', ← ringKrullDim_quotient_add_one_eq (hf P' hP') hW']`. Take `⟨m, hm⟩` from `exists_ringKrullDim_quotient_eq W'`. Rewrite `hlt` using `[hm]`. Establish `: m + 1 ≤ m` using `by exact_mod_cast hlt`. Use linear arithmetic over natural numbers and integers.

Introduce `P hP W`. Use `⟨fun hW => ⟨fwd P hP W hW, le_sup_left.trans hW.1.2⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hW, hPW⟩`. Establish `_ : W.IsPrime` using `hW.1.1`. Take `⟨W', hW', hW'W⟩` from `Ideal.exists_minimalPrimes_le (sup_le hPW (le_sup_right.trans hW.1.2) : P ⊔ Ideal.span {f} ≤ W)`.

Establish `heq : W = W'` using `le_antisymm (hW.2 (fwd P hP W' hW').1 hW'W) hW'W`. Rewrite using `[heq]` and apply the resulting hypothesis.
-/
theorem SectionComponents.proof_closed : SectionComponents.Statement := by
  intro F _ n J f hequi hf

  have fwd : ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes → W ∈ (J ⊔ Ideal.span {f}).minimalPrimes := by
    intro P hP W hW
    have _ : P.IsPrime := hP.1.1
    have _ : W.IsPrime := hW.1.1
    refine ⟨⟨hW.1.1, sup_le_sup_right hP.1.2 _ |>.trans hW.1.2⟩, ?_⟩
    rintro Q ⟨hQ, hJQ⟩ hQW
    obtain ⟨P', hP', hP'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hJQ)
    have _ : P'.IsPrime := hP'.1.1
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hP'Q (le_sup_right.trans hJQ) : P' ⊔ Ideal.span {f} ≤ Q)
    have _ : W'.IsPrime := hW'.1.1
    have hW'W : W' ≤ W := hW'Q.trans hQW
    suffices W' = W by rw [← this]; exact hW'Q
    by_contra hne
    have hlt := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW'W hne)
    rw [ringKrullDim_quotient_add_one_eq (hf P hP) hW, hequi P hP P' hP',
      ← ringKrullDim_quotient_add_one_eq (hf P' hP') hW'] at hlt
    obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W'
    rw [hm] at hlt
    have : m + 1 ≤ m := by exact_mod_cast hlt
    omega
  intro P hP W
  refine ⟨fun hW => ⟨fwd P hP W hW, le_sup_left.trans hW.1.2⟩, ?_⟩
  rintro ⟨hW, hPW⟩
  have _ : W.IsPrime := hW.1.1
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW (le_sup_right.trans hW.1.2) : P ⊔ Ideal.span {f} ≤ W)
  have heq : W = W' := le_antisymm (hW.2 (fwd P hP W' hW').1 hW'W) hW'W
  rwa [heq]

end GroundTheory.Heights₂.Heights
