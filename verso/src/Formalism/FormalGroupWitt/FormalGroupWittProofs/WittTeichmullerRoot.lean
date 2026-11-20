import Formalism.FormalGroupWitt.Statement

noncomputable section

namespace Formalism.FG.WittVectorsCharZero

/- English proof (translation)
Introduce `a b h`. Establish `h1` using `WittVector.map_injective _ (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective h`. Conclude with `(WittVector.equiv l).symm.injective h1`.
-/
theorem zlToW_injective (l : ℕ) [Fact l.Prime] : Function.Injective (zlToW l) := by
  intro a b h
  have h1 := WittVector.map_injective _ (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective h
  exact (WittVector.equiv l).symm.injective h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hl : 1 ≤ l ^ d` using `Nat.one_le_pow _ _ (Fact.out : l.Prime).pos`. Rewrite using `[Nat.cast_sub hl, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), Nat.cast_one, zero_sub]`. Conclude with `neg_ne_zero.mpr one_ne_zero`.
-/
theorem neZero_cast (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : 1 ≤ d) :
    NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := by
  constructor
  have hl : 1 ≤ l ^ d := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  rw [Nat.cast_sub hl, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

end Formalism.FG.WittVectorsCharZero

namespace Formalism.FG

open Formalism.FG.WittVectorsCharZero

/- English proof (translation)
Introduce `l _`. Use `⟨fun m n h => ?_⟩` and prove the remaining obligations. Establish `h1 : ((m : ℤ_[l])) = (n : ℤ_[l])` using `zlToW_injective l (by rw [map_natCast, map_natCast]; exact h)`. Conclude with `h1` after adjusting the coercions.
-/
theorem witt_char_zero : Formalism.FG.WittCharZero := by
  intro l _
  refine ⟨fun m n h => ?_⟩
  have h1 : ((m : ℤ_[l])) = (n : ℤ_[l]) :=
    zlToW_injective l (by rw [map_natCast, map_natCast]; exact h)
  exact_mod_cast h1

/- English proof (translation)
Introduce `l _ d hd`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hNpos : 0 < l ^ d - 1`. Establish `: l ≤ l ^ d` using `Nat.le_self_pow (by omega) l`. Use linear arithmetic over natural numbers and integers.

Use `haveI : NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := neZero_cast l d hd`. Use `haveI : NeZero (((l ^ d - 1 : ℕ) : AlgebraicClosure (ZMod l))) := by`. Establish `h` using `NeZero.of_injective (f := algebraMap (ZMod l) (AlgebraicClosure (ZMod l))) (a := (((l ^ d - 1 : ℕ) : ZMod l))) (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective`. Rewrite `h` using `[map_natCast]`. Conclude with `h`.

Establish `hdeg : (Polynomial.cyclotomic (l ^ d - 1) (AlgebraicClosure (ZMod l))).degree ≠ 0`. Rewrite using `[Polynomial.degree_cyclotomic]`. Conclude with `(Nat.totient_pos.mpr hNpos).ne'` after adjusting the coercions. Take `⟨μ, hμ⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `hprim : IsPrimitiveRoot μ (l ^ d - 1)` using `Polynomial.isRoot_cyclotomic_iff.mp hμ`.

Use `⟨WittVector.teichmuller l μ, hprim.map_of_injective ?_⟩` and prove the remaining obligations. Introduce `a b h`. Establish `h2` using `congrArg (fun w => WittVector.coeff w 0) h`. Simplify `h2` using `[WittVector.teichmuller_coeff_zero]`.
-/
theorem witt_teichmuller_root : Formalism.FG.WittTeichRoot := by
  intro l _ d hd
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hNpos : 0 < l ^ d - 1 := by
    have : l ≤ l ^ d := Nat.le_self_pow (by omega) l
    omega
  haveI : NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := neZero_cast l d hd
  haveI : NeZero (((l ^ d - 1 : ℕ) : AlgebraicClosure (ZMod l))) := by
    have h := NeZero.of_injective (f := algebraMap (ZMod l) (AlgebraicClosure (ZMod l)))
      (a := (((l ^ d - 1 : ℕ) : ZMod l))) (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective
    rw [map_natCast] at h
    exact h
  have hdeg : (Polynomial.cyclotomic (l ^ d - 1) (AlgebraicClosure (ZMod l))).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hNpos).ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot μ (l ^ d - 1) := Polynomial.isRoot_cyclotomic_iff.mp hμ
  refine ⟨WittVector.teichmuller l μ, hprim.map_of_injective ?_⟩
  intro a b h
  have h2 := congrArg (fun w => WittVector.coeff w 0) h
  simpa [WittVector.teichmuller_coeff_zero] using h2

end Formalism.FG
