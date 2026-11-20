import Mathlib
import Formalism.CMTypeGalois.StatementGroup

namespace Formalism.Q3

open ZMod

/- English proof (translation)
Establish `hpo : p % 2 = 1` using `Nat.odd_iff.mp (hp.odd_of_ne_two hp2)`. Establish `hqo : q % 2 = 1` using `by omega`. Rewrite using `[jacobiSym.neg _ (Nat.odd_iff.mpr hpo)]`. Establish `h` using `jacobiSym.quadratic_reciprocity_if hpo hqo`. Break down `Nat.odd_mod_four_iff.mp hpo with h1 | h3` into its components or cases.

Rewrite using `[χ₄_nat_one_mod_four h1, one_mul, ← h]`. Simplify using `[h1]`. Rewrite using `[χ₄_nat_three_mod_four h3, ← h]`. Simplify using `[h3, hq4]`.
-/
lemma kron_odd (q p : ℕ) (hq4 : q % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo : q % 2 = 1 := by omega
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hpo)]
  have h := jacobiSym.quadratic_reciprocity_if hpo hqo
  rcases Nat.odd_mod_four_iff.mp hpo with h1 | h3
  · rw [χ₄_nat_one_mod_four h1, one_mul, ← h]
    simp [h1]
  · rw [χ₄_nat_three_mod_four h3, ← h]
    simp [h3, hq4]

/- English proof (translation)
Introduce `q hq hq4`. Establish `hqo : Odd q` using `Nat.odd_iff.mpr (by omega)`. Use `⟨fun p hp hp2 _ => kron_odd q p hq4 hp hp2, ?_, ?_⟩` and prove the remaining obligations. Unfold `chiQ`. Rewrite using `[jacobiSym.at_two hqo, χ₈_nat_eq_if_mod_eight]`.

Rewrite using `[if_neg (by omega)]`. Distinguish the cases in `h8 : q % 8 = 7`. Rewrite using `[if_pos (Or.inr h8)]`. Simplify using `[h8]`. Rewrite using `[if_neg (by omega)]; simp [h8]`.

Unfold `chiQ`. Rewrite using `[jacobiSym.at_neg_one hqo, χ₄_nat_three_mod_four hq4]`.
-/
theorem kroneckerMeaning : KroneckerMeaning := by
  intro q hq hq4
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  refine ⟨fun p hp hp2 _ => kron_odd q p hq4 hp hp2, ?_, ?_⟩
  · unfold chiQ
    rw [jacobiSym.at_two hqo, χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega)]
    by_cases h8 : q % 8 = 7
    · rw [if_pos (Or.inr h8)]; simp [h8]
    · rw [if_neg (by omega)]; simp [h8]
  · unfold chiQ
    rw [jacobiSym.at_neg_one hqo, χ₄_nat_three_mod_four hq4]

/- English proof (translation)
Unfold `sgn`. Rewrite using `[if_pos rfl]`.
-/
lemma sgn_one : sgn 1 = 1 := by
  unfold sgn; rw [if_pos rfl]

/- English proof (translation)
Introduce `h`. Establish `hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `x (rfl | rfl)`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]`.

Conclude with `ha`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]`. Conclude with `hb`. Use `hle h` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker, Pi.evalMonoidHom_apply]`.

Establish `h' : (-1 : ℤˣ) = 1` using `this`. Conclude with `absurd h' (by decide)`.
-/
lemma cc_not_mem (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by
  intro h
  have hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact ha
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact hb
  have := hle h
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at this
  have h' : (-1 : ℤˣ) = 1 := this
  exact absurd h' (by decide)

end Formalism.Q3
