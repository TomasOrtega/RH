import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.UnipotentAdelicQuotients.CuspidalCharExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GreenExists

open Polynomial Formalism.D.Classical Formalism.CyclotomicNorms Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq

variable {g : ℕ} [hg : Fact g.Prime]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i j hj hi => ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `h i j with h1 | h1` into its components or cases. Rewrite using `[h1, if_neg]`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use extensionality with `i j`. Establish `hi` using `i.2`.

Establish `hj` using `j.2`. Establish `hij : (i : ℕ) < d ∧ (j : ℕ) < d` using `by omega`. Break down `h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1` into its components or cases. Simplify using `only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]`. Simplify using `only at h1`.

Use linear arithmetic over natural numbers and integers. Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Establish `hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d` using `by omega`.

Break down `h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1` into its components or cases. Simplify using `only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]`. Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h1, h2, h3⟩ i j`.

Establish `hi` using `i.2`. Establish `hj` using `j.2`. Distinguish the cases in `hia : (i : ℕ) < a`. Distinguish the cases in `hja : (j : ℕ) < a`. Use `left`.

Use `congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩` as an intermediate fact. Simplify `this` using `only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff]`. Use `right`. Use linear arithmetic over natural numbers and integers. Use `left`.

Distinguish the cases in `hja : (j : ℕ) < a`. Rewrite using `[h1 i j hja (by omega), if_neg]; rintro rfl; omega`. Use `congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩` as an intermediate fact. Establish `e1 : a + (i - a) = (i : ℕ)` using `by omega`. Establish `e2 : a + (j - a) = (j : ℕ)` using `by omega`.

Establish `e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j` using `by omega`. Simplify `this` using `only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff]`.
-/
theorem mem_grUnipBlock_iff {d a : ℕ} (ha : a < d) (u : Gn g d) :
    u ∈ (grUnipBlock d a : Set (GL (Fin d) (ZMod g))) ↔
      InPar a (u : Mt g d) ∧ tl a (u : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (u : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rcases h i j with h1 | h1
      · rw [h1, if_neg]; rintro rfl; omega
      · omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : (i : ℕ) < d ∧ (j : ℕ) < d := by omega
      rcases h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1
      · simp only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]
      · simp only at h1; omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d := by omega
      rcases h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1
      · simp only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]
      · simp only at h1; omega
  · rintro ⟨h1, h2, h3⟩ i j
    have hi := i.2
    have hj := j.2
    by_cases hia : (i : ℕ) < a
    · by_cases hja : (j : ℕ) < a
      · left
        have := congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩
        simpa only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff] using this
      · right; omega
    · left
      by_cases hja : (j : ℕ) < a
      · rw [h1 i j hja (by omega), if_neg]; rintro rfl; omega
      · have := congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
        have e1 : a + (i - a) = (i : ℕ) := by omega
        have e2 : a + (j - a) = (j : ℕ) := by omega
        have e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
        simpa only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply,
          Fin.ext_iff] using this

/- English proof (translation)
Establish `hx : IsIntegral (ZMod g) z` using `Algebra.IsIntegral.isIntegral z`. Establish `has : Associated (minpoly (ZMod g) z) f` using `(minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)`. Rewrite using `[hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← has.dvd_iff_dvd_left, minpoly.dvd_iff]`. Simplify using `[sub_eq_zero]`.
-/
theorem pow_eq_self_iff {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) (n : ℕ) :
    z ^ g ^ n = z ↔ f.natDegree ∣ n := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have has : Associated (minpoly (ZMod g) z) f :=
    (minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)
  rw [hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← has.dvd_iff_dvd_left, minpoly.dvd_iff]
  simp [sub_eq_zero]

/- English proof (translation)
Establish `hroot : ∀ i, aeval (z ^ g ^ i) f = 0` using `fun i => by`. Use `aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) z f` as an intermediate fact. Rewrite `this` using `[hz, map_zero]`. Rewrite using `[← this]`. Use `congr 1`.

Rewrite using `[AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]`. Establish `hinj : ∀ i j, i < j → j < f.natDegree → z ^ g ^ i ≠ z ^ g ^ j` using `fun i j hij hj h => by`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Establish `h2 : (z ^ g ^ i) ^ g ^ (m + 1) = z ^ g ^ i`. Rewrite using `[← pow_mul, ← pow_add, ← add_assoc, ← h]`.

Use `Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hf (hroot i) _).1 h2)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup`. Use `Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup` and prove the remaining obligations. Rewrite `hi`, `hj` using `[← Finset.mem_def, Finset.mem_range]`.

Break down `lt_trichotomy i j with h1 | h1 | h1` into its components or cases. Conclude with `absurd h (hinj i j h1 hj)`. Conclude with `h1`. Conclude with `absurd h.symm (hinj j i h1 hi)`. Use `symm`.

Use `Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun w hw => ?_) ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hw`. Simplify `hroot i` using `[rootsBar, hf.ne_zero, aeval_def, eval_map]`. Use `card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))` as an intermediate fact. Simplify `this` using `[rootsBar]`.
-/
theorem rootsBar_eq {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) :
    rootsBar f = (Finset.range f.natDegree).val.map fun i => z ^ g ^ i := by
  have hroot : ∀ i, aeval (z ^ g ^ i) f = 0 := fun i => by
    have := aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) z f
    rw [hz, map_zero] at this
    rw [← this]
    congr 1
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hinj : ∀ i j, i < j → j < f.natDegree → z ^ g ^ i ≠ z ^ g ^ j := fun i j hij hj h => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h2 : (z ^ g ^ i) ^ g ^ (m + 1) = z ^ g ^ i := by
      rw [← pow_mul, ← pow_add, ← add_assoc, ← h]
    have := Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hf (hroot i) _).1 h2)
    omega
  have hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup := by
    refine Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup
    rw [← Finset.mem_def, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd h (hinj i j h1 hj)
    · exact h1
    · exact absurd h.symm (hinj j i h1 hi)
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun w hw => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hw
    simpa [rootsBar, hf.ne_zero, aeval_def, eval_map] using hroot i
  · have := card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))
    simpa [rootsBar] using this

end GlobalTheory.GreenExists
