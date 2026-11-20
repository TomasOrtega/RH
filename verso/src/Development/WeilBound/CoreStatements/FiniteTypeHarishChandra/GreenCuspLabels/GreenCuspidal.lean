import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.LabelMapNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal rootsBar
open ReciprocityTheory.Ty.Fin GlobalTheory.GLq GlobalTheory.CompanionTheory.TyFin.CuspIff GlobalTheory.CompanionTheory.TyFin.CuspLabel

noncomputable section

namespace PositivityTheory.GreenCharacters

/- English proof (translation)
Establish `hP : ∀ v : V, (∑ u : G, if u ∈ U then ρ u v else 0) = 0`. Introduce `v`. Apply `h` to reduce the goal to its premises. Introduce `u hu`. Rewrite using `[map_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft u) _ _ ?_` and prove the remaining obligations. Introduce `w`. Simplify using `only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, U.mul_mem_cancel_left hu]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hL : (∑ u : G, if u ∈ U then ρ u else 0) = 0`.

Use extensionality with `v`. Rewrite using `[LinearMap.sum_apply, LinearMap.zero_apply, ← hP v]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Representation.character]`. Use `_ = 0 := by rw [hL, map_zero]`.
-/
theorem sum_char_eq_zero {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : ∀ v : V, (∀ u ∈ U, ρ u v = v) → v = 0) : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0 := by
  classical
  have hP : ∀ v : V, (∑ u : G, if u ∈ U then ρ u v else 0) = 0 := by
    intro v
    apply h
    intro u hu
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ ?_
    intro w
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, U.mul_mem_cancel_left hu]
    split_ifs <;> simp
  have hL : (∑ u : G, if u ∈ U then ρ u else 0) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply, ← hP v]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> rfl
  calc (∑ u : G, if u ∈ U then ρ.character u else 0)
      = LinearMap.trace ℂ V (∑ u : G, if u ∈ U then ρ u else 0) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        split_ifs <;> simp [Representation.character]
    _ = 0 := by rw [hL, map_zero]

/- English proof (translation)
Set `b : Fin d → Fin 2` to `fun i => if (i : ℕ) < a then 0 else 1`. Use `hc 2 b ?_ le_rfl v fun u hu => hv u ?_` and prove the remaining obligations. Introduce `c fin_cases c`. Conclude with `⟨⟨0, by omega⟩, by simp [b, h0]⟩`. Conclude with `⟨⟨a, h1⟩, by simp [b]⟩`.

Introduce `i j`. Distinguish the cases in `hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)`. Conclude with `Or.inr hij`. Use `left`. Distinguish the cases in `hi : (i : ℕ) < a`.

Establish `hj : (j : ℕ) < a` using `by omega`. Conclude with `hu.2 i j (by simp [b, hi, hj])`. Distinguish the cases in `hj : (j : ℕ) < a`. Establish `hne : i ≠ j` using `by rintro rfl; exact hi hj`. Rewrite using `[if_neg hne]`.

Conclude with `hu.1.1 i j (by simp [b, hi, hj])`. Conclude with `hu.2 i j (by simp [b, hi, hj])`.
-/
theorem fixed_eq_zero {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} (τ : FDRep ℂ (GL (Fin d) K))
    (hc : IsCuspidal K τ) (h0 : 0 < a) (h1 : a < d) (v : τ) (hv : ∀ u ∈ stdRadical K d a, τ.ρ u v = v) : v = 0 := by
  let b : Fin d → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  refine hc 2 b ?_ le_rfl v fun u hu => hv u ?_
  · intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [b, h0]⟩
    · exact ⟨⟨a, h1⟩, by simp [b]⟩
  · intro i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by omega
      exact hu.2 i j (by simp [b, hi, hj])
    · by_cases hj : (j : ℕ) < a
      · have hne : i ≠ j := by rintro rfl; exact hi hj
        rw [if_neg hne]
        exact hu.1.1 i j (by simp [b, hi, hj])
      · exact hu.2 i j (by simp [b, hi, hj])

variable {g : ℕ} [Fact g.Prime]

def conv (L : LabelDatum g) : LabelConv (ZMod g) where
  ι := L.teich
  ι_inj := L.teich_inj
  gen := L.gen
  gen_order d hd := by rw [ZMod.card]; exact L.gen_order d hd
  gen_norm d e hd he := by rw [ZMod.card]; exact L.gen_norm d e hd he

/- English proof (translation)
Substitute `ha hb` using the available equality. Simplify using `[Formalism.MainNotions.ArithmeticCylinders.entN]`.
-/
theorem entN_eq {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (i j : Fin N) {a b : ℕ}
    (ha : a = i) (hb : b = j) : Formalism.MainNotions.ArithmeticCylinders.entN M a b = M i j := by
  subst ha hb
  simp [Formalism.MainNotions.ArithmeticCylinders.entN]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, ht, hb⟩ i j`. Establish `hid` using `i.isLt`. Establish `hjd` using `j.isLt`. Distinguish the cases in `hi : (i : ℕ) < a`.

Distinguish the cases in `hj : (j : ℕ) < a`. Use `left`. Use `congrFun (congrFun ht ⟨i, hi⟩) ⟨j, hj⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.ArithmeticCylinders.entN M (i : ℕ) (j : ℕ) = (1 : Matrix (Fin a) (Fin a) (ZMod g)) ⟨i, hi⟩ ⟨j, hj⟩ at this`. Rewrite `this` using `[entN_eq M i j rfl rfl, Matrix.one_apply]`.

Rewrite using `[this]`. Conclude with `if_congr (by simp [Fin.ext_iff]) rfl rfl`. Conclude with `Or.inr ⟨hi, not_lt.mp hj⟩`. Distinguish the cases in `hj : (j : ℕ) < a`. Use `left`.

Establish `hne : i ≠ j`. Introduce `e`. Substitute `e` using the available equality. Conclude with `hi hj`. Rewrite using `[if_neg hne]`.

Conclude with `hP i j hj (not_lt.mp hi)`. Use `left`. Establish `hi' : (i : ℕ) - a < d - a` using `by omega`. Establish `hj' : (j : ℕ) - a < d - a` using `by omega`. Use `congrFun (congrFun hb ⟨i - a, hi'⟩) ⟨j - a, hj'⟩` as an intermediate fact.

Express the relevant statement in the definitionally equal form `Formalism.MainNotions.ArithmeticCylinders.entN M (a + ((i : ℕ) - a)) (a + ((j : ℕ) - a)) = (1 : Matrix (Fin (d - a)) (Fin (d - a)) (ZMod g)) ⟨i - a, hi'⟩ ⟨j - a, hj'⟩ at this`. Rewrite `this` using `[entN_eq M i j (by omega) (by omega), Matrix.one_apply]`. Rewrite using `[this]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Fin.ext_iff, Fin.ext_iff]`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `hM`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hj hi`.

Break down `hM i j with h | h` into its components or cases. Rewrite using `[h, if_neg]`. Introduce `e`. Substitute `e` using the available equality. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.ArithmeticCylinders.entN M (i : ℕ) (j : ℕ) = (1 : Matrix (Fin a) (Fin a) (ZMod g)) i j`.

Rewrite using `[entN_eq M ⟨i, by omega⟩ ⟨j, by omega⟩ rfl rfl, Matrix.one_apply]`. Break down `hM ⟨i, by omega⟩ ⟨j, by omega⟩ with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `if_congr (by simp [Fin.ext_iff]) rfl rfl`. It suffices to derive a contradiction.

Use `h.2` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`.

Establish `hj` using `j.isLt`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.ArithmeticCylinders.entN M (a + (i : ℕ)) (a + (j : ℕ)) = (1 : Matrix (Fin (d - a)) (Fin (d - a)) (ZMod g)) i j`. Rewrite using `[entN_eq M ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ rfl rfl, Matrix.one_apply]`. Break down `hM ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ with h | h` into its components or cases. Rewrite using `[h]`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Simplify using `only [Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use `h.1` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem rad_iff {d a : ℕ} (had : a ≤ d) (M : Mt g d) :
    (InPar a M ∧ tl a M = 1 ∧ br a (d - a) M = 1) ↔
      ∀ i j : Fin d, M i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
  constructor
  · rintro ⟨hP, ht, hb⟩ i j
    have hid := i.isLt
    have hjd := j.isLt
    by_cases hi : (i : ℕ) < a
    · by_cases hj : (j : ℕ) < a
      · left
        have := congrFun (congrFun ht ⟨i, hi⟩) ⟨j, hj⟩
        change Formalism.MainNotions.ArithmeticCylinders.entN M (i : ℕ) (j : ℕ) = (1 : Matrix (Fin a) (Fin a) (ZMod g)) ⟨i, hi⟩ ⟨j, hj⟩ at this
        rw [entN_eq M i j rfl rfl, Matrix.one_apply] at this
        rw [this]
        exact if_congr (by simp [Fin.ext_iff]) rfl rfl
      · exact Or.inr ⟨hi, not_lt.mp hj⟩
    · by_cases hj : (j : ℕ) < a
      · left
        have hne : i ≠ j := by
          intro e
          subst e
          exact hi hj
        rw [if_neg hne]
        exact hP i j hj (not_lt.mp hi)
      · left
        have hi' : (i : ℕ) - a < d - a := by omega
        have hj' : (j : ℕ) - a < d - a := by omega
        have := congrFun (congrFun hb ⟨i - a, hi'⟩) ⟨j - a, hj'⟩
        change Formalism.MainNotions.ArithmeticCylinders.entN M (a + ((i : ℕ) - a)) (a + ((j : ℕ) - a)) =
          (1 : Matrix (Fin (d - a)) (Fin (d - a)) (ZMod g)) ⟨i - a, hi'⟩ ⟨j - a, hj'⟩ at this
        rw [entN_eq M i j (by omega) (by omega), Matrix.one_apply] at this
        rw [this]
        refine if_congr ?_ rfl rfl
        rw [Fin.ext_iff, Fin.ext_iff]
        simp only
        omega
  · intro hM
    refine ⟨?_, ?_, ?_⟩
    · intro i j hj hi
      rcases hM i j with h | h
      · rw [h, if_neg]
        intro e
        subst e
        omega
      · omega
    · refine Matrix.ext fun i j => ?_
      have hi := i.isLt
      have hj := j.isLt
      change Formalism.MainNotions.ArithmeticCylinders.entN M (i : ℕ) (j : ℕ) = (1 : Matrix (Fin a) (Fin a) (ZMod g)) i j
      rw [entN_eq M ⟨i, by omega⟩ ⟨j, by omega⟩ rfl rfl, Matrix.one_apply]
      rcases hM ⟨i, by omega⟩ ⟨j, by omega⟩ with h | h
      · rw [h]
        exact if_congr (by simp [Fin.ext_iff]) rfl rfl
      · exfalso
        have := h.2
        simp only at this
        omega
    · refine Matrix.ext fun i j => ?_
      have hi := i.isLt
      have hj := j.isLt
      change Formalism.MainNotions.ArithmeticCylinders.entN M (a + (i : ℕ)) (a + (j : ℕ)) = (1 : Matrix (Fin (d - a)) (Fin (d - a)) (ZMod g)) i j
      rw [entN_eq M ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ rfl rfl, Matrix.one_apply]
      rcases hM ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ with h | h
      · rw [h]
        refine if_congr ?_ rfl rfl
        simp only [Fin.ext_iff]
        omega
      · exfalso
        have := h.1
        simp only at this
        omega

open Classical in

/- English proof (translation)
Unfold `res`. Establish `hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero))`. Rewrite using `[mul_eq_zero, or_iff_right hg]`. Establish `key : ∀ x : Gn g d, (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = ((1 : Gn g a) : Mt g a) ∧ br a (d - a) (x : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a))) ↔ x ∈ stdRadical (ZMod g) d a`. Introduce `x`.

Rewrite using `[Units.val_one, Units.val_one, rad_iff had, mem_stdRadical]`. Rewrite using `[Finset.sum_congr rfl fun x _ => if_congr (key x) rfl rfl]`.
-/
theorem res_eq_zero_iff {d a : ℕ} (had : a ≤ d) (χ : Gn g d → ℂ) :
    res a (d - a) χ 1 1 = 0 ↔ (∑ u : Gn g d, if u ∈ stdRadical (ZMod g) d a then χ u else 0) = 0 := by
  unfold res
  have hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero))
  rw [mul_eq_zero, or_iff_right hg]
  have key : ∀ x : Gn g d, (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
      br a (d - a) (x : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a))) ↔ x ∈ stdRadical (ZMod g) d a := by
    intro x
    rw [Units.val_one, Units.val_one, rad_iff had, mem_stdRadical]
  rw [Finset.sum_congr rfl fun x _ => if_congr (key x) rfl rfl]

/- English proof (translation)
Use `⟨hd, ⟨τ, hs, fun x => rfl⟩, fun a ha had => ?_⟩` and prove the remaining obligations. Rewrite using `[res_eq_zero_iff had.le]`. Use `sum_char_eq_zero τ.ρ (stdRadical (ZMod g) d a) (fixed_eq_zero τ hc ha had) using 1` and compare the differences between its conclusion and the goal. Use `first`. Consider the case `rfl`.

Consider the case `simp [FDRep.character, Representation.character]`.
-/
theorem isCusp_character {d : ℕ} (hd : 0 < d) (τ : FDRep ℂ (Gn g d)) (hs : Simple τ) (hc : IsCuspidal (ZMod g) τ) :
    IsCusp τ.character := by
  refine ⟨hd, ⟨τ, hs, fun x => rfl⟩, fun a ha had => ?_⟩
  rw [res_eq_zero_iff had.le]
  classical
  convert sum_char_eq_zero τ.ρ (stdRadical (ZMod g) d a) (fixed_eq_zero τ hc ha had) using 1
  first
    | rfl
    | simp [FDRep.character, Representation.character]

/- English proof (translation)
Use `isCuspidal_of_sum_char (ZMod g) d τ fun a ha had => ?_` and prove the remaining obligations. Use `(res_eq_zero_iff had.le τ.character).mp (h.2.2 a ha had)` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun u _ => if_congr mem_stdRadical.symm rfl rfl`.
-/
theorem isCuspidal_of_isCusp {d : ℕ} (τ : FDRep ℂ (Gn g d)) (h : IsCusp τ.character) : IsCuspidal (ZMod g) τ := by
  classical
  refine isCuspidal_of_sum_char (ZMod g) d τ fun a ha had => ?_
  have := (res_eq_zero_iff had.le τ.character).mp (h.2.2 a ha had)
  refine Eq.trans ?_ this
  exact Finset.sum_congr rfl fun u _ => if_congr mem_stdRadical.symm rfl rfl

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar at hx`. Establish `h2 : Polynomial.eval x (P.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0` using `(Polynomial.mem_roots'.mp hx).2`. Rewrite `h2` using `[Polynomial.eval_map_algebraMap]`. Then use the resulting hypothesis.
-/
theorem aeval_of_mem_rootsBar {P : (ZMod g)[X]} {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) :
    aeval x P = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar at hx
  have h2 : Polynomial.eval x (P.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0 :=
    (Polynomial.mem_roots'.mp hx).2
  rwa [Polynomial.eval_map_algebraMap] at h2

/- English proof (translation)
Unfold `IsPrimeLab`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hm, hi, h0, hd⟩`. Use `⟨hm, hi, ?_, hd⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `h0 (by simp)`. Introduce and unpack `⟨hm, hi, hX, hd⟩`. Use `⟨hm, hi, ?_, hd⟩` and prove the remaining obligations. Introduce `h0`. Apply `hX` to reduce the goal to its premises.

Establish `hdvd : X ∣ P` using `Polynomial.X_dvd_iff.mpr h0`. Conclude with `(Polynomial.eq_of_monic_of_associated Polynomial.monic_X hm (Polynomial.irreducible_X.associated_of_dvd hi hdvd)).symm`.
-/
theorem isPrimeLab_iff {d : ℕ} {P : (ZMod g)[X]} :
    IsPrimeLab d P ↔ P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  unfold IsPrimeLab
  constructor
  · rintro ⟨hm, hi, h0, hd⟩
    refine ⟨hm, hi, ?_, hd⟩
    rintro rfl
    exact h0 (by simp)
  · rintro ⟨hm, hi, hX, hd⟩
    refine ⟨hm, hi, ?_, hd⟩
    intro h0
    apply hX
    have hdvd : X ∣ P := Polynomial.X_dvd_iff.mpr h0
    exact (Polynomial.eq_of_monic_of_associated Polynomial.monic_X hm
      (Polynomial.irreducible_X.associated_of_dvd hi hdvd)).symm

/- English proof (translation)
Establish `hex : ∃ n : ℕ, L.gen d ^ m = L.gen d ^ n` using `⟨m, rfl⟩`. Unfold `thetaOf`. Rewrite using `[dif_pos hex]`. Establish `hc : L.gen d ^ m = L.gen d ^ hex.choose` using `hex.choose_spec`. Establish `hg2` using `(Fact.out : g.Prime).two_le`.

Establish `hgd : g ≤ g ^ d` using `Nat.le_self_pow hd.ne' g`. Establish `hN : 0 < orderOf (L.gen d)`. Rewrite using `[L.gen_order d hd]`. Use linear arithmetic over natural numbers and integers. Establish `heq : hex.choose % orderOf (L.gen d) = m % orderOf (L.gen d)`.

Use `pow_injOn_Iio_orderOf (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) ?_` and prove the remaining obligations. Simplify using `only [pow_mod_orderOf]`. Conclude with `hc.symm`. Establish `hmod : hex.choose ≡ m [MOD g ^ d - 1]`. Rewrite using `[← L.gen_order d hd]`.

Conclude with `heq`. Establish `ht : L.teich x ^ (g ^ d - 1) = 1`. Rewrite using `[← map_pow, hx, map_one]`. Establish `hdvd : orderOf (L.teich x) ∣ g ^ d - 1` using `orderOf_dvd_of_pow_eq_one ht`. Rewrite using `[← pow_mod_orderOf (L.teich x) hex.choose, ← pow_mod_orderOf (L.teich x) m]`.

Conclude with `congrArg _ (Nat.ModEq.of_dvd hdvd hmod)`.
-/
theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1)
    (m : ℕ) : thetaOf L d x (L.gen d ^ m) = L.teich x ^ m := by
  have hex : ∃ n : ℕ, L.gen d ^ m = L.gen d ^ n := ⟨m, rfl⟩
  unfold thetaOf
  rw [dif_pos hex]
  have hc : L.gen d ^ m = L.gen d ^ hex.choose := hex.choose_spec
  have hg2 := (Fact.out : g.Prime).two_le
  have hgd : g ≤ g ^ d := Nat.le_self_pow hd.ne' g
  have hN : 0 < orderOf (L.gen d) := by
    rw [L.gen_order d hd]
    omega
  have heq : hex.choose % orderOf (L.gen d) = m % orderOf (L.gen d) := by
    refine pow_injOn_Iio_orderOf (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) ?_
    simp only [pow_mod_orderOf]
    exact hc.symm
  have hmod : hex.choose ≡ m [MOD g ^ d - 1] := by
    rw [← L.gen_order d hd]
    exact heq
  have ht : L.teich x ^ (g ^ d - 1) = 1 := by
    rw [← map_pow, hx, map_one]
  have hdvd : orderOf (L.teich x) ∣ g ^ d - 1 := orderOf_dvd_of_pow_eq_one ht
  rw [← pow_mod_orderOf (L.teich x) hex.choose, ← pow_mod_orderOf (L.teich x) m]
  exact congrArg _ (Nat.ModEq.of_dvd hdvd hmod)

/- English proof (translation)
Take `⟨hm, hi, hX, hdeg, hlab⟩` from `hl`. Establish `hdeg' : P.natDegree = d` using `by simpa using hdeg`. Establish `hP : IsPrimeLab d P` using `isPrimeLab_iff.mpr ⟨hm, hi, hX, hdeg'⟩`. Use `⟨hP, isCusp_character hd τ hs hc, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy z hz`.

Establish `hxP` using `aeval_of_mem_rootsBar hx`. Establish `hzP` using `aeval_of_mem_rootsBar hz`. Establish `hx1 : x ^ (g ^ d - 1) = 1`. Use `root_pow_eq_one hm hi hX hxP` as an intermediate fact. Rewrite `this` using `[ZMod.card, hdeg']`. Then use the resulting hypothesis.

Establish `hcX : (y : Matrix (Fin d) (Fin d) (ZMod g)).charpoly ≠ X`. Introduce `hE`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det _).mp y.isUnit`. Rewrite `hdet` using `[Matrix.det_eq_sign_charpoly_coeff, hE, Polynomial.coeff_X_zero, mul_zero]`. Conclude with `not_isUnit_zero hdet`.

Establish `hcdeg : (y : Matrix (Fin d) (Fin d) (ZMod g)).charpoly.natDegree = d`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hz1 : z ^ (g ^ d - 1) = 1`. Use `root_pow_eq_one (Matrix.charpoly_monic _) hy hcX hzP` as an intermediate fact. Rewrite `this` using `[ZMod.card, hcdeg]`. Then use the resulting hypothesis.

Establish `hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1)`. Rewrite using `[← L.gen_order d hd]`. Conclude with `IsPrimitiveRoot.orderOf _`. Establish `hg2` using `(Fact.out : g.Prime).two_le`. Establish `hgd : g ≤ g ^ d` using `Nat.le_self_pow hd.ne' g`.

Use `haveI : NeZero (g ^ d - 1) := ⟨by omega⟩`. Take `⟨m, -, hmz⟩` from `hprim.eq_pow_of_pow_eq_one hz1`. Simplify using `only [Fintype.card_fin, conv, ZMod.card] at hlab`. Establish `htr` using `hlab x hxP y hy z hzP m hmz`. Rewrite using `[show τ.character y = _ from htr]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hmz, ← pow_mul, thetaOf_gen_pow L hd hx1]`.
-/
theorem isCuspOf_character (L : LabelDatum g) {d : ℕ} (hd : 0 < d) (τ : FDRep ℂ (Gn g d)) (P : (ZMod g)[X])
    (hs : Simple τ) (hc : IsCuspidal (ZMod g) τ) (hl : HasCuspLabel (conv L) τ P) : IsCuspOf L P τ.character := by
  obtain ⟨hm, hi, hX, hdeg, hlab⟩ := hl
  have hdeg' : P.natDegree = d := by simpa using hdeg
  have hP : IsPrimeLab d P := isPrimeLab_iff.mpr ⟨hm, hi, hX, hdeg'⟩
  refine ⟨hP, isCusp_character hd τ hs hc, ?_⟩
  intro x hx y hy z hz
  have hxP := aeval_of_mem_rootsBar hx
  have hzP := aeval_of_mem_rootsBar hz
  have hx1 : x ^ (g ^ d - 1) = 1 := by
    have := root_pow_eq_one hm hi hX hxP
    rwa [ZMod.card, hdeg'] at this
  have hcX : (y : Matrix (Fin d) (Fin d) (ZMod g)).charpoly ≠ X := by
    intro hE
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [Matrix.det_eq_sign_charpoly_coeff, hE, Polynomial.coeff_X_zero, mul_zero] at hdet
    exact not_isUnit_zero hdet
  have hcdeg : (y : Matrix (Fin d) (Fin d) (ZMod g)).charpoly.natDegree = d := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hz1 : z ^ (g ^ d - 1) = 1 := by
    have := root_pow_eq_one (Matrix.charpoly_monic _) hy hcX hzP
    rwa [ZMod.card, hcdeg] at this
  have hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd]
    exact IsPrimitiveRoot.orderOf _
  have hg2 := (Fact.out : g.Prime).two_le
  have hgd : g ≤ g ^ d := Nat.le_self_pow hd.ne' g
  haveI : NeZero (g ^ d - 1) := ⟨by omega⟩
  obtain ⟨m, -, hmz⟩ := hprim.eq_pow_of_pow_eq_one hz1
  simp only [Fintype.card_fin, conv, ZMod.card] at hlab
  have htr := hlab x hxP y hy z hzP m hmz
  rw [show τ.character y = _ from htr]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmz, ← pow_mul, thetaOf_gen_pow L hd hx1]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `hl`. Use `⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => ?_⟩` and prove the remaining obligations. Establish `hv` using `h5 x hx γ hγ z hz m hm`. Use `show τ'.character γ = _`. Rewrite using `[← congrFun h γ]`.

Conclude with `hv`.
-/
theorem hasCuspLabel_of_character {K : Type} [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) {d : ℕ}
    {τ τ' : FDRep ℂ (GL (Fin d) K)} (h : τ.character = τ'.character) {P : K[X]} (hl : HasCuspLabel C τ P) :
    HasCuspLabel C τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  refine ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => ?_⟩
  have hv := h5 x hx γ hγ z hz m hm
  show τ'.character γ = _
  rw [← congrFun h γ]
  exact hv

/- English proof (translation)
Introduce `p _ L d hd`. Establish `hd1 : 1 ≤ d` using `hd`. Take `⟨hA, hB, hC⟩` from `(GreenAll.cuspParam_all (K := ZMod p) (conv L)) d hd1`. Use `choose σ hσs hσc hσl using fun P (hP : IsPrimeLab d P) => hB P (isPrimeLab_iff.mp hP).1 (isPrimeLab_iff.mp hP).2.1 (isPrimeLab_iff.mp hP).2.2.1 (isPrimeLab_iff.mp hP).2.2.2`. Set `rep : (ZMod p)[X] → Gn p d → ℂ` to `fun P => if hP : IsPrimeLab d P then (σ P hP).character else 0`.

Use `⟨rep, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Simplify using `only [rep, dif_pos hP]`. Use `⟨isCuspOf_character L hd (σ P hP) P (hσs P hP) (hσc P hP) (hσl P hP), ?_⟩` and prove the remaining obligations. Rewrite using `[FDRep.char_one]`.

Establish `h2` using `congrArg (Int.cast : ℤ → ℂ) (hA _ (hσs P hP) (hσc P hP)).2`. Move the coercions through the operations in `at h2`. Simplify `h2` using `[ZMod.card]`. Introduce `P P' hP hP' heq`. Simplify using `only [rep, dif_pos hP, dif_pos hP'] at heq`.

Establish `hl2 : HasCuspLabel (conv L) (σ P hP) P'` using `hasCuspLabel_of_character (conv L) heq.symm (hσl P' hP')`. Conclude with `(hA _ (hσs P hP) (hσc P hP)).1.unique (hσl P hP) hl2`. Introduce `χ hχ`. Take `⟨V, hVs, hVχ⟩` from `hχ.2.1`. Establish `hχV : V.character = χ` using `funext hVχ`.

Establish `hVc : IsCuspidal (ZMod p) V` using `isCuspidal_of_isCusp V (by rw [hχV]; exact hχ)`. Take `⟨P, hPl, -⟩` from `(hA V hVs hVc).1`. Establish `hP : IsPrimeLab d P` using `isPrimeLab_iff.mpr ⟨hPl.1, hPl.2.1, hPl.2.2.1, by simpa using hPl.2.2.2.1⟩`. Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Simplify using `only [rep, dif_pos hP]`.

Rewrite using `[← hχV]`. Conclude with `FDRep.char_iso (hC V (σ P hP) P hVs hVc (hσs P hP) (hσc P hP) hPl (hσl P hP)).some`.
-/
theorem green : GlobalTheory.GLq.Green := by
  intro p _ L d hd
  classical
  have hd1 : 1 ≤ d := hd
  obtain ⟨hA, hB, hC⟩ := (GreenAll.cuspParam_all (K := ZMod p) (conv L)) d hd1
  choose σ hσs hσc hσl using fun P (hP : IsPrimeLab d P) =>
    hB P (isPrimeLab_iff.mp hP).1 (isPrimeLab_iff.mp hP).2.1 (isPrimeLab_iff.mp hP).2.2.1
      (isPrimeLab_iff.mp hP).2.2.2
  let rep : (ZMod p)[X] → Gn p d → ℂ := fun P =>
    if hP : IsPrimeLab d P then (σ P hP).character else 0
  refine ⟨rep, ?_, ?_, ?_⟩
  · intro P hP
    simp only [rep, dif_pos hP]
    refine ⟨isCuspOf_character L hd (σ P hP) P (hσs P hP) (hσc P hP) (hσl P hP), ?_⟩
    rw [FDRep.char_one]
    have h2 := congrArg (Int.cast : ℤ → ℂ) (hA _ (hσs P hP) (hσc P hP)).2
    push_cast at h2
    simpa [ZMod.card] using h2
  · intro P P' hP hP' heq
    simp only [rep, dif_pos hP, dif_pos hP'] at heq
    have hl2 : HasCuspLabel (conv L) (σ P hP) P' :=
      hasCuspLabel_of_character (conv L) heq.symm (hσl P' hP')
    exact (hA _ (hσs P hP) (hσc P hP)).1.unique (hσl P hP) hl2
  · intro χ hχ
    obtain ⟨V, hVs, hVχ⟩ := hχ.2.1
    have hχV : V.character = χ := funext hVχ
    have hVc : IsCuspidal (ZMod p) V := isCuspidal_of_isCusp V (by rw [hχV]; exact hχ)
    obtain ⟨P, hPl, -⟩ := (hA V hVs hVc).1
    have hP : IsPrimeLab d P :=
      isPrimeLab_iff.mpr ⟨hPl.1, hPl.2.1, hPl.2.2.1, by simpa using hPl.2.2.2.1⟩
    refine ⟨P, hP, ?_⟩
    simp only [rep, dif_pos hP]
    rw [← hχV]
    exact FDRep.char_iso (hC V (σ P hP) P hVs hVc (hσs P hP) (hσc P hP) hPl (hσl P hP)).some

/- English proof (translation)
The claim follows from `green`.
-/
theorem greenCuspidal : GlobalTheory.Published.GreenCuspidal := green

end PositivityTheory.GreenCharacters
