import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorCoeffSuccIndex
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CommPow

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `h` using `hE.1 a b b a`. Simplify using `only [if_true] at h`. Conclude with `eq_add_of_sub_eq' h`.
-/
theorem raising_lowering_mul_comm_add {E : GLOps n K V} (hE : IsGLRep E) (a b : Fin n) :
    E a b * E b a = E b a * E a b + (E a a - E b b) := by
  have h := hE.1 a b b a
  simp only [if_true] at h
  exact eq_add_of_sub_eq' h

/- English proof (translation)
Establish `h1` using `hE.1 a a a b`. Establish `h2` using `hE.1 b b a b`. Simplify using `only [if_true, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2`. Rewrite using `[sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]`. Normalize the expressions using the abelian group laws.
-/
theorem cartan_raising_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E a b = E a b * (E a a - E b b) + (2 : K) • E a b := by
  have h1 := hE.1 a a a b
  have h2 := hE.1 b b a b
  simp only [if_true, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

/- English proof (translation)
Establish `h1` using `hE.1 a a b a`. Establish `h2` using `hE.1 b b b a`. Simplify using `only [if_true, if_neg hab, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2`. Rewrite using `[sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]`. Normalize the expressions using the abelian group laws.
-/
theorem cartan_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E b a = E b a * (E a a - E b b) - (2 : K) • E b a := by
  have h1 := hE.1 a a b a
  have h2 := hE.1 b b b a
  simp only [if_true, if_neg hab, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

/- English proof (translation)
Establish `hw : ∀ c, E c c x = (ν c : K) • x` using `fun c => by`. Establish `h` using `(Submodule.mem_iInf _).1 hx c`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `h`. Rewrite using `[LinearMap.sub_apply, hw a, hw b, sub_smul]`.
-/
theorem cartan_difference_apply_weight (E : GLOps n K V) (a b : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    (E a a - E b b) x = ((ν a : K) - (ν b : K)) • x := by
  have hw : ∀ c, E c c x = (ν c : K) • x := fun c => by
    have h := (Submodule.mem_iInf _).1 hx c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  rw [LinearMap.sub_apply, hw a, hw b, sub_smul]

/- English proof (translation)
Rewrite using `[pf_eq_P, pf_eq_P]`. Conclude with `R1 (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_lowering_commute hE hab) (cartan_difference_apply_weight E a b ν x hx) s T hnil`.
-/
theorem raising_projector_factor_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (x : V) (hx : x ∈ weightSp E ν) :
    E a b (pf E a b s T x) =
      (((s : K) - ((ν a : K) - (ν b : K)) - 1) / ((s : K) + 1)) • pf E a b (s + 1) T (E a b x) := by
  rw [pf_eq_P, pf_eq_P]
  exact R1 (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_lowering_commute hE hab) (cartan_difference_apply_weight E a b ν x hx) s T hnil

/- English proof (translation)
Rewrite using `[pf_eq_P, pf_eq_P]`. Conclude with `sl2_projector_apply_f_eq_smul_f_projector_succ (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_difference_apply_weight E a b ν z hz) s T hnil`.
-/
theorem projector_factor_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (z : V) (hz : z ∈ weightSp E ν) :
    pf E a b s T (E b a z) =
      (((s : K) + 1 - ((ν a : K) - (ν b : K))) / ((s : K) + 1)) • E b a (pf E a b (s + 1) T z) := by
  rw [pf_eq_P, pf_eq_P]
  exact sl2_projector_apply_f_eq_smul_f_projector_succ (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_difference_apply_weight E a b ν z hz) s T hnil

/- English proof (translation)
Establish `hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ → ((E a' b') ^ k) y ∈ weightSp E (μ + k • rootW a' b')`. Introduce `a' b' k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `μ y hy`.

Simplify using `using hy`. Consider the case `succ k ih`. Introduce `μ y hy`. Rewrite using `[pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]`. Conclude with `hs a' b' _ _ (ih μ y hy)`.

Rewrite using `[pf_eq, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`.

Establish `h1` using `hpow b a k _ _ (hpow a b k ν x hx)`. Establish `e : ν + k • rootW a b + k • rootW b a = ν`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, rootW, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem projector_factor_mem_weight_space {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      ((E a' b') ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero =>
      intro μ y hy
      simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]
      exact hs a' b' _ _ (ih μ y hy)
  rw [pf_eq, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [Module.End.mul_apply]
  have h1 := hpow b a k _ _ (hpow a b k ν x hx)
  have e : ν + k • rootW a b + k • rootW b a = ν := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, rootW, Pi.sub_apply, smul_eq_mul]
    ring
  rwa [e] at h1

end

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE a b hab ν s hs T hT x hx`. Establish `hnil` using `restNil K V n E hE a b hab T hT`. Rewrite using `[raising_projector_factor_commute hE hab ν s T hnil x hx]`. Establish `h0 : ((s : K) - ((ν a : K) - (ν b : K)) - 1) = 0`. Establish `h1 : ((s : ℤ) : K) = ((ν a - ν b + 1 : ℤ) : K)` using `by rw [hs]`.

Move the coercions through the operations in `at h1`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0, zero_div, zero_smul]`.
-/
theorem restKill : RestKill := by
  intro K V _ _ _ _ _ n E hE a b hab ν s hs T hT x hx
  have hnil := restNil K V n E hE a b hab T hT
  rw [raising_projector_factor_commute hE hab ν s T hnil x hx]
  have h0 : ((s : K) - ((ν a : K) - (ν b : K)) - 1) = 0 := by
    have h1 : ((s : ℤ) : K) = ((ν a - ν b + 1 : ℤ) : K) := by rw [hs]
    push_cast at h1
    rw [h1]
    ring
  rw [h0, zero_div, zero_smul]

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE a b c hab hac hbc ν s u hsu T hT w hw`. Establish `hsh` using `gl_rep_shifts_weights hE`. Establish `n1` using `restNil K V n E hE a b hab T hT`. Establish `n3` using `restNil K V n E hE a c hac T hT`. Establish `c1` using `fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ab hE hab hac hbc s T n1)`.

Establish `c3` using `fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ac hE hab hac hbc u T n3)`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at c1 c3`. Establish `hz : pf E a c (u + 1) T (E a c w) ∈ weightSp E (ν + rootW a c)` using `projector_factor_mem_weight_space hsh _ a c _ T _ (hsh a c ν w hw)`. Rewrite using `[c1, c3, raising_projector_factor_commute hE hac ν u T n3 w hw, map_sub, map_smul, map_smul, map_smul, projector_factor_lowering_commute hE hab _ s T n1 _ hz]`. Generalize the expression as in `E b a (pf E a b (s + 1) T (pf E a c (u + 1) T (E a c w))) = Y`.

Rewrite using `[smul_smul, smul_smul, sub_add, sub_eq_self, ← sub_smul]`. Establish `hs1 : (s : K) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero s`. Establish `hu1 : (u : K) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero u`. Establish `hK : (u : K) - ((ν a : K) - (ν c : K)) - 1 = (s : K) - ((ν a : K) - (ν b : K))`. Conclude with `congrArg (fun z : ℤ => (z : K)) hsu` after adjusting the coercions.

Establish `ra : (ν + rootW a c) a = ν a + 1` using `by simp [rootW, hac]`. Establish `rb : (ν + rootW a c) b = ν b` using `by simp [rootW, hab.symm, hbc]`. Rewrite using `[ra, rb, hK]`. Use `zero_smul K Y using 2` and compare the differences between its conclusion and the goal. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem restPair : RestPair := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s u hsu T hT w hw
  have hsh := gl_rep_shifts_weights hE
  have n1 := restNil K V n E hE a b hab T hT
  have n3 := restNil K V n E hE a c hac T hT
  have c1 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ab hE hab hac hbc s T n1)
  have c3 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ac hE hab hac hbc u T n3)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at c1 c3
  have hz : pf E a c (u + 1) T (E a c w) ∈ weightSp E (ν + rootW a c) :=
    projector_factor_mem_weight_space hsh _ a c _ T _ (hsh a c ν w hw)
  rw [c1, c3, raising_projector_factor_commute hE hac ν u T n3 w hw, map_sub, map_smul, map_smul, map_smul,
    projector_factor_lowering_commute hE hab _ s T n1 _ hz]
  generalize E b a (pf E a b (s + 1) T (pf E a c (u + 1) T (E a c w))) = Y
  rw [smul_smul, smul_smul, sub_add, sub_eq_self, ← sub_smul]
  have hs1 : (s : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have hu1 : (u : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero u
  have hK : (u : K) - ((ν a : K) - (ν c : K)) - 1 = (s : K) - ((ν a : K) - (ν b : K)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) hsu
  have ra : (ν + rootW a c) a = ν a + 1 := by simp [rootW, hac]
  have rb : (ν + rootW a c) b = ν b := by simp [rootW, hab.symm, hbc]
  rw [ra, rb, hK]
  convert zero_smul K Y using 2
  push_cast
  field_simp
  ring

end Formalism.MainNotions.G.ExtremalProjector
