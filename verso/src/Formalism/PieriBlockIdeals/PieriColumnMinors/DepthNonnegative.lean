import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.PieriBlockIdeals.PieriColumnMinors.UnitNormBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.JointCorollaryFiveBound
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas
import Formalism.RankGapBounds.RankGapProofs.FormsTensorLocalization
import Formalism.PieriBlockIdeals.PieriColumnMinors.RegularCuspidalTrace

noncomputable section

open TensorProduct MvPolynomial

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

/- English proof (translation)
Establish `h1 : ¬ l ∣ m.natAbs` using `fun h => hm (Int.natCast_dvd.mpr h)`. Establish `h2` using `hu _ h1`. Break down `Int.natAbs_eq m with h | h` into its components or cases. Establish `e : (m : R) = ((m.natAbs : ℕ) : R)` using `by conv_lhs => rw [h]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h2`. Establish `e : (m : R) = -((m.natAbs : ℕ) : R)` using `by conv_lhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `h2.neg`.
-/
theorem isUnit_intCast_of_not_dvd' (R : Type) [CommRing R] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : R) := by
  have h1 : ¬ l ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
  have h2 := hu _ h1
  rcases Int.natAbs_eq m with h | h
  · have e : (m : R) = ((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2
  · have e : (m : R) = -((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2.neg

/- English proof (translation)
Rewrite `hx` using `[standardMonomialSpanDomain R r r ν]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨K, sz, hsz, I, hshape, rfl⟩` from `hg`. Establish `hhom` using `ldbasis_bidet_rowHom R sz hsz I`.

Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hhom)]`. Use `split_ifs with hw`. Establish `h1 : bideterminant ℤ sz hsz I ∈ nablaWt r ν μ`. Use `Submodule.mem_inf.2 ⟨hshape ▸ bidetMem ℤ r r K sz hsz I, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_bidet_rowHom ℤ sz hsz I)`. Take `⟨m, hm, h2⟩` from `hE _ h1`. Establish `h3` using `LA.la_map_weyl R le_rfl ν _ h2`. Rewrite `h3` using `[LA.la_map_smul, ldlat_map_bidet]`. Take `⟨u, hu'⟩` from `isUnit_intCast_of_not_dvd' R l hu m hm`.

Establish `h4` using `Submodule.smul_mem _ (↑u⁻¹ : R) h3`. Rewrite `h4` using `[smul_smul]`. Use `h4 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[← hu', ← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul, smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem pow_smul_weighted_component_mem_weyl (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hE : ExpLe l r ν μ e)
    (x : MvPolynomial (Fin r × Fin r) R) (hx : x ∈ dualWeyl R r r ν) :
    (l : R) ^ e • weightedHomogeneousComponent (rowW r r) μ x ∈ weyl R r r le_rfl ν := by
  classical
  rw [standardMonomialSpanDomain R r r ν] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    have hhom := ldbasis_bidet_rowHom R sz hsz I
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hhom)]
    split_ifs with hw
    · have h1 : bideterminant ℤ sz hsz I ∈ nablaWt r ν μ := by
        refine Submodule.mem_inf.2 ⟨hshape ▸ bidetMem ℤ r r K sz hsz I, ?_⟩
        rw [hw]
        exact (mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_bidet_rowHom ℤ sz hsz I)
      obtain ⟨m, hm, h2⟩ := hE _ h1
      have h3 := LA.la_map_weyl R le_rfl ν _ h2
      rw [LA.la_map_smul, ldlat_map_bidet] at h3
      obtain ⟨u, hu'⟩ := isUnit_intCast_of_not_dvd' R l hu m hm
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : R) h3
      rw [smul_smul] at h4
      convert h4 using 2
      push_cast
      rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [smul_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `R _ _ l r ν μ e hu hE x hx`. Conclude with `⟨dualWeylRowGraded R r r ν μ x hx, pow_smul_weighted_component_mem_weyl R l r ν μ e hu hE x hx⟩`.
-/
theorem exponent_le_ring_component_holds : ExpLeRingComp := by
  intro R _ _ l r ν μ e hu hE x hx
  exact ⟨dualWeylRowGraded R r r ν μ x hx, pow_smul_weighted_component_mem_weyl R l r ν μ e hu hE x hx⟩

/- English proof (translation)
Introduce `R _ _ l r ν μ e hu hE x hx`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 hx`. Establish `h3` using `pow_smul_weighted_component_mem_weyl R l r ν μ e hu hE x h1`. Rewrite `h3` using `[weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 h2)]`. Then use the resulting hypothesis.
-/
theorem exponent_le_over_ring_holds : ExpLeRing := by
  intro R _ _ l r ν μ e hu hE x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
  have h3 := pow_smul_weighted_component_mem_weyl R l r ν μ e hu hE x h1
  rwa [weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 h2)] at h3

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[rowW, rowDeg]`. Introduce `b _ hb`. Simplify using `[rowW, Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem weight_rowWeights_eq_rowDeg {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

/- English proof (translation)
Introduce `r c ν μ hν hne`. Take `⟨f, hf, hf0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 hf`. Take `⟨m, hm⟩` from `MvPolynomial.support_nonempty.2 hf0`. Establish `hdom` using `dualWeylDominanceZ r r ν le_rfl hν f h1 m hm`.

Establish `hw : Finsupp.weight (rowW r r) m = μ` using `((mem_weightedHomogeneousSubmodule _ _ _ _).1 h2) (MvPolynomial.mem_support_iff.1 hm)`. Establish `hrd : ∀ a : Fin r, rowDeg m a = μ a` using `fun a => by rw [← hw, weight_rowWeights_eq_rowDeg]`. Establish `hrn : ∀ a : Fin r, rowNu (r` using `r) ν a = ν a := fun a => by simp [rowNu]`. Simplify using `only [hrd, hrn] at hdom`. Use `⟨hdom.2, ?_⟩` and prove the remaining obligations.

Establish `h3` using `hdom.1 c`. Unfold `depth2 res varpi`. Simplify using `only [ite_mul, one_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter, Finset.sum_sub_distrib]`. Establish `h4 : ((∑ a : Fin r with a.val < c, μ a : ℕ) : ℤ) ≤ ((∑ a : Fin r with a.val < c, ν a : ℕ) : ℤ)`.

Conclude with `h3` after adjusting the coercions. Move the coercions through the operations in `at h4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem depth_nonneg_holds : DepthNonneg := by
  intro r c ν μ hν hne
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hf0
  have hdom := dualWeylDominanceZ r r ν le_rfl hν f h1 m hm
  have hw : Finsupp.weight (rowW r r) m = μ :=
    ((mem_weightedHomogeneousSubmodule _ _ _ _).1 h2) (MvPolynomial.mem_support_iff.1 hm)
  have hrd : ∀ a : Fin r, rowDeg m a = μ a := fun a => by rw [← hw, weight_rowWeights_eq_rowDeg]
  have hrn : ∀ a : Fin r, rowNu (r := r) ν a = ν a := fun a => by simp [rowNu]
  simp only [hrd, hrn] at hdom
  refine ⟨hdom.2, ?_⟩
  have h3 := hdom.1 c
  unfold depth2 res varpi
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.sum_sub_distrib]
  have h4 : ((∑ a : Fin r with a.val < c, μ a : ℕ) : ℤ) ≤ ((∑ a : Fin r with a.val < c, ν a : ℕ) : ℤ) := by
    exact_mod_cast h3
  push_cast at h4
  linarith

/- English proof (translation)
Introduce `hD l k j t q h lam xm xp hl ht hanti hconst hspread hh hcloud hlows habove hle htop ecl hecl I μ hμ`. Use `expLeMono l _ _ μ _ _ ?_ (applicationSteps hD l k j t q h lam hl ht hanti hconst hspread ecl hecl I μ hμ)` and prove the remaining obligations. Use `Nat.le_floor ?_` and prove the remaining obligations. Establish `hb : ∀ a : Fin (k + j), lam (k + j) ≤ res (k + j) lam a ∧ res (k + j) lam a ≤ lam 0` using `fun a => ⟨hanti a.val (k + j) (by have := a.isLt; omega) (by omega), hanti 0 a.val (Nat.zero_le _) (by have := a.isLt; omega)⟩`. Establish `eU : ∀ a : Fin (k + j), UN (k + j + t + q) lam a.val = U k j t (res (k + j) lam) a + (q : ℤ)`.

Introduce `a`. Unfold `UN U res`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : UN (k + j + t + q) lam (k + j) = maxB t (lam (k + j)) + (q : ℤ)`.

Unfold `UN maxB`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : Rows k j t (lam (k + j)) (lam 0) (res (k + j) lam) (xm - q) (xp - q)`. Use `⟨fun a => (hb a).1, fun a => (hb a).2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Establish `h1` using `hcloud a.val ha`. Rewrite `h1` using `[eU a]`. Apply the tactic sequence `constructor <;> omega`. Introduce `a ha`.

Establish `h1` using `hlows a.val ha a.isLt`. Rewrite `h1` using `[eU a]`. Use linear arithmetic over natural numbers and integers. Rewrite `habove` using `[e3]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hxp : (xp - q) - maxB t (lam (k + j)) ≤ (h : ℤ)`. Rewrite `htop` using `[e3]`. Use linear arithmetic over natural numbers and integers. Establish `hh1 : 1 ≤ h` using `by omega`.

Establish `hcost : (blockCost l (k + j) t I lam : ℝ) ≤ (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j)))`. Unfold `blockCost`. Take `⟨i, hi, heq⟩` from `Finset.exists_mem_eq_sup (Finset.range (I + 1)) ⟨0, by simp⟩ (fun i => padicValInt l (Dn t (lam 0 - lam (k + j)) i fun b : Fin (k + j) => lam 0 - res (k + j) lam (Fin.rev b)))`. Rewrite using `[heq]`. Conclude with `second_valuation_up_to_holds l k j t (lam (k + j)) (lam 0) h i (I : ℝ) (res (k + j) lam) _ _ hl hR hxp hh (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))`.

Establish `hP : (((h - 1) / (l - 1) : ℕ) : ℝ) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1)`. Establish `h1` using `Nat.cast_div_le (α := ℝ) (m := h - 1) (n := l - 1)`. Establish `hl2` using `hl.two_le`. Rewrite `h1` using `[Nat.cast_sub hh1, Nat.cast_sub (by omega : 1 ≤ l)]`. Simplify using `using h1`.

Establish `hs` using `labelRHSPlus_shift_invariant l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) q`. Rewrite `hs` using `[sub_add_cancel, sub_add_cancel]`. Unfold `cPrime`. Rewrite using `[e3, hs]`. Establish `hq` using `mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))`.

Establish `hj` using `mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem application_window : ApplicationWindow := by
  intro hD l k j t q h lam xm xp hl ht hanti hconst hspread hh hcloud hlows habove hle htop ecl hecl I μ hμ
  refine expLeMono l _ _ μ _ _ ?_
    (applicationSteps hD l k j t q h lam hl ht hanti hconst hspread ecl hecl I μ hμ)
  refine Nat.le_floor ?_
  have hb : ∀ a : Fin (k + j), lam (k + j) ≤ res (k + j) lam a ∧ res (k + j) lam a ≤ lam 0 := fun a =>
    ⟨hanti a.val (k + j) (by have := a.isLt; omega) (by omega),
      hanti 0 a.val (Nat.zero_le _) (by have := a.isLt; omega)⟩
  have eU : ∀ a : Fin (k + j),
      UN (k + j + t + q) lam a.val = U k j t (res (k + j) lam) a + (q : ℤ) := by
    intro a
    unfold UN U res
    push_cast
    ring
  have e3 : UN (k + j + t + q) lam (k + j) = maxB t (lam (k + j)) + (q : ℤ) := by
    unfold UN maxB
    push_cast
    ring
  have hR : Rows k j t (lam (k + j)) (lam 0) (res (k + j) lam) (xm - q) (xp - q) := by
    refine ⟨fun a => (hb a).1, fun a => (hb a).2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h1 := hcloud a.val ha
      rw [eU a] at h1
      constructor <;> omega
    · intro a ha
      have h1 := hlows a.val ha a.isLt
      rw [eU a] at h1
      omega
    · rw [e3] at habove
      omega
    · omega
  have hxp : (xp - q) - maxB t (lam (k + j)) ≤ (h : ℤ) := by
    rw [e3] at htop
    omega
  have hh1 : 1 ≤ h := by omega
  have hcost : (blockCost l (k + j) t I lam : ℝ) ≤ (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) +
      labelSumBoundPos l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) := by
    unfold blockCost
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (I + 1)) ⟨0, by simp⟩
      (fun i => padicValInt l (Dn t (lam 0 - lam (k + j)) i fun b : Fin (k + j) =>
        lam 0 - res (k + j) lam (Fin.rev b)))
    rw [heq]
    exact second_valuation_up_to_holds l k j t (lam (k + j)) (lam 0) h i (I : ℝ) (res (k + j) lam) _ _ hl hR hxp hh
      (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hP : (((h - 1) / (l - 1) : ℕ) : ℝ) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (α := ℝ) (m := h - 1) (n := l - 1)
    have hl2 := hl.two_le
    rw [Nat.cast_sub hh1, Nat.cast_sub (by omega : 1 ≤ l)] at h1
    simpa using h1
  have hs := labelRHSPlus_shift_invariant l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) q
  rw [sub_add_cancel, sub_add_cancel] at hs
  unfold cPrime
  rw [e3, hs]
  have hq := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))
  have hj := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  push_cast
  linarith

section SizeData₂

open Formalism.RankGapBounds.ChebyshevFactorialBounds

/- English proof (translation)
Introduce `ι D τ l hl hτ hP`. Take `⟨hh1, _, _, hD0, _, _, _, _, _, hT⟩` from `hP`. Take `⟨hmB, hlo, hxx, hS, hxh, _⟩` from `hT τ hτ`. Establish `hl0R : (0 : ℝ) < l` using `by exact_mod_cast hl.pos`. Establish `hl1R : (0 : ℝ) < (l : ℝ) - 1`.

Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : (0 : ℝ) ≤ D.k` using `Nat.cast_nonneg _`. Establish `hi : (0 : ℝ) ≤ (D.depth τ l : ℝ)` using `Nat.cast_nonneg _`. Establish `hil : (0 : ℝ) ≤ (D.depth τ l : ℝ) / (l : ℝ)` using `div_nonneg hi hl0R.le`.

Establish `hpeel : ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) - 1) / ((l : ℝ) - 1)) ≤ ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6)`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `h1 : ((D.h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)`. Apply `div_le_div_of_nonneg_right _ hl1R.le` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ (D.Nr : ℝ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : (D.k : ℝ) * (((D.xhi τ - D.xlo τ : ℤ) : ℝ) / (l : ℝ) + D.Icl τ l) ≤ (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)`. Apply `mul_le_mul_of_nonneg_left _ hk` to reduce the goal to its premises. Establish `h1 : ((D.xhi τ - D.xlo τ : ℤ) : ℝ) ≤ (D.S : ℝ)` using `by exact_mod_cast hS`.

Use `div_le_div_of_nonneg_right h1 hl0R.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hH : harm l D.h (D.depth τ l : ℝ) ≤ ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))`. Unfold `harm`. Use `split_ifs`.

Conclude with `mul_nonneg hil (le_max_left _ _)`. Conclude with `mul_le_mul_of_nonneg_left (le_max_right _ _) hil`. Establish `hG : (if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0) = (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) els …` using `rfl`. Unfold `cPrime labelSumBoundPos Cor.coefficientBoundTau`. Rewrite using `[jw_Il_eq, hG]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c_prime_le_weight_correction_holds : CPrimeLeCW5 := by
  intro ι D τ l hl hτ hP
  obtain ⟨hh1, _, _, hD0, _, _, _, _, _, hT⟩ := hP
  obtain ⟨hmB, hlo, hxx, hS, hxh, _⟩ := hT τ hτ
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hk : (0 : ℝ) ≤ D.k := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ (D.depth τ l : ℝ) := Nat.cast_nonneg _
  have hil : (0 : ℝ) ≤ (D.depth τ l : ℝ) / (l : ℝ) := div_nonneg hi hl0R.le
  have hpeel : ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) - 1) / ((l : ℝ) - 1)) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((D.h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hl1R.le
      have : (0 : ℝ) ≤ (D.Nr : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hA : (D.k : ℝ) * (((D.xhi τ - D.xlo τ : ℤ) : ℝ) / (l : ℝ) + D.Icl τ l) ≤
      (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have h1 : ((D.xhi τ - D.xlo τ : ℤ) : ℝ) ≤ (D.S : ℝ) := by exact_mod_cast hS
    have := div_le_div_of_nonneg_right h1 hl0R.le
    linarith
  have hH : harm l D.h (D.depth τ l : ℝ) ≤
      ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) := by
    unfold harm
    split_ifs
    · exact mul_nonneg hil (le_max_left _ _)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hil
  have hG : (if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0) =
      (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := rfl
  unfold cPrime labelSumBoundPos Cor.coefficientBoundTau
  rw [jw_Il_eq, hG]
  linarith

/- English proof (translation)
Introduce `l h i hh hl hi`. Establish `hh0 : (0 : ℝ) < h` using `by exact_mod_cast hh`. Establish `hl0 : (0 : ℝ) < l`. Establish `: (h : ℝ) < l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq0 : (0 : ℝ) < (h : ℝ) / (l : ℝ)` using `div_pos hh0 hl0`. Establish `hq1 : (h : ℝ) / (l : ℝ) < 1`. Rewrite using `[div_lt_one hl0]`. Conclude with `hl` after adjusting the coercions. Establish `hlog : Real.log ((h : ℝ) / (l : ℝ)) < 0` using `Real.log_neg hq0 hq1`.

Establish `hpos : Real.posLog ((h : ℝ) / (l : ℝ)) = 0`. Rewrite using `[Real.posLog_def]`. Conclude with `max_eq_left hlog.le`. Rewrite using `[hpos, add_zero]`. Apply `mul_lt_mul_of_pos_left _ (div_pos hi hl0)` to reduce the goal to its premises.

Rewrite using `[max_lt_iff]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem log_plus_versus_max_holds : LogPlusVsMax := by
  intro l h i hh hl hi
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hl0 : (0 : ℝ) < l := by
    have : (h : ℝ) < l := by exact_mod_cast hl
    linarith
  have hq0 : (0 : ℝ) < (h : ℝ) / (l : ℝ) := div_pos hh0 hl0
  have hq1 : (h : ℝ) / (l : ℝ) < 1 := by
    rw [div_lt_one hl0]
    exact_mod_cast hl
  have hlog : Real.log ((h : ℝ) / (l : ℝ)) < 0 := Real.log_neg hq0 hq1
  have hpos : Real.posLog ((h : ℝ) / (l : ℝ)) = 0 := by
    rw [Real.posLog_def]
    exact max_eq_left hlog.le
  rw [hpos, add_zero]
  apply mul_lt_mul_of_pos_left _ (div_pos hi hl0)
  rw [max_lt_iff]
  constructor <;> linarith

/- English proof (translation)
Establish `hl0R : (0 : ℝ) < l` using `by exact_mod_cast hl.pos`. Establish `hl1R : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (0 : ℝ) ≤ ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6)`.

Establish `: (0 : ℝ) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)` using `div_nonneg (by positivity) hl1R.le`. Check the signs of the components of the expression. Establish `h2 : (0 : ℝ) ≤ (D.ecl τ l : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : (0 : ℝ) ≤ (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)` using `mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (jw_Icl_nonneg D τ l))`. Establish `h4` using `jw_gate_nonneg D τ l`.

Establish `h5 : (0 : ℝ) ≤ ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))` using `mul_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (le_max_left _ _)`. Unfold `Cor.coefficientBoundTau`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coefficientBoundTau_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) (hl : l.Prime) : 0 ≤ Cor.coefficientBoundTau D τ l := by
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have h1 : (0 : ℝ) ≤ ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    have : (0 : ℝ) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := div_nonneg (by positivity) hl1R.le
    positivity
  have h2 : (0 : ℝ) ≤ (D.ecl τ l : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (jw_Icl_nonneg D τ l))
  have h4 := jw_gate_nonneg D τ l
  have h5 : (0 : ℝ) ≤ ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (le_max_left _ _)
  unfold Cor.coefficientBoundTau
  linarith

/- English proof (translation)
Unfold `cTau`. Use `split_ifs with hτ`. Rewrite using `[Nat.cast_min]`. Apply `min_le_min le_rfl` to reduce the goal to its premises. Distinguish the cases in `h0 : 0 ≤ cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ) (D.depth τ l : ℝ)`.

Conclude with `(Nat.floor_le h0).trans (c_prime_le_weight_correction_holds ι D τ l hl hτ hP)`. Use `show ((⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ) (D.depth τ l : ℝ)⌋₊ : ℕ) : ℝ) ≤ _`. Rewrite using `[Nat.floor_of_nonpos (not_le.1 h0).le]`. Simplify using `using coefficientBoundTau_nonneg D τ l hl`. Conclude with `le_rfl`.
-/
theorem tau_term_le_correction_bound {ι : Type} [DecidableEq ι] (D : Data ι) (hP : D.Params) (l : ℕ) (hl : l.Prime) (τ : ι) :
    ((cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) ≤
      (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ)) := by
  unfold cTau
  split_ifs with hτ
  · rw [Nat.cast_min]
    apply min_le_min le_rfl
    by_cases h0 : 0 ≤ cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
        (D.depth τ l : ℝ)
    · exact (Nat.floor_le h0).trans (c_prime_le_weight_correction_holds ι D τ l hl hτ hP)
    · show ((⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊ : ℕ) : ℝ) ≤ _
      rw [Nat.floor_of_nonpos (not_le.1 h0).le]
      simpa using coefficientBoundTau_nonneg D τ l hl
  · exact le_rfl

/- English proof (translation)
Introduce `ι _ _ D hP h l hl hE hlJ h2 h3 h4`. Establish `h5` using `h l hl hE hlJ h2 h3 h4`. Establish `h6 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l) (fun τ => ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ) (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ)` using `by exact_mod_cast h5`. Use `h6.trans ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sum]`.

Conclude with `Finset.sum_le_sum fun τ _ => tau_term_le_correction_bound D hP l hl τ`.
-/
theorem sizeData_joint : JointEstimate := by
  intro ι _ _ D hP h l hl hE hlJ h2 h3 h4
  have h5 := h l hl hE hlJ h2 h3 h4
  have h6 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) := by exact_mod_cast h5
  refine h6.trans ?_
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum fun τ _ => tau_term_le_correction_bound D hP l hl τ

end SizeData₂

section Subquotients

open CategoryTheory CategoryTheory.Limits

/- English proof (translation)
Introduce `A _ V G G' _ _ _ _ _ _ ⟨e⟩ ⟨E, ψ, hψ⟩`. Conclude with `⟨E, e.toLinearMap ∘ₗ ψ, e.surjective.comp hψ⟩`.
-/
theorem subquotient_iso_holds : SubquotIso := by
  intro A _ V G G' _ _ _ _ _ _ ⟨e⟩ ⟨E, ψ, hψ⟩
  exact ⟨E, e.toLinearMap ∘ₗ ψ, e.surjective.comp hψ⟩

/- English proof (translation)
Introduce `R _ P X P' _ _ _ _ _ _ p l c h z`. Establish `h1 : ∀ y : X ⊗[R] P', l ^ c • TensorProduct.map p (LinearMap.id : P' →ₗ[R] P') y = 0`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x b => rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', h x, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`.

Rewrite using `[TensorProduct.map_tmul, ← TensorProduct.tmul_smul, h1 y, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]`.
-/
theorem tensor_projection_kill_holds : TensorProjKill := by
  intro R _ P X P' _ _ _ _ _ _ p l c h z
  have h1 : ∀ y : X ⊗[R] P', l ^ c • TensorProduct.map p (LinearMap.id : P' →ₗ[R] P') y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', h x, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [TensorProduct.map_tmul, ← TensorProduct.tmul_smul, h1 y, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

def mulOntoScaledSubmodule {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : V →ₗ[A] scaleSub A V c where
  toFun v := ⟨c • v, v, rfl⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' b x := Subtype.ext (smul_comm c b x)

/- English proof (translation)
Introduce `O _ A _ _ V _ _ _ _ ϖ a`. Establish `hker : scaleSub A V ϖ ≤ LinearMap.ker (((scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype).mkQ ∘ₗ mulOntoScaledSubmodule A V (ϖ ^ a))`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `⟨y, by show ϖ ^ a • ϖ • y = ϖ ^ (a + 1) • y`.

Rewrite using `[pow_succ, mul_smul]⟩`. Use `⟨(scaleSub A V ϖ).liftQ _ hker, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Both sides reduce to the same expression. Introduce `z`.

Take `⟨⟨x, y, rfl⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩`. Introduce `hreg`. Establish `hpow : ∀ (b : ℕ) (v : V), ϖ ^ b • v = 0 → v = 0`. Introduce `b`.

Proceed by induction on `b with`. Consider the case `zero => intro v hv`. Simplify using `using hv`. Consider the case `succ b ih`. Introduce `v hv`.

Rewrite `hv` using `[pow_succ, mul_smul]`. Conclude with `hreg v (ih _ hv)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Establish `h1 : (Submodule.Quotient.mk (⟨ϖ ^ a • v, v, rfl⟩ : scaleSub A V (ϖ ^ a)) : scaleSub A V (ϖ ^ a) ⧸ (scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype) = 0` using `hz`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Take `⟨y, hy⟩` from `h1`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Establish `h2 : ϖ ^ a • (v - ϖ • y) = 0`. Establish `h3 : ϖ ^ a • v = ϖ ^ (a + 1) • y` using `hy`. Rewrite using `[smul_sub, h3, pow_succ, mul_smul, sub_self]`. Conclude with `sub_eq_zero.mp (hpow a _ h2)`.
-/
theorem power_quotient_holds : PowQuotient := by
  intro O _ A _ _ V _ _ _ _ ϖ a
  have hker : scaleSub A V ϖ ≤ LinearMap.ker
      (((scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype).mkQ ∘ₗ
        mulOntoScaledSubmodule A V (ϖ ^ a)) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    exact ⟨y, by
      show ϖ ^ a • ϖ • y = ϖ ^ (a + 1) • y
      rw [pow_succ, mul_smul]⟩
  refine ⟨(scaleSub A V ϖ).liftQ _ hker, ?_, ?_, ?_⟩
  · intro v
    rfl
  · intro z
    obtain ⟨⟨x, y, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro hreg
    have hpow : ∀ (b : ℕ) (v : V), ϖ ^ b • v = 0 → v = 0 := by
      intro b
      induction b with
      | zero => intro v hv; simpa using hv
      | succ b ih =>
        intro v hv
        rw [pow_succ, mul_smul] at hv
        exact hreg v (ih _ hv)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have h1 : (Submodule.Quotient.mk (⟨ϖ ^ a • v, v, rfl⟩ : scaleSub A V (ϖ ^ a)) :
        scaleSub A V (ϖ ^ a) ⧸ (scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype) = 0 := hz
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
    obtain ⟨y, hy⟩ := h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨y, ?_⟩
    have h2 : ϖ ^ a • (v - ϖ • y) = 0 := by
      have h3 : ϖ ^ a • v = ϖ ^ (a + 1) • y := hy
      rw [smul_sub, h3, pow_succ, mul_smul, sub_self]
    exact sub_eq_zero.mp (hpow a _ h2)

/- English proof (translation)
Introduce `O _ A _ _ V _ _ _ _ ϖ n F F' hFF hn hsimple`. Establish `hcov : F ⋖ F'` using `(covBy_iff_quot_is_simple hFF).mpr hsimple`. Use `set Fa : ℕ → Submodule A V := fun a => F ⊔ (F' ⊓ scaleSub A V (ϖ ^ a)) with hFa`. Establish `hle : ∀ a, F ≤ Fa a` using `fun a => le_sup_left`. Establish `hle' : ∀ a, Fa a ≤ F'` using `fun a => sup_le hFF inf_le_left`.

Establish `h0 : Fa 0 = F'`. Apply `le_antisymm (hle' 0)` to reduce the goal to its premises. Introduce `x hx`. Conclude with `Submodule.mem_sup_right ⟨hx, x, by simp⟩`. Establish `hnF : Fa n = F` using `le_antisymm (sup_le le_rfl (inf_le_right.trans hn)) (hle n)`.

Establish `hex : ∃ a, Fa a = F` using `⟨n, hnF⟩`. Establish `ha1` using `Nat.find_spec hex`. Establish `hne : Nat.find hex ≠ 0`. Introduce `h`. Rewrite `ha1` using `[h, h0]`.

Conclude with `hcov.ne ha1.symm`. Take `⟨a, ha⟩` from `Nat.exists_eq_succ_of_ne_zero hne`. Establish `haF' : Fa a = F'`. Break down `hcov.eq_or_eq (hle a) (hle' a) with h | h` into its components or cases. Conclude with `absurd h (Nat.find_min hex (by omega))`.

Conclude with `h`. Establish `haF : Fa (a + 1) = F` using `by rw [← Nat.succ_eq_add_one, ← ha]; exact ha1`. Set `m : V →ₗ[A] V` to `(scaleSub A V (ϖ ^ a)).subtype ∘ₗ mulOntoScaledSubmodule A V (ϖ ^ a)`. Establish `hm : ∀ v, m v = ϖ ^ a • v` using `fun v => rfl`. Set `E0 : Submodule A V` to `F'.comap m`.

Set `ψ0 : E0 →ₗ[A] (F' ⧸ F.comap F'.subtype)` to `(F.comap F'.subtype).mkQ ∘ₗ m.restrict (p := E0) (q := F') (fun x hx => hx)`. Establish `hψ0 : Function.Surjective ψ0`. Introduce `z`. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hz' : z ∈ Fa a` using `haF'.symm ▸ hz`.

Take `⟨u, hu, v, ⟨hv, y, rfl⟩, rfl⟩` from `Submodule.mem_sup.mp hz'`. Use `⟨⟨y, hv⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap]`. Establish `: (ϖ ^ a • y) - (u + ϖ ^ a • y) = -u` using `by abel`.

Use `show (ϖ ^ a • y) - (u + ϖ ^ a • y) ∈ F`. Rewrite using `[this]`. Conclude with `F.neg_mem hu`. Set `π : E0 →ₗ[A] E0.map (scaleSub A V ϖ).mkQ` to `((scaleSub A V ϖ).mkQ).restrict (p := E0) (q := E0.map (scaleSub A V ϖ).mkQ) (fun x hx => Submodule.mem_map_of_mem hx)`. Establish `hπ : Function.Surjective π`.

Introduce and unpack `⟨_, x, hx, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hker : LinearMap.ker π ≤ LinearMap.ker ψ0`. Introduce and unpack `⟨x, hx⟩ hxk`. Rewrite `hxk`, the goal using `[LinearMap.mem_ker]`.

Establish `h1 : (scaleSub A V ϖ).mkQ x = 0` using `congrArg Subtype.val hxk`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, rfl⟩` from `h1`. Use `show Submodule.Quotient.mk _ = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Use `show ϖ ^ a • ϖ • y ∈ F`. Rewrite using `[← haF]`. Use `Submodule.mem_sup_right ⟨hx, y, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, mul_smul]`. Use `⟨E0.map (scaleSub A V ϖ).mkQ, (LinearMap.ker π).liftQ ψ0 hker ∘ₗ (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, ?_⟩` and prove the remaining obligations.

Introduce `z`. Take `⟨x, rfl⟩` from `hψ0 z`. Use `⟨LinearMap.quotKerEquivOfSurjective π hπ (Submodule.Quotient.mk x), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem simple_subquotient_of_power_holds : SimpleSubquotOfPower := by
  intro O _ A _ _ V _ _ _ _ ϖ n F F' hFF hn hsimple
  classical
  have hcov : F ⋖ F' := (covBy_iff_quot_is_simple hFF).mpr hsimple
  set Fa : ℕ → Submodule A V := fun a => F ⊔ (F' ⊓ scaleSub A V (ϖ ^ a)) with hFa
  have hle : ∀ a, F ≤ Fa a := fun a => le_sup_left
  have hle' : ∀ a, Fa a ≤ F' := fun a => sup_le hFF inf_le_left
  have h0 : Fa 0 = F' := by
    apply le_antisymm (hle' 0)
    intro x hx
    exact Submodule.mem_sup_right ⟨hx, x, by simp⟩
  have hnF : Fa n = F := le_antisymm (sup_le le_rfl (inf_le_right.trans hn)) (hle n)
  have hex : ∃ a, Fa a = F := ⟨n, hnF⟩
  have ha1 := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, h0] at ha1
    exact hcov.ne ha1.symm
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have haF' : Fa a = F' := by
    rcases hcov.eq_or_eq (hle a) (hle' a) with h | h
    · exact absurd h (Nat.find_min hex (by omega))
    · exact h
  have haF : Fa (a + 1) = F := by rw [← Nat.succ_eq_add_one, ← ha]; exact ha1

  let m : V →ₗ[A] V := (scaleSub A V (ϖ ^ a)).subtype ∘ₗ mulOntoScaledSubmodule A V (ϖ ^ a)
  have hm : ∀ v, m v = ϖ ^ a • v := fun v => rfl
  let E0 : Submodule A V := F'.comap m
  let ψ0 : E0 →ₗ[A] (F' ⧸ F.comap F'.subtype) :=
    (F.comap F'.subtype).mkQ ∘ₗ m.restrict (p := E0) (q := F') (fun x hx => hx)
  have hψ0 : Function.Surjective ψ0 := by
    intro z
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz' : z ∈ Fa a := haF'.symm ▸ hz
    obtain ⟨u, hu, v, ⟨hv, y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz'
    refine ⟨⟨y, hv⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have : (ϖ ^ a • y) - (u + ϖ ^ a • y) = -u := by abel
    show (ϖ ^ a • y) - (u + ϖ ^ a • y) ∈ F
    rw [this]
    exact F.neg_mem hu
  let π : E0 →ₗ[A] E0.map (scaleSub A V ϖ).mkQ :=
    ((scaleSub A V ϖ).mkQ).restrict (p := E0) (q := E0.map (scaleSub A V ϖ).mkQ)
      (fun x hx => Submodule.mem_map_of_mem hx)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker ψ0 := by
    rintro ⟨x, hx⟩ hxk
    rw [LinearMap.mem_ker] at hxk ⊢
    have h1 : (scaleSub A V ϖ).mkQ x = 0 := congrArg Subtype.val hxk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨y, rfl⟩ := h1
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show ϖ ^ a • ϖ • y ∈ F
    rw [← haF]
    refine Submodule.mem_sup_right ⟨hx, y, ?_⟩
    rw [pow_succ, mul_smul]
  refine ⟨E0.map (scaleSub A V ϖ).mkQ,
    (LinearMap.ker π).liftQ ψ0 hker ∘ₗ (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := hψ0 z
  refine ⟨LinearMap.quotKerEquivOfSurjective π hπ (Submodule.Quotient.mk x), ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Introduce `C D _ _ _ _ F _ _ _ P P' hP Y hY`. Proceed by induction on `hY with`. Consider the case `zero Y h => exact Filtered.zero _ (F.map_isZero h)`. Consider the case `step S hS _ h3 ih => exact Filtered.step (S.map F) (hS.map_of_exact F) ih (hP _ h3)`.
-/
theorem filtered_map_holds : FilteredMap := by
  intro C D _ _ _ _ F _ _ _ P P' hP Y hY
  induction hY with
  | zero Y h => exact Filtered.zero _ (F.map_isZero h)
  | step S hS _ h3 ih => exact Filtered.step (S.map F) (hS.map_of_exact F) ih (hP _ h3)

/- English proof (translation)
Consider the cases of `h with`. Consider the case `zero _ h => intro Y' e`. Conclude with `Filtered.zero _ (h.of_iso e.symm)`. Consider the case `step S hS h1 h3`. Introduce `Y' e`.

Establish `w : (S.f ≫ e.hom) ≫ (e.inv ≫ S.g) = 0` using `by simp`. Establish `hiso : S ≅ ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w` using `ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp) (by simp)`. Conclude with `Filtered.step (ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w) (ShortComplex.shortExact_of_iso hiso hS) h1 h3`.
-/
theorem filtered_of_iso {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Y : C}
    (h : Filtered P Y) : ∀ {Y' : C} (_ : Y ≅ Y'), Filtered P Y' := by
  cases h with
  | zero _ h => intro Y' e; exact Filtered.zero _ (h.of_iso e.symm)
  | step S hS h1 h3 =>
    intro Y' e
    have w : (S.f ≫ e.hom) ≫ (e.inv ≫ S.g) = 0 := by simp
    have hiso : S ≅ ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w :=
      ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp) (by simp)
    exact Filtered.step (ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w)
      (ShortComplex.shortExact_of_iso hiso hS) h1 h3

/- English proof (translation)
Proceed by induction on `hZ with`. Consider the case `zero Z h0`. Introduce `X Y f g w hS hX`. Establish `hm : Mono f` using `hS.mono_f`. Establish `he : Epi f` using `hS.exact.epi_f (h0.eq_of_tgt _ _)`.

Establish `: IsIso f` using `isIso_of_mono_of_epi f`. Conclude with `filtered_of_iso hX (asIso f)`. Consider the case `step S' hS' _ h3 ih`. Introduce `X Y f g w hS hX`. Establish `hmf : Mono f` using `hS.mono_f`.

Establish `heg : Epi g` using `hS.epi_g`. Establish `hmu : Mono S'.f` using `hS'.mono_f`. Establish `hev : Epi S'.g` using `hS'.epi_g`. Set `ι : kernel (g ≫ S'.g) ⟶ Y` to `kernel.ι (g ≫ S'.g)`. Establish `hι : ι ≫ g ≫ S'.g = 0` using `kernel.condition _`.

Establish `htop : (ShortComplex.mk ι (g ≫ S'.g) hι).ShortExact` using `{ exact := ShortComplex.exact_kernel _ mono_f := by dsimp; infer_instance epi_g := by dsimp; infer_instance }`. Use `Filtered.step (ShortComplex.mk ι (g ≫ S'.g) hι) htop ?_ h3` and prove the remaining obligations. Set `f' : X ⟶ kernel (g ≫ S'.g)` to `kernel.lift (g ≫ S'.g) f (by rw [← Category.assoc, w, zero_comp])`. Establish `hf' : f' ≫ ι = f` using `kernel.lift_ι _ _ _`. Set `g' : kernel (g ≫ S'.g) ⟶ S'.X₁` to `hS'.exact.lift (ι ≫ g) (by rw [Category.assoc]; exact hι)`.

Establish `hg' : g' ≫ S'.f = ι ≫ g` using `hS'.exact.lift_f _ _`. Establish `w' : f' ≫ g' = 0`. Rewrite using `[← cancel_mono S'.f, Category.assoc, hg', ← Category.assoc, hf', w, zero_comp]`. Use `ih f' g' w' ?_ hX` and prove the remaining obligations. Use `{ exact := ?_, mono_f := ?_, epi_g := ?_ }` and prove the remaining obligations.

Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`. Introduce `A x₂ hx₂`. Simplify using `at x₂ hx₂`. Establish `h1 : (x₂ ≫ ι) ≫ g = 0`. Rewrite using `[Category.assoc, ← hg', ← Category.assoc, hx₂, zero_comp]`.

Take `⟨A', π, hπ, x₁, hx₁⟩` from `hS.exact.exact_up_to_refinements (x₂ ≫ ι) h1`. Simplify using `at x₁ hx₁`. Use `⟨A', π, hπ, x₁, ?_⟩` and prove the remaining obligations. Use `dsimp`. Rewrite using `[← cancel_mono ι, Category.assoc, Category.assoc, hf', hx₁]`.

Use `dsimp`. Conclude with `mono_of_mono_fac hf'`. Use `dsimp`. Rewrite using `[epi_iff_surjective_up_to_refinements]`. Introduce `A y`.

Take `⟨A', π, hπ, x₀, hx₀⟩` from `surjective_up_to_refinements_of_epi g (y ≫ S'.f)`. Establish `h2 : x₀ ≫ g ≫ S'.g = 0`. Rewrite using `[← Category.assoc, ← hx₀, Category.assoc, Category.assoc, S'.zero, comp_zero, comp_zero]`. Use `⟨A', π, hπ, kernel.lift (g ≫ S'.g) x₀ h2, ?_⟩` and prove the remaining obligations. Establish `h3' : kernel.lift (g ≫ S'.g) x₀ h2 ≫ ι = x₀` using `kernel.lift_ι _ _ _`.

Apply `(cancel_mono S'.f).mp` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem filtered_middle_of_short_exact {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Z : C}
    (hZ : Filtered P Z) : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact → Filtered P X → Filtered P Y := by
  induction hZ with
  | zero Z h0 =>
    intro X Y f g w hS hX
    have hm : Mono f := hS.mono_f
    have he : Epi f := hS.exact.epi_f (h0.eq_of_tgt _ _)
    have : IsIso f := isIso_of_mono_of_epi f
    exact filtered_of_iso hX (asIso f)
  | step S' hS' _ h3 ih =>
    intro X Y f g w hS hX
    have hmf : Mono f := hS.mono_f
    have heg : Epi g := hS.epi_g
    have hmu : Mono S'.f := hS'.mono_f
    have hev : Epi S'.g := hS'.epi_g

    let ι : kernel (g ≫ S'.g) ⟶ Y := kernel.ι (g ≫ S'.g)
    have hι : ι ≫ g ≫ S'.g = 0 := kernel.condition _
    have htop : (ShortComplex.mk ι (g ≫ S'.g) hι).ShortExact :=
      { exact := ShortComplex.exact_kernel _
        mono_f := by dsimp; infer_instance
        epi_g := by dsimp; infer_instance }
    refine Filtered.step (ShortComplex.mk ι (g ≫ S'.g) hι) htop ?_ h3
    let f' : X ⟶ kernel (g ≫ S'.g) := kernel.lift (g ≫ S'.g) f (by rw [← Category.assoc, w, zero_comp])
    have hf' : f' ≫ ι = f := kernel.lift_ι _ _ _
    let g' : kernel (g ≫ S'.g) ⟶ S'.X₁ := hS'.exact.lift (ι ≫ g) (by rw [Category.assoc]; exact hι)
    have hg' : g' ≫ S'.f = ι ≫ g := hS'.exact.lift_f _ _
    have w' : f' ≫ g' = 0 := by
      rw [← cancel_mono S'.f, Category.assoc, hg', ← Category.assoc, hf', w, zero_comp]
    refine ih f' g' w' ?_ hX
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      dsimp at x₂ hx₂
      have h1 : (x₂ ≫ ι) ≫ g = 0 := by
        rw [Category.assoc, ← hg', ← Category.assoc, hx₂, zero_comp]
      obtain ⟨A', π, hπ, x₁, hx₁⟩ := hS.exact.exact_up_to_refinements (x₂ ≫ ι) h1
      dsimp at x₁ hx₁
      refine ⟨A', π, hπ, x₁, ?_⟩
      dsimp
      rw [← cancel_mono ι, Category.assoc, Category.assoc, hf', hx₁]
    · dsimp
      exact mono_of_mono_fac hf'
    · dsimp
      rw [epi_iff_surjective_up_to_refinements]
      intro A y
      obtain ⟨A', π, hπ, x₀, hx₀⟩ := surjective_up_to_refinements_of_epi g (y ≫ S'.f)
      have h2 : x₀ ≫ g ≫ S'.g = 0 := by
        rw [← Category.assoc, ← hx₀, Category.assoc, Category.assoc, S'.zero, comp_zero, comp_zero]
      refine ⟨A', π, hπ, kernel.lift (g ≫ S'.g) x₀ h2, ?_⟩
      have h3' : kernel.lift (g ≫ S'.g) x₀ h2 ≫ ι = x₀ := kernel.lift_ι _ _ _
      apply (cancel_mono S'.f).mp
      calc (π ≫ y) ≫ S'.f = π ≫ y ≫ S'.f := Category.assoc _ _ _
        _ = x₀ ≫ g := hx₀
        _ = (kernel.lift (g ≫ S'.g) x₀ h2 ≫ ι) ≫ g := by rw [h3']
        _ = kernel.lift (g ≫ S'.g) x₀ h2 ≫ g' ≫ S'.f := by rw [Category.assoc, hg']
        _ = (kernel.lift (g ≫ S'.g) x₀ h2 ≫ g') ≫ S'.f := (Category.assoc _ _ _).symm

/- English proof (translation)
Introduce `C _ _ P S hS h1 h3`. Conclude with `filtered_middle_of_short_exact h3 S.f S.g S.zero hS h1`.
-/
theorem filtered_extension_holds : FilteredExt := by
  intro C _ _ P S hS h1 h3
  exact filtered_middle_of_short_exact h3 S.f S.g S.zero hS h1

/- English proof (translation)
Introduce `C _ _ P Y hY`. Proceed by induction on `hY with`. Consider the case `zero Y h => exact Filtered.zero _ h`. Consider the case `step S hS _ h3 ih => exact filtered_extension_holds C P S hS ih h3`.
-/
theorem filtered_transitive_holds : FilteredTrans := by
  intro C _ _ P Y hY
  induction hY with
  | zero Y h => exact Filtered.zero _ h
  | step S hS _ h3 ih => exact filtered_extension_holds C P S hS ih h3

/- English proof (translation)
Introduce `C D _ _ _ _ F _ _ _ P P' hP Y hY`. Proceed by induction on `hY with`. Consider the case `zero Y h => exact Filtered.zero _ (F.map_isZero h)`. Consider the case `step S hS _ h3 ih => exact filtered_extension_holds D P' (S.map F) (hS.map_of_exact F) ih (hP _ h3)`.
-/
theorem filtered_map_filtered_holds : FilteredMapFiltered := by
  intro C D _ _ _ _ F _ _ _ P P' hP Y hY
  induction hY with
  | zero Y h => exact Filtered.zero _ (F.map_isZero h)
  | step S hS _ h3 ih => exact filtered_extension_holds D P' (S.map F) (hS.map_of_exact F) ih (hP _ h3)

end Subquotients

/- English proof (translation)
Introduce `O _ ι _ _ Nb _ _ τ p x`. Unfold `atFactor`. Rewrite using `[PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `σ`.

Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem factor_action_on_tensor_product_holds : AtFactorTprod := by
  intro O _ ι _ _ Nb _ _ τ p x
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Use `⟨PiTensorProduct.tprod O (fun τ => (⟨x τ, hx τ⟩ : B τ)), ?_⟩` and prove the remaining obligations. Rewrite using `[PiTensorProduct.map_tprod]`. Both sides reduce to the same expression.
-/
theorem tprod_mem_tensorSubmodule {O : Type} [CommRing O] {ι : Type} [Fintype ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (x : ∀ τ, Nb τ)
    (hx : ∀ τ, x τ ∈ B τ) : PiTensorProduct.tprod O x ∈ tensSub B := by
  refine ⟨PiTensorProduct.tprod O (fun τ => (⟨x τ, hx τ⟩ : B τ)), ?_⟩
  rw [PiTensorProduct.map_tprod]
  rfl

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r u`. Rewrite using `[map_smul, PiTensorProduct.map_tprod]`. Conclude with `U.smul_mem _ (h _ fun τ => (u τ).2)`.

Consider the case `add a b ha hb`. Rewrite using `[map_add]`. Conclude with `U.add_mem ha hb`.
-/
theorem tensorSubmodule_le_of_tprod_mem {O : Type} [CommRing O] {ι : Type} [Fintype ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ))
    (U : Submodule O (⨂[O] τ, Nb τ))
    (h : ∀ x : ∀ τ, Nb τ, (∀ τ, x τ ∈ B τ) → PiTensorProduct.tprod O x ∈ U) : tensSub B ≤ U := by
  rintro _ ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact U.smul_mem _ (h _ fun τ => (u τ).2)
  | add a b ha hb =>
    rw [map_add]
    exact U.add_mem ha hb

/- English proof (translation)
Introduce `O _ ι _ _ Nb _ _ B s a p l c ha hp`. Establish `key : tensSub (chainB B (insert a s)) ≤ (tensSub (chainB B s)).comap ((l ^ c) • atFactor a p)`. Apply `tensorSubmodule_le_of_tprod_mem` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[Submodule.mem_comap, LinearMap.smul_apply, factor_action_on_tensor_product_holds, ← MultilinearMap.map_update_smul]`.

Apply the tactic sequence `try rw [Function.update_idem]`. Apply `tprod_mem_tensorSubmodule` to reduce the goal to its premises. Introduce `τ`. Distinguish the cases in `h : τ = a`. Substitute `h` using the available equality.

Simplify using `only [Function.update_self, chainB, if_neg ha]`. Conclude with `hp _`. Rewrite using `[Function.update_of_ne h]`. Establish `h1` using `hx τ`. Simplify using `only [chainB, Finset.mem_insert, h, false_or] at h1 ⊢`.

Conclude with `h1`. Introduce `y hy`. Conclude with `key hy`.
-/
theorem tensor_weight_kill_holds : TensorWeightKill := by
  intro O _ ι _ _ Nb _ _ B s a p l c ha hp
  have key : tensSub (chainB B (insert a s)) ≤
      (tensSub (chainB B s)).comap ((l ^ c) • atFactor a p) := by
    apply tensorSubmodule_le_of_tprod_mem
    intro x hx
    rw [Submodule.mem_comap, LinearMap.smul_apply, factor_action_on_tensor_product_holds,
      ← MultilinearMap.map_update_smul]
    try rw [Function.update_idem]
    apply tprod_mem_tensorSubmodule
    intro τ
    by_cases h : τ = a
    · subst h
      simp only [Function.update_self, chainB, if_neg ha]
      exact hp _
    · rw [Function.update_of_ne h]
      have h1 := hx τ
      simp only [chainB, Finset.mem_insert, h, false_or] at h1 ⊢
      exact h1
  intro y hy
  exact key hy

/- English proof (translation)
Introduce `O _ ι _ _ Nb _ _ B s s' hss`. Apply `tensorSubmodule_le_of_tprod_mem` to reduce the goal to its premises. Introduce `x hx`. Apply `tprod_mem_tensorSubmodule` to reduce the goal to its premises. Introduce `τ`.

Establish `h1` using `hx τ`. Simplify using `only [chainB] at h1 ⊢`. Distinguish the cases in `h : τ ∈ s`. Rewrite using `[if_pos (hss h)]`. Discharge the goal by the elementary cases of `trivial`.

Rewrite `h1`, `split_ifs` using `[if_neg h]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `h1`.
-/
theorem chain_monotone_holds : ChainMono := by
  intro O _ ι _ _ Nb _ _ B s s' hss
  apply tensorSubmodule_le_of_tprod_mem
  intro x hx
  apply tprod_mem_tensorSubmodule
  intro τ
  have h1 := hx τ
  simp only [chainB] at h1 ⊢
  by_cases h : τ ∈ s
  · rw [if_pos (hss h)]
    trivial
  · rw [if_neg h] at h1
    split_ifs
    · trivial
    · exact h1

/- English proof (translation)
Introduce `O _ ι _ _ Nb _ _ B`. Prove the components needed by the constructor for the conclusion. Establish `h0 : chainB B ∅ = B`. Use function extensionality and compare the values at `τ`. Simplify using `[chainB]`.

Rewrite using `[h0]`. Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Apply `tprod_mem_tensorSubmodule` to reduce the goal to its premises. Introduce `τ`.

Simplify using `[chainB]`.
-/
theorem chain_ends_holds : ChainEnds := by
  intro O _ ι _ _ Nb _ _ B
  constructor
  · have h0 : chainB B ∅ = B := by
      funext τ
      simp [chainB]
    rw [h0]
  · rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    apply tprod_mem_tensorSubmodule
    intro τ
    simp [chainB]

/- English proof (translation)
Introduce `O _ A _ _ G _ K jK W _ _ _ _ κ w`. Both sides reduce to the same expression.
-/
theorem representation_of_apply_holds : RepOfApply := by
  intro O _ A _ _ G _ K jK W _ _ _ _ κ w
  rfl

/- English proof (translation)
Unfold `atFactor`. Rewrite using `[Function.update_eq_self a (fun τ => (LinearMap.id : Nb τ →ₗ[O] Nb τ)), PiTensorProduct.map_id]`. Both sides reduce to the same expression.
-/
theorem factorAction_id {O : Type} [CommRing O] {ι : Type} [Fintype ι] [DecidableEq ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (a : ι) (y : ⨂[O] τ, Nb τ) :
    atFactor a (LinearMap.id : Nb a →ₗ[O] Nb a) y = y := by
  unfold atFactor
  rw [Function.update_eq_self a (fun τ => (LinearMap.id : Nb τ →ₗ[O] Nb τ)), PiTensorProduct.map_id]
  rfl

/- English proof (translation)
Introduce `O _ A _ _ G _ Γ K jK T _ V W _ _ _ _ _ _ _ _ _ _ S F F' ψ hst hnat hker hsub f hf`. Establish `hmem : (fun g => ψ ⟨(f : G → V) g, hf g⟩) ∈ Forms O Γ jK W`. Introduce `γ g κ`. Establish `h1 : (⟨(f : G → V) ((γ : G) * g * κ), hf _⟩ : F') = jK κ⁻¹ • ⟨(f : G → V) g, hf g⟩` using `Subtype.ext (f.2 γ g κ)`. Use `show ψ _ = jK κ⁻¹ • ψ _`.

Rewrite using `[h1, map_smul]`. Set `φ : Forms O Γ jK W` to `⟨_, hmem⟩`. Establish `h0 : LocalizedModule.mk φ (1 : S) = LocalizedModule.mk 0 (1 : S)` using `Subsingleton.elim _ _`. Take `⟨u, hu⟩` from `LocalizedModule.mk_eq.mp h0`. Establish `hu' : (u : T) • φ = 0`.

Simplify `hu` using `[Submonoid.smul_def]`. Use `⟨u, u.2, fun g => ?_⟩` and prove the remaining obligations. Apply `hker ⟨_, hst F' u f hf g⟩` to reduce the goal to its premises. Rewrite using `[← hnat F' ψ u f φ hf (hst F' u f hf) (fun _ => rfl) g, hu']`. Both sides reduce to the same expression.
-/
theorem forms_induction_holds : FormsStep := by
  intro O _ A _ _ G _ Γ K jK T _ V W _ _ _ _ _ _ _ _ _ _ S F F' ψ hst hnat hker hsub f hf
  have hmem : (fun g => ψ ⟨(f : G → V) g, hf g⟩) ∈ Forms O Γ jK W := by
    intro γ g κ
    have h1 : (⟨(f : G → V) ((γ : G) * g * κ), hf _⟩ : F') = jK κ⁻¹ • ⟨(f : G → V) g, hf g⟩ :=
      Subtype.ext (f.2 γ g κ)
    show ψ _ = jK κ⁻¹ • ψ _
    rw [h1, map_smul]
  let φ : Forms O Γ jK W := ⟨_, hmem⟩
  have h0 : LocalizedModule.mk φ (1 : S) = LocalizedModule.mk 0 (1 : S) := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h0
  have hu' : (u : T) • φ = 0 := by
    simpa [Submonoid.smul_def] using hu
  refine ⟨u, u.2, fun g => ?_⟩
  apply hker ⟨_, hst F' u f hf g⟩
  rw [← hnat F' ψ u f φ hf (hst F' u f hf) (fun _ => rfl) g, hu']
  rfl

/- English proof (translation)
Introduce `O _ A _ _ G _ Γ K jK T _ V _ _ _ _ _ S D₀ D E hN hA hD0 hDE hstep f hf`. Set `Φ : Submodule A V → Submodule O (V ⧸ D₀)` to `fun F => (F.restrictScalars O).map D₀.mkQ`. Establish `hΦmono : ∀ F1 F2 : Submodule A V, F1 ≤ F2 → Φ F1 ≤ Φ F2` using `fun F1 F2 h => Submodule.map_mono (fun x hx => h hx)`. Establish `hΦ : ∀ F1 F2 : Submodule A V, D ≤ F1 → Φ F2 ≤ Φ F1 → F2 ≤ F1`. Introduce `F1 F2 h1 h x hx`.

Take `⟨y, hy, hxy⟩` from `h (Submodule.mem_map_of_mem (f := D₀.mkQ) (show x ∈ F2.restrictScalars O from hx))`. Establish `h2 : y - x ∈ D₀`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]`. Conclude with `sub_eq_zero.mpr hxy`. Establish `h3 : y - x ∈ F1` using `h1 (hD0 h2)`.

Establish `h4 : x = y - (y - x)` using `by abel`. Rewrite using `[h4]`. Conclude with `F1.sub_mem hy h3`. Set `PP : Set (Submodule A V)` to `{F | D ≤ F ∧ F ≤ E ∧ ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F}`. Establish `hE : E ∈ PP` using `⟨hDE, le_rfl, 1, S.one_mem, by simpa using hf⟩`.

Take `⟨_, ⟨F, hF, rfl⟩, hmin⟩` from `IsArtinian.set_has_minimal (Φ '' PP) ⟨_, E, hE, rfl⟩`. Take `⟨hDF, hFE, s, hs, hsf⟩` from `hF`. Distinguish the cases in `hEq : F ≤ D`. Conclude with `⟨s, hs, fun g => hEq (hsf g)⟩`. It suffices to derive a contradiction.

Establish `hlt : D < F` using `lt_of_le_not_ge hDF hEq`. Establish `hNA : IsNoetherian A V` using `isNoetherian_of_tower O hN`. Take `⟨F0, ⟨hDF0, hF0F⟩, hmax⟩` from `set_has_maximal_iff_noetherian.mpr hNA {F0 : Submodule A V | D ≤ F0 ∧ F0 < F} ⟨D, le_rfl, hlt⟩`. Establish `hcov : F0 ⋖ F` using `⟨hF0F, fun c h1 h2 => hmax c ⟨hDF0.trans h1.le, h2⟩ h1⟩`. Take `⟨s', hs', hs'f⟩` from `hstep F0 F hDF0 hcov hFE (s • f) hsf`.

Establish `hF0 : F0 ∈ PP` using `⟨hDF0, hF0F.le.trans hFE, s' * s, S.mul_mem hs' hs, by`. Introduce `g`. Rewrite using `[mul_smul]`. Conclude with `hs'f g⟩`. Apply `hmin (Φ F0) ⟨F0, hF0, rfl⟩` to reduce the goal to its premises.

Use `lt_of_le_not_ge (hΦmono _ _ hF0F.le) fun h => ?_` and prove the remaining obligations. Conclude with `absurd (hΦ F0 F hDF0 h) (not_le_of_gt hF0F)`.
-/
theorem forms_devissage_holds : FormsDevissage := by
  intro O _ A _ _ G _ Γ K jK T _ V _ _ _ _ _ S D₀ D E hN hA hD0 hDE hstep f hf
  let Φ : Submodule A V → Submodule O (V ⧸ D₀) := fun F => (F.restrictScalars O).map D₀.mkQ
  have hΦmono : ∀ F1 F2 : Submodule A V, F1 ≤ F2 → Φ F1 ≤ Φ F2 := fun F1 F2 h =>
    Submodule.map_mono (fun x hx => h hx)
  have hΦ : ∀ F1 F2 : Submodule A V, D ≤ F1 → Φ F2 ≤ Φ F1 → F2 ≤ F1 := by
    intro F1 F2 h1 h x hx
    obtain ⟨y, hy, hxy⟩ := h (Submodule.mem_map_of_mem (f := D₀.mkQ) (show x ∈ F2.restrictScalars O from hx))
    have h2 : y - x ∈ D₀ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      exact sub_eq_zero.mpr hxy
    have h3 : y - x ∈ F1 := h1 (hD0 h2)
    have h4 : x = y - (y - x) := by abel
    rw [h4]
    exact F1.sub_mem hy h3
  let PP : Set (Submodule A V) := {F | D ≤ F ∧ F ≤ E ∧
    ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F}
  have hE : E ∈ PP := ⟨hDE, le_rfl, 1, S.one_mem, by simpa using hf⟩
  obtain ⟨_, ⟨F, hF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Φ '' PP) ⟨_, E, hE, rfl⟩
  obtain ⟨hDF, hFE, s, hs, hsf⟩ := hF
  by_cases hEq : F ≤ D
  · exact ⟨s, hs, fun g => hEq (hsf g)⟩
  · exfalso
    have hlt : D < F := lt_of_le_not_ge hDF hEq
    have hNA : IsNoetherian A V := isNoetherian_of_tower O hN
    obtain ⟨F0, ⟨hDF0, hF0F⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr hNA
      {F0 : Submodule A V | D ≤ F0 ∧ F0 < F} ⟨D, le_rfl, hlt⟩
    have hcov : F0 ⋖ F := ⟨hF0F, fun c h1 h2 => hmax c ⟨hDF0.trans h1.le, h2⟩ h1⟩
    obtain ⟨s', hs', hs'f⟩ := hstep F0 F hDF0 hcov hFE (s • f) hsf
    have hF0 : F0 ∈ PP := ⟨hDF0, hF0F.le.trans hFE, s' * s, S.mul_mem hs' hs, by
      intro g
      rw [mul_smul]
      exact hs'f g⟩
    apply hmin (Φ F0) ⟨F0, hF0, rfl⟩
    refine lt_of_le_not_ge (hΦmono _ _ hF0F.le) fun h => ?_
    exact absurd (hΦ F0 F hDF0 h) (not_le_of_gt hF0F)

/- English proof (translation)
Introduce `O _ A _ _ G _ Γ K jK ι _ _ Nb _ _ B _ _ T _ _ _ _ S l ϖ n₀ ω pr e Λ L _ _ _ _ _ hwt depth i T2 ex c' hNoe hArt hdvd hstab he hHS hHN hclass hhw hIN1 hex hIN2`. Set `DA : Finset ι → Submodule A (⨂[O] τ, Nb τ)` to `fun s => { toAddSubmonoid := (tensSub (chainB B s)).toAddSubmonoid smul_mem' := fun a x hx => hstab s a x hx }`. Establish `hDA : ∀ s x, x ∈ DA s ↔ x ∈ tensSub (chainB B s)` using `fun s x => Iff.rfl`. Establish `hends` using `chain_ends_holds O ι Nb B`. Establish `hmono : ∀ s s' : Finset ι, s ⊆ s' → DA s ≤ DA s'` using `fun s s' h x hx => chain_monotone_holds O ι Nb B s s' h hx`.

Establish `hval : ∀ (c : ℕ) (f : Forms O Γ jK (⨂[O] τ, Nb τ)) (g : G), (((algebraMap O T l) ^ c • f : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g = l ^ c • (f : G → ⨂[O] τ, Nb τ) g`. Introduce `c f g`. Rewrite using `[← map_pow, algebraMap_smul]`. Both sides reduce to the same expression. Establish `hpow : scaleSub A (⨂[O] τ, Nb τ) (ϖ ^ (n₀ * ∑ τ, ex τ)) ≤ DA ∅`.

Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨u, hu⟩` from `hdvd`. Rewrite using `[hDA, hends.1, pow_mul, hu, mul_pow, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (tensor_reduction_holds O ι Nb B l ex hex y)`. Establish `hstep : ∀ (s : Finset ι) (a : ι), a ∉ s → ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ), (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA (insert a s)) → ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ cTau T2 ex c' a • f) : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s`.

Introduce `s a ha f hf`. Establish `hkill : ∀ c : ℕ, (∀ x : Nb a, l ^ c • x ∈ B a) → ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ c • f) : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s`. Introduce `c hc`. Use `⟨1, S.one_mem, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, hval]`.

Establish `h1` using `tensor_weight_kill_holds O ι Nb B s a LinearMap.id l c ha hc _ (hf g)`. Rewrite `h1` using `[factorAction_id]`. Then use the resulting hypothesis. Distinguish the cases in `haT : a ∈ T2`. Use `swap`. Establish `hc : cTau T2 ex c' a = ex a` using `by simp [cTau, haT]`.

Rewrite using `[hc]`. Conclude with `hkill _ (hex a)`. Distinguish the cases in `hle : ex a ≤ c' a`. Establish `hc : cTau T2 ex c' a = ex a` using `by simp [cTau, haT, hle]`. Rewrite using `[hc]`.

Conclude with `hkill _ (hex a)`. Establish `hc : cTau T2 ex c' a = c' a`. Simplify using `only [cTau, haT, if_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hc]`.

Set `E : Submodule A (⨂[O] τ, Nb τ)` to `{ carrier := {x | ∃ d ∈ DA s, ∃ n ∈ DA (insert a s), x = d + l ^ c' a • n} zero_mem' := ⟨0, (DA s).zero_mem, 0, (DA _).zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨d, hd, n, hn, rfl⟩ ⟨d', hd', n', hn', rfl⟩`. Conclude with `⟨d + d', (DA s).add_mem hd hd', n + n', (DA _).add_mem hn hn', by`. Rewrite using `[smul_add]`. Use the proof step `abel⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `b _ ⟨d, hd, n, hn, rfl⟩`. Conclude with `⟨b • d, (DA s).smul_mem b hd, b • n, (DA _).smul_mem b hn, by`. Rewrite using `[smul_add, smul_comm]⟩ }`. Establish `hDE : DA s ≤ E` using `fun d hd => ⟨d, hd, 0, (DA _).zero_mem, by simp⟩`.

Establish `hD0 : tensSub B ≤ (DA s).restrictScalars O`. Introduce `x hx`. Rewrite `hx` using `[← hends.1]`. Conclude with `hmono ∅ s (Finset.empty_subset _) hx`. Use `forms_devissage_holds O A G Γ K jK T (⨂[O] τ, Nb τ) S (tensSub B) (DA s) E hNoe hArt hD0 hDE ?_ _ (fun g => ⟨0, (DA s).zero_mem, _, hf g, by rw [hval, zero_add]⟩)` and prove the remaining obligations.

Introduce `F F' hDF hcov hF'E`. Establish `hsimple : IsSimpleModule A (F' ⧸ F.comap F'.subtype)` using `(covBy_iff_quot_is_simple hcov.le).mp hcov`. Establish `hsq` using `hSS O A (⨂[O] τ, Nb τ) ϖ _ F F' hcov.le (hpow.trans ((hmono ∅ s (Finset.empty_subset _)).trans hDF)) hsimple`. Take `⟨μ, ⟨iso⟩⟩` from `hclass _ hsimple hsq`. Establish `hcf` using `hIso A _ _ (L μ) ⟨iso⟩ hsq`.

Set `ψ : F' →ₗ[A] L μ` to `iso.toLinearMap.comp (F.comap F'.subtype).mkQ`. Establish `hψ0 : ∀ x : F', (x : ⨂[O] τ, Nb τ) ∈ F → ψ x = 0`. Introduce `x hx`. Use `show iso ((F.comap F'.subtype).mkQ x) = 0`. Establish `h1 : (F.comap F'.subtype).mkQ x = 0`.

Rewrite using `[Submodule.mkQ_apply]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ F.comap F'.subtype from hx)`. Rewrite using `[h1, map_zero]`. Establish `hker : ∀ x : F', ψ x = 0 → (x : ⨂[O] τ, Nb τ) ∈ F`. Introduce `x hx`.

Establish `h1 : (F.comap F'.subtype).mkQ x = 0` using `iso.injective (by rw [map_zero]; exact hx)`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `h1`. Establish `hdeep : i a < depth a (hwt μ a)`. Assume the negation of the conclusion as `hnot`.

Establish `hle' : depth a (hwt μ a) ≤ i a` using `not_lt.mp hnot`. Take `⟨z, hz⟩` from `hhw μ a`. Take `⟨x, rfl⟩ : ∃ x, ψ x = z` from `(iso.surjective.comp (Submodule.mkQ_surjective _)) z`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← map_smul]`.

Apply `hψ0` to reduce the goal to its premises. Take `⟨d, hd, n, hn, hxe⟩` from `hF'E x.2`. Rewrite using `[Submodule.coe_smul, hxe, smul_add, smul_comm]`. Use `F.add_mem (hDF ((DA s).smul_mem _ hd)) (hDF ?_)` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `tensor_weight_kill_holds O ι Nb B s a (pr a (hwt μ a)) l (c' a) ha (hIN2 a haT _ hle') n hn`. Establish `hvan : Subsingleton (LocalizedModule S (Forms O Γ jK (L μ)))`. Assume the negation of the conclusion as `hns`. Conclude with `absurd (hIN1 μ hcf hns a haT) (not_le.mpr hdeep)`. Conclude with `forms_induction_holds O A G Γ K jK T (⨂[O] τ, Nb τ) (L μ) S F F' ψ hHS (hHN μ) hker hvan`.

Establish `hall : ∀ s : Finset ι, ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ), (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA s) → ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) • f) : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA ∅`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`.

Conclude with `⟨1, S.one_mem, by simpa using hf⟩`. Consider the case `insert a s ha ih`. Introduce `f hf`. Take `⟨σ1, hσ1, h1⟩` from `hstep s a ha f hf`. Take `⟨σ2, hσ2, h2⟩` from `ih _ h1`.

Use `⟨σ2 * σ1, S.mul_mem hσ2 hσ1, fun g => ?_⟩` and prove the remaining obligations. Establish `e1 : (σ2 * σ1) • ((algebraMap O T l) ^ (∑ τ ∈ insert a s, cTau T2 ex c' τ) • f) = σ2 • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) • (σ1 • ((algebraMap O T l) ^ cTau T2 ex c' a • f)))`. Rewrite using `[Finset.sum_insert ha]`. Simplify using `only [smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `h2 g`. Introduce `y`. Proceed by induction on `y using LocalizedModule.induction_on with`.

Consider the case `h f σ0`. Take `⟨σ, hσ, h⟩` from `hall Finset.univ f (fun g => by rw [hDA, hends.2]; trivial)`. Use `⟨σ • ((algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • f), ?_, ⟨σ, hσ⟩ * σ0, ?_⟩` and prove the remaining obligations. Use `⟨Subtype.property _, fun g _ => ?_⟩` and prove the remaining obligations. Establish `h1` using `h g`.

Rewrite `h1` using `[hDA, hends.1]`. Then use the resulting hypothesis. Rewrite using `[LocalizedModule.smul'_mk]`. Conclude with `LocalizedModule.mk_cancel_common_left ⟨σ, hσ⟩ σ0 _`.
-/
theorem theorem_w_central_of_simple_quotients (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWCore := by
  intro O _ A _ _ G _ Γ K jK ι _ _ Nb _ _ B _ _ T _ _ _ _ S l ϖ n₀ ω pr e Λ L _ _ _ _ _ hwt depth i T2
    ex c' hNoe hArt hdvd hstab he hHS hHN hclass hhw hIN1 hex hIN2
  let DA : Finset ι → Submodule A (⨂[O] τ, Nb τ) := fun s =>
    { toAddSubmonoid := (tensSub (chainB B s)).toAddSubmonoid
      smul_mem' := fun a x hx => hstab s a x hx }
  have hDA : ∀ s x, x ∈ DA s ↔ x ∈ tensSub (chainB B s) := fun s x => Iff.rfl
  have hends := chain_ends_holds O ι Nb B
  have hmono : ∀ s s' : Finset ι, s ⊆ s' → DA s ≤ DA s' := fun s s' h x hx =>
    chain_monotone_holds O ι Nb B s s' h hx
  have hval : ∀ (c : ℕ) (f : Forms O Γ jK (⨂[O] τ, Nb τ)) (g : G),
      (((algebraMap O T l) ^ c • f : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g =
        l ^ c • (f : G → ⨂[O] τ, Nb τ) g := by
    intro c f g
    rw [← map_pow, algebraMap_smul]
    rfl
  have hpow : scaleSub A (⨂[O] τ, Nb τ) (ϖ ^ (n₀ * ∑ τ, ex τ)) ≤ DA ∅ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, hu⟩ := hdvd
    rw [hDA, hends.1, pow_mul, hu, mul_pow, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (tensor_reduction_holds O ι Nb B l ex hex y)
  have hstep : ∀ (s : Finset ι) (a : ι), a ∉ s → ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA (insert a s)) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ cTau T2 ex c' a • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
    intro s a ha f hf
    have hkill : ∀ c : ℕ, (∀ x : Nb a, l ^ c • x ∈ B a) →
        ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ c • f) :
          Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
      intro c hc
      refine ⟨1, S.one_mem, fun g => ?_⟩
      rw [one_smul, hval]
      have h1 := tensor_weight_kill_holds O ι Nb B s a LinearMap.id l c ha hc _ (hf g)
      rwa [factorAction_id] at h1
    by_cases haT : a ∈ T2
    swap
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT]
      rw [hc]
      exact hkill _ (hex a)
    by_cases hle : ex a ≤ c' a
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT, hle]
      rw [hc]
      exact hkill _ (hex a)
    have hc : cTau T2 ex c' a = c' a := by
      simp only [cTau, haT, if_true]
      omega
    rw [hc]
    let E : Submodule A (⨂[O] τ, Nb τ) :=
      { carrier := {x | ∃ d ∈ DA s, ∃ n ∈ DA (insert a s), x = d + l ^ c' a • n}
        zero_mem' := ⟨0, (DA s).zero_mem, 0, (DA _).zero_mem, by simp⟩
        add_mem' := by
          rintro _ _ ⟨d, hd, n, hn, rfl⟩ ⟨d', hd', n', hn', rfl⟩
          exact ⟨d + d', (DA s).add_mem hd hd', n + n', (DA _).add_mem hn hn', by
            rw [smul_add]; abel⟩
        smul_mem' := by
          rintro b _ ⟨d, hd, n, hn, rfl⟩
          exact ⟨b • d, (DA s).smul_mem b hd, b • n, (DA _).smul_mem b hn, by
            rw [smul_add, smul_comm]⟩ }
    have hDE : DA s ≤ E := fun d hd => ⟨d, hd, 0, (DA _).zero_mem, by simp⟩
    have hD0 : tensSub B ≤ (DA s).restrictScalars O := by
      intro x hx
      rw [← hends.1] at hx
      exact hmono ∅ s (Finset.empty_subset _) hx
    refine forms_devissage_holds O A G Γ K jK T (⨂[O] τ, Nb τ) S (tensSub B) (DA s) E hNoe hArt hD0 hDE
      ?_ _ (fun g => ⟨0, (DA s).zero_mem, _, hf g, by rw [hval, zero_add]⟩)
    intro F F' hDF hcov hF'E
    have hsimple : IsSimpleModule A (F' ⧸ F.comap F'.subtype) :=
      (covBy_iff_quot_is_simple hcov.le).mp hcov
    have hsq := hSS O A (⨂[O] τ, Nb τ) ϖ _ F F' hcov.le
      (hpow.trans ((hmono ∅ s (Finset.empty_subset _)).trans hDF)) hsimple
    obtain ⟨μ, ⟨iso⟩⟩ := hclass _ hsimple hsq
    have hcf := hIso A _ _ (L μ) ⟨iso⟩ hsq
    let ψ : F' →ₗ[A] L μ := iso.toLinearMap.comp (F.comap F'.subtype).mkQ
    have hψ0 : ∀ x : F', (x : ⨂[O] τ, Nb τ) ∈ F → ψ x = 0 := by
      intro x hx
      show iso ((F.comap F'.subtype).mkQ x) = 0
      have h1 : (F.comap F'.subtype).mkQ x = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ F.comap F'.subtype from hx)
      rw [h1, map_zero]
    have hker : ∀ x : F', ψ x = 0 → (x : ⨂[O] τ, Nb τ) ∈ F := by
      intro x hx
      have h1 : (F.comap F'.subtype).mkQ x = 0 := iso.injective (by rw [map_zero]; exact hx)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    have hdeep : i a < depth a (hwt μ a) := by
      by_contra hnot
      have hle' : depth a (hwt μ a) ≤ i a := not_lt.mp hnot
      obtain ⟨z, hz⟩ := hhw μ a
      obtain ⟨x, rfl⟩ : ∃ x, ψ x = z :=
        (iso.surjective.comp (Submodule.mkQ_surjective _)) z
      apply hz
      rw [← map_smul]
      apply hψ0
      obtain ⟨d, hd, n, hn, hxe⟩ := hF'E x.2
      rw [Submodule.coe_smul, hxe, smul_add, smul_comm]
      refine F.add_mem (hDF ((DA s).smul_mem _ hd)) (hDF ?_)
      rw [he]
      exact tensor_weight_kill_holds O ι Nb B s a (pr a (hwt μ a)) l (c' a) ha
        (hIN2 a haT _ hle') n hn
    have hvan : Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) := by
      by_contra hns
      exact absurd (hIN1 μ hcf hns a haT) (not_le.mpr hdeep)
    exact forms_induction_holds O A G Γ K jK T (⨂[O] τ, Nb τ) (L μ) S F F' ψ hHS (hHN μ) hker hvan
  have hall : ∀ s : Finset ι, ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA s) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      exact ⟨1, S.one_mem, by simpa using hf⟩
    | insert a s ha ih =>
      intro f hf
      obtain ⟨σ1, hσ1, h1⟩ := hstep s a ha f hf
      obtain ⟨σ2, hσ2, h2⟩ := ih _ h1
      refine ⟨σ2 * σ1, S.mul_mem hσ2 hσ1, fun g => ?_⟩
      have e1 : (σ2 * σ1) • ((algebraMap O T l) ^ (∑ τ ∈ insert a s, cTau T2 ex c' τ) • f) =
          σ2 • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) •
            (σ1 • ((algebraMap O T l) ^ cTau T2 ex c' a • f))) := by
        rw [Finset.sum_insert ha]
        simp only [smul_smul]
        congr 1
        ring
      rw [e1]
      exact h2 g
  intro y
  induction y using LocalizedModule.induction_on with
  | h f σ0 =>
    obtain ⟨σ, hσ, h⟩ := hall Finset.univ f (fun g => by rw [hDA, hends.2]; trivial)
    refine ⟨σ • ((algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • f), ?_, ⟨σ, hσ⟩ * σ0, ?_⟩
    · refine ⟨Subtype.property _, fun g _ => ?_⟩
      have h1 := h g
      rwa [hDA, hends.1] at h1
    · rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel_common_left ⟨σ, hσ⟩ σ0 _

/- English proof (translation)
Establish `h : dualWeyl O r n ν ≤ homogeneousSubmodule (Fin r × Fin n) O (∑ s, ν s)`. Introduce `f hf`. Establish `h1` using `(mem_dualWeyl_iff.1 hf).1`. Rewrite using `[mem_homogeneousSubmodule]`. Introduce `m hm`.

Rewrite using `[← lclosedeq_weight_sum, h1 hm]`. Conclude with `Module.Finite.iff_fg.mpr (Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h)`.
-/
theorem dualWeyl_module_finite (O : Type) [CommRing O] [IsNoetherianRing O] (r n : ℕ) (ν : Fin n → ℕ) :
    Module.Finite O (dualWeyl O r n ν) := by
  have h : dualWeyl O r n ν ≤ homogeneousSubmodule (Fin r × Fin n) O (∑ s, ν s) := by
    intro f hf
    have h1 := (mem_dualWeyl_iff.1 hf).1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← lclosedeq_weight_sum, h1 hm]
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h)

/- English proof (translation)
Use `haveI : Finite (O ⧸ (Ideal.span {l}) ^ J) := Ideal.finite_quotient_pow (IsNoetherian.noetherian (Ideal.span {l})) J`. Use `haveI : Finite (V ⧸ ((Ideal.span {l}) ^ J • ⊤ : Submodule O V)) := Module.finite_of_finite (O ⧸ (Ideal.span {l}) ^ J)`. Establish `hle : ((Ideal.span {l}) ^ J • ⊤ : Submodule O V) ≤ U`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr n _`.

Rewrite `hr` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hr`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `U.smul_mem _ (hU n)`. Conclude with `Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)`.
-/
theorem finite_quotient_of_pow_smul_mem (O : Type) [CommRing O] [IsNoetherianRing O] (V : Type) [AddCommGroup V]
    [Module O V] [Module.Finite O V] (l : O) (J : ℕ) (U : Submodule O V)
    (hfin : Finite (O ⧸ Ideal.span {l})) (hU : ∀ x : V, l ^ J • x ∈ U) : Finite (V ⧸ U) := by
  haveI : Finite (O ⧸ (Ideal.span {l}) ^ J) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (Ideal.span {l})) J
  haveI : Finite (V ⧸ ((Ideal.span {l}) ^ J • ⊤ : Submodule O V)) :=
    Module.finite_of_finite (O ⧸ (Ideal.span {l}) ^ J)
  have hle : ((Ideal.span {l}) ^ J • ⊤ : Submodule O V) ≤ U := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rw [mul_comm, mul_smul]
    exact U.smul_mem _ (hU n)
  exact Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/- English proof (translation)
Introduce `hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hT`. Take `⟨hl, hu, hfin, hdvd, hh, ht, hshape, hecl, hex, hstab, he, hHS, hHN, hclass, hhw, hIN1⟩` from `hT`. Use `haveI : ∀ τ : ι, Module.Finite O (dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_module_finite O N N _`. Set `pr : ∀ τ : ι, (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) →ₗ[O] dualWeyl O N N (res N (lam τ))` to `fun τ w => (weightedHomogeneousComponent (rowW N N) w).restrict (fun x hx => dualWeylRowGraded O N N (res N (lam τ)) w x hx)`. Establish `hexO : ∀ τ, LatIncl (l : O) (deltaIn O N lam τ) (ex τ)` using `fun τ x => LA.la_incl_R_of_Z O N N le_rfl (res N (lam τ)) l (ex τ) hu (hex τ) x x.2`.

Establish `hNoe : IsNoetherian O (NablaT O N lam)` using `inferInstance`. Establish `hArt : IsArtinian O (NablaT O N lam ⧸ tensSub (deltaIn O N lam))` using `by haveI := finite_quotient_of_pow_smul_mem O (NablaT O N lam) (l : O) (∑ τ, ex τ) (tensSub (deltaIn O N lam)) hfin (tensor_reduction_holds O ι _ (deltaIn O N lam) (l : O) ex hexO)`. Conclude with `isArtinian_of_finite`. Establish `he' : ∀ τ w (x : NablaT O N lam), e τ w • x = atFactor τ (pr τ w) x`. Introduce `τ w x`.

Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r u`. Rewrite using `[smul_comm, map_smul, he τ w u (pr τ w (u τ)) rfl, factor_action_on_tensor_product_holds]`. Consider the case `add a b ha hb => rw [smul_add, map_add, ha, hb]`. Establish `hIN2 : ∀ τ ∈ T2, ∀ w, depthAt N k j lam τ w ≤ ((i τ : ℕ) : ℤ) → ∀ x : dualWeyl O N N (res N (lam τ)), (l : O) ^ cFloor l N k t h lam j q xm xp ecl i τ • pr τ w x ∈ deltaIn O N lam τ`.

Introduce `τ hτ w hw x`. Take `⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩` from `hshape τ hτ`. Establish `hA` using `application_window hD l k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ) hl ht`. Rewrite `hA` using `[hrows]`. Establish `hE` using `hA hanti hblock hspread hh hcloud hlows habove hle htop (ecl τ) (hecl τ hτ) (i τ) w hw`.

Conclude with `pow_smul_weighted_component_mem_weyl O l N (res N (lam τ)) w _ hu hE x x.2`. Establish `hmain` using `theorem_w_central_of_simple_quotients hSS hIso O A G Γ K jK ι (fun τ => dualWeyl O N N (res N (lam τ))) (deltaIn O N lam) T S (l : O) ϖ n₀ (Fin N → ℕ) pr e Λ L hwt (depthAt N k j lam) (fun τ => (i τ : ℤ)) T2 ex (cFloor l N k t h lam j q xm xp ecl i) hNoe hArt hdvd hstab he' hHS h …`. Conclude with `⟨hmain, Nat.sInf_le hmain⟩`.
-/
theorem theorem_w_top_of_simple_quotients (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWTop := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  obtain ⟨hl, hu, hfin, hdvd, hh, ht, hshape, hecl, hex, hstab, he, hHS, hHN, hclass, hhw, hIN1⟩ := hT
  haveI : ∀ τ : ι, Module.Finite O (dualWeyl O N N (res N (lam τ))) :=
    fun τ => dualWeyl_module_finite O N N _
  let pr : ∀ τ : ι, (Fin N → ℕ) →
      dualWeyl O N N (res N (lam τ)) →ₗ[O] dualWeyl O N N (res N (lam τ)) := fun τ w =>
    (weightedHomogeneousComponent (rowW N N) w).restrict
      (fun x hx => dualWeylRowGraded O N N (res N (lam τ)) w x hx)
  have hexO : ∀ τ, LatIncl (l : O) (deltaIn O N lam τ) (ex τ) := fun τ x =>
    LA.la_incl_R_of_Z O N N le_rfl (res N (lam τ)) l (ex τ) hu (hex τ) x x.2
  have hNoe : IsNoetherian O (NablaT O N lam) := inferInstance
  have hArt : IsArtinian O (NablaT O N lam ⧸ tensSub (deltaIn O N lam)) := by
    haveI := finite_quotient_of_pow_smul_mem O (NablaT O N lam) (l : O) (∑ τ, ex τ) (tensSub (deltaIn O N lam)) hfin
      (tensor_reduction_holds O ι _ (deltaIn O N lam) (l : O) ex hexO)
    exact isArtinian_of_finite
  have he' : ∀ τ w (x : NablaT O N lam), e τ w • x = atFactor τ (pr τ w) x := by
    intro τ w x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [smul_comm, map_smul, he τ w u (pr τ w (u τ)) rfl, factor_action_on_tensor_product_holds]
    | add a b ha hb => rw [smul_add, map_add, ha, hb]
  have hIN2 : ∀ τ ∈ T2, ∀ w, depthAt N k j lam τ w ≤ ((i τ : ℕ) : ℤ) →
      ∀ x : dualWeyl O N N (res N (lam τ)),
        (l : O) ^ cFloor l N k t h lam j q xm xp ecl i τ • pr τ w x ∈ deltaIn O N lam τ := by
    intro τ hτ w hw x
    obtain ⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩ := hshape τ hτ
    have hA := application_window hD l k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ) hl ht
    rw [hrows] at hA
    have hE := hA hanti hblock hspread hh hcloud hlows habove hle htop (ecl τ) (hecl τ hτ) (i τ) w hw
    exact pow_smul_weighted_component_mem_weyl O l N (res N (lam τ)) w _ hu hE x x.2
  have hmain := theorem_w_central_of_simple_quotients hSS hIso O A G Γ K jK ι (fun τ => dualWeyl O N N (res N (lam τ)))
    (deltaIn O N lam) T S (l : O) ϖ n₀ (Fin N → ℕ) pr e Λ L hwt (depthAt N k j lam)
    (fun τ => (i τ : ℤ)) T2 ex (cFloor l N k t h lam j q xm xp ecl i) hNoe hArt hdvd hstab he' hHS hHN
    hclass hhw hIN1 hexO hIN2
  exact ⟨hmain, Nat.sInf_le hmain⟩

open Formalism.RankGapBounds.ChebyshevFactorialBounds in
/- English proof (translation)
Introduce `hD ι _ _ D l O _ _ _ A _ _ G _ Γ K jK lam _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hP hT hmaxB hJ`. Establish `hl : l.Prime` using `hT.1`. Establish `h1` using `(hTop hD O A G Γ K jK ι l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l) (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e Λ L hwt hT).2`. Establish `h2 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l) (cFloor l D.Nr D.k D.t D.h lam D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l) (fun τ => D.depth τ l)) τ : ℕ) : ℝ)`. Conclude with `hJ.trans h1` after adjusting the coercions.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `τ _`. Use `le_trans (le_of_eq ?_) (tau_term_le_correction_bound D hP l hl τ)` and prove the remaining obligations.

Use `congr 1`. Unfold `cTau`. Distinguish the cases in `hτ : τ ∈ D.T2`. Rewrite using `[if_pos hτ, if_pos hτ]`. Unfold `cFloor`.

Simplify using `only [hmaxB τ hτ]`. Rewrite using `[if_neg hτ, if_neg hτ]`.
-/
theorem block_ideal_at_of_top_theorem (hTop : TheoremWTop) : BlockIdealAt := by
  intro hD ι _ _ D l O _ _ _ A _ _ G _ Γ K jK lam _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hP hT hmaxB hJ
  have hl : l.Prime := hT.1
  have h1 := (hTop hD O A G Γ K jK ι l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi
    (fun τ => D.ecl τ l) (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e Λ L hwt hT).2
  have h2 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l)
      (cFloor l D.Nr D.k D.t D.h lam D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
        (fun τ => D.depth τ l)) τ : ℕ) : ℝ) := by
    exact_mod_cast hJ.trans h1
  refine h2.trans ?_
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro τ _
  refine le_trans (le_of_eq ?_) (tau_term_le_correction_bound D hP l hl τ)
  congr 1
  unfold cTau
  by_cases hτ : τ ∈ D.T2
  · rw [if_pos hτ, if_pos hτ]
    unfold cFloor
    simp only [hmaxB τ hτ]
  · rw [if_neg hτ, if_neg hτ]

/- English proof (translation)
The claim follows from `theorem_w_central_of_simple_quotients simple_subquotient_of_power_holds subquotient_iso_holds`.
-/
theorem theorem_w_central_holds : TheoremWCore := theorem_w_central_of_simple_quotients simple_subquotient_of_power_holds subquotient_iso_holds

/- English proof (translation)
The claim follows from `theorem_w_top_of_simple_quotients simple_subquotient_of_power_holds subquotient_iso_holds`.
-/
theorem weight_theorem_top : TheoremWTop := theorem_w_top_of_simple_quotients simple_subquotient_of_power_holds subquotient_iso_holds

/- English proof (translation)
The claim follows from `block_ideal_at_of_top_theorem weight_theorem_top`.
-/
theorem block_ideal_at : BlockIdealAt := block_ideal_at_of_top_theorem weight_theorem_top

/- English proof (translation)
Introduce `hD R _ _ l N k j t q h lam xm xp ecl hl hu hh ht hS hecl I w hw x hx`. Take `⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩` from `hS`. Establish `hA` using `application_window hD l k j t q h lam xm xp hl ht`. Rewrite `hA` using `[hrows]`. Establish `hE` using `hA hanti hblock hspread hh hcloud hlows habove hle htop ecl hecl I w hw`.

Conclude with `exponent_le_over_ring_holds R l N (res N lam) w _ hu hE x hx`.
-/
theorem integral_ring_second_level : WeightSpacePrimePowerBoundOverDomain := by
  intro hD R _ _ l N k j t q h lam xm xp ecl hl hu hh ht hS hecl I w hw x hx
  obtain ⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩ := hS
  have hA := application_window hD l k j t q h lam xm xp hl ht
  rw [hrows] at hA
  have hE := hA hanti hblock hspread hh hcloud hlows habove hle htop ecl hecl I w hw
  exact exponent_le_over_ring_holds R l N (res N lam) w _ hu hE x hx

/- English proof (translation)
Introduce `r ν μ l e ⟨m, hm, h⟩ x hx`. Use `⟨(m : ℤ), fun hd => hm (Int.natCast_dvd_natCast.mp hd), ?_⟩` and prove the remaining obligations. Establish `h1` using `h x hx.1`. Move the coercions through the operations in `at h1`. Conclude with `h1`.
-/
theorem exponent_le_of_integral_inclusion_holds : ExpLeOfInclZ := by
  intro r ν μ l e ⟨m, hm, h⟩ x hx
  refine ⟨(m : ℤ), fun hd => hm (Int.natCast_dvd_natCast.mp hd), ?_⟩
  have h1 := h x hx.1
  push_cast at h1
  exact h1

/- English proof (translation)
Introduce `l N k lam hl hN hk`. Conclude with `⟨LA.exact_z_specialization N N le_rfl _ hN l hl, fun μ => exponent_le_of_integral_inclusion_holds k _ μ l _ (LA.exact_z_specialization k k le_rfl _ hk l hl)⟩`.
-/
theorem exact_exponents_fit_holds : ExactExponentsFit := by
  intro l N k lam hl hN hk
  exact ⟨LA.exact_z_specialization N N le_rfl _ hN l hl,
    fun μ => exponent_le_of_integral_inclusion_holds k _ μ l _ (LA.exact_z_specialization k k le_rfl _ hk l hl)⟩

/- English proof (translation)
Introduce `O _ A _ _ G _ Γ K jK ι l N lam _ _ T _ _ _ _ S J J' hJ h y`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hJ`. Take `⟨x, hx, s, hxs⟩` from `h y`. Use `⟨(algebraMap O T (l : O)) ^ d • x, ?_, s, ?_⟩` and prove the remaining obligations. Use `show (((algebraMap O T (l : O)) ^ d • x : Forms O Γ jK (NablaT O N lam)) : G → NablaT O N lam) ∈ formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))`.

Rewrite using `[← map_pow, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[← LocalizedModule.smul'_mk, hxs, smul_smul, ← pow_add, add_comm]`.
-/
theorem top_inclusion_monotone_holds : TopInclMono := by
  intro O _ A _ _ G _ Γ K jK ι l N lam _ _ T _ _ _ _ S J J' hJ h y
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJ
  obtain ⟨x, hx, s, hxs⟩ := h y
  refine ⟨(algebraMap O T (l : O)) ^ d • x, ?_, s, ?_⟩
  · show (((algebraMap O T (l : O)) ^ d • x : Forms O Γ jK (NablaT O N lam)) : G → NablaT O N lam) ∈
      formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))
    rw [← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx
  · rw [← LocalizedModule.smul'_mk, hxs, smul_smul, ← pow_add, add_comm]

/- English proof (translation)
Introduce `hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hT`. Establish `hl : l.Prime` using `hT.1`. Use `top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_ (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1` and prove the remaining obligations. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `τ _`.

Unfold `cTau`. Use `split_ifs`. Conclude with `min_le_min le_rfl (Nat.floor_le_floor (c_prime_le_coarse_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))`. Conclude with `le_rfl`.
-/
theorem weight_theorem_top_coarse : TheoremWTopCoarse := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  have hl : l.Prime := hT.1
  refine top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_
    (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1
  apply Finset.sum_le_sum
  intro τ _
  unfold cTau
  split_ifs
  · exact min_le_min le_rfl (Nat.floor_le_floor
      (c_prime_le_coarse_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))
  · exact le_rfl

open Formalism.RankGapBounds.ChebyshevFactorialBounds in
/- English proof (translation)
Introduce `hD ι _ _ D hP h l hl hE hlJ h2 h3 h4`. Take `⟨O, _, _, _, A, _, _, G, _, Γ, K, jK, lam, _, _, T, _, _, _, _, S, ϖ, n₀, e, Λ, L, _, _, _, _, _, hwt, hT, hB, hJ⟩` from `h l hl hE hlJ h2 h3 h4`. Conclude with `block_ideal_at hD ι D l O A G Γ K jK lam T S ϖ n₀ e Λ L hwt hP hT hB hJ`.
-/
theorem block_ideal_bound_derived : BlockIdealBound5Derived := by
  intro hD ι _ _ D hP h l hl hE hlJ h2 h3 h4
  obtain ⟨O, _, _, _, A, _, _, G, _, Γ, K, jK, lam, _, _, T, _, _, _, _, S, ϖ, n₀, e, Λ, L, _, _, _, _, _,
    hwt, hT, hB, hJ⟩ := h l hl hE hlJ h2 h3 h4
  exact block_ideal_at hD ι D l O A G Γ K jK lam T S ϖ n₀ e Λ L hwt hP hT hB hJ

/- English proof (translation)
Introduce `N c lam w`. Unfold `depth2 res varpi UN`. Rewrite using `[Finset.sum_filter]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Use `split_ifs`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem depth_as_weight_sum_holds : DepthAsU := by
  intro N c lam w
  unfold depth2 res varpi UN
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · ring
  · ring

/- English proof (translation)
Introduce `ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ lam w hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hU hU'`. Establish `h` using `weightExchangeFull_holds ι σ k j t q l h F W U U' bot cst kap c τ hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11`. Rewrite using `[depth_as_weight_sum_holds]`. Establish `e1 : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (UN (k + j + t + q) lam a - ((w a : ℤ) + ((k + j + t + q : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ))) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a)` using `Finset.sum_congr rfl fun a _ => by rw [hU, hU']`. Rewrite using `[e1]`.

Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_exponent_depth_holds : WEDepth := by
  intro ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ lam w hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    hU hU'
  have h := weightExchangeFull_holds ι σ k j t q l h F W U U' bot cst kap c τ hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11
  rw [depth_as_weight_sum_holds]
  have e1 : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (UN (k + j + t + q) lam a - ((w a : ℤ) + ((k + j + t + q : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ))) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) :=
    Finset.sum_congr rfl fun a _ => by rw [hU, hU']
  rw [e1]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Formalism.CohomologicalDescent.DepthNonnegative
