import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultMk

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Mk

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

/- English proof (translation)
Rewrite using `[X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]`.
-/
theorem mono_two (v1 v2 : VarH X) (a b : ℕ) :
    (monomial (Finsupp.single v1 a + Finsupp.single v2 b) (1 : KK O) : RHH O X) =
      MvPolynomial.X v1 ^ a * MvPolynomial.X v2 ^ b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

/- English proof (translation)
Break down `a with x | x | x | c` into its components or cases. Establish `h` using `softKSP S hS hD x.1 x.2 ((X.seg C0 CE1 CE2 x.1).P X.p x.2)`. Rewrite `h` using `[sgKS_powP]`. Use `show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) + Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)) 1) _`. Rewrite using `[mono_two]`.

Conclude with `h`. Establish `h` using `softKW S hS hD x.1 x.2.1 x.2.2 show SoftOK S.w _ _ (monomial (Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 + Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)) 1) _`. Rewrite using `[mono_two, pow_one]`. Conclude with `h`. Establish `h` using `softKS S hS hD x.1 x.2 show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) + Finsupp.single ((topOdd X x.1 x.2, false), 0) 1) 1) _`.

Rewrite using `[mono_two, pow_one]`. Conclude with `h`. Establish `h` using `softLoc S.w hD h2 c show SoftOK S.w _ _ (monomial (∑ j : Fin (numSeg X.TT), Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)) 1) _`. Rewrite using `[monomial_sum_one]`. Establish `e : ∏ j : Fin (numSeg X.TT), (monomial (Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (X.p ^ segG X.TT j - 1)) (1 : KK O) : RHH O X) = sgLoc O X`.

Unfold `sgLoc`. Conclude with `Finset.prod_congr rfl fun j _ => by rw [X_pow_eq_monomial]`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem softMk (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (C0 CE1 CE2 : ℝ) (a : IM X) :
    SoftOK S.w (fMk O C0 CE1 CE2 X a) (oMk C0 CE1 CE2 X a) (monomial (aMk C0 CE1 CE2 X a) 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · have h := softKSP S hS hD x.1 x.2 ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
    rw [sgKS_powP] at h
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)) 1) _
    rw [mono_two]
    exact h
  · have h := softKW S hS hD x.1 x.2.1 x.2.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softKS S hS hD x.1 x.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softLoc S.w hD h2 c
    show SoftOK S.w _ _ (monomial (∑ j : Fin (numSeg X.TT),
      Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)) 1) _
    rw [monomial_sum_one]
    have e : ∏ j : Fin (numSeg X.TT), (monomial (Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1)))
        (X.p ^ segG X.TT j - 1)) (1 : KK O) : RHH O X) = sgLoc O X := by
      unfold sgLoc
      exact Finset.prod_congr rfl fun j _ => by rw [X_pow_eq_monomial]
    rw [e]
    exact h

/- English proof (translation)
Break down `a with x | x | x | c` into its components or cases. Conclude with `mem_Pol_iff.2 fun l => by`. Establish `h` using `(mem_Pol_iff.1 (kS_pol (O := O) x.1 x.2) l).pow ((X.seg C0 CE1 CE2 x.1).P X.p x.2)`. Rewrite `h` using `[smul_eq_mul]`. Conclude with `h`.

Conclude with `kW_pol x.1 x.2.1 _`. Conclude with `kS_pol x.1 x.2`. Conclude with `loc_pol _`.
-/
theorem fMk_pol (C0 CE1 CE2 : ℝ) (a : IM X) :
    fMk O C0 CE1 CE2 X a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · exact mem_Pol_iff.2 fun l => by
      have h := (mem_Pol_iff.1 (kS_pol (O := O) x.1 x.2) l).pow ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
      rw [smul_eq_mul] at h
      exact h
  · exact kW_pol x.1 x.2.1 _
  · exact kS_pol x.1 x.2
  · exact loc_pol _

end Mk

section Deg

variable {X : Loc}

/- English proof (translation)
Introduce `j j' h`. Establish `h1 : (evenTops X.TT).get j = (evenTops X.TT).get j'` using `congrArg Subtype.val h`. Establish `hnd : (evenTops X.TT).Nodup` using `Finset.sort_nodup _ _`. Conclude with `hnd.get_inj_iff.mp h1`.
-/
theorem topStart_inj (X : Loc) : Function.Injective (topStart X) := by
  intro j j' h
  have h1 : (evenTops X.TT).get j = (evenTops X.TT).get j' := congrArg Subtype.val h
  have hnd : (evenTops X.TT).Nodup := Finset.sort_nodup _ _
  exact hnd.get_inj_iff.mp h1

/- English proof (translation)
Introduce `h`. Establish `h1 : (segPos X.TT j i).val = (segNext X.TT j').val` using `congrArg (fun x : X.TT => (x.val : ℕ)) h`. Conclude with `(pos_mem X.TT j i).2 (h1 ▸ (next_mem X.TT j').2)`.
-/
theorem topOdd_ne_endAny (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (j' : Fin (numSeg X.TT)) :
    topOdd X j i ≠ topEnd X j' := by
  intro h
  have h1 : (segPos X.TT j i).val = (segNext X.TT j').val := congrArg (fun x : X.TT => (x.val : ℕ)) h
  exact (pos_mem X.TT j i).2 (h1 ▸ (next_mem X.TT j').2)

/- English proof (translation)
The claim follows from `Nat.pow_le_pow_right hD.1.pos (dist_pos_lt X.TT j i).2.le`.
-/
theorem pd_le (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i ≤ X.p ^ segG X.TT j :=
  Nat.pow_le_pow_right hD.1.pos (dist_pos_lt X.TT j i).2.le

/- English proof (translation)
Establish `hp : 1 ≤ X.p` using `hD.1.one_lt.le`. Establish `hpG : ∀ j, X.p ^ segG X.TT j ≤ X.p ^ X.G'` using `fun j => Nat.pow_le_pow_right hp (hG j)`. Establish `h1 : 1 ≤ X.p ^ X.G'` using `Nat.one_le_pow _ _ hp`. Establish `hdl : ∀ j i, X.p ^ (segDists X.TT j).get i ≤ X.p ^ X.G'` using `fun j i => (pd_le hD j i).trans (hpG j)`. Establish `hso : ∀ j i, topStart X j ≠ topOdd X j i`.

Introduce `j i h`. Establish `h2 : (segStart X.TT j).val = (segPos X.TT j i).val` using `congrArg (fun x : X.TT => (x.val : ℕ)) h`. Conclude with `(pos_mem X.TT j i).2 (h2 ▸ (start_mem X.TT j).2)`. Break down `a with x | x | x | x` into its components or cases. Take `⟨-, hdG⟩` from `dist_pos_lt X.TT x.1 x.2`.

Establish `hPd : (X.seg C0 CE1 CE2 x.1).P X.p x.2 * X.p ^ (segDists X.TT x.1).get x.2 = X.p ^ segG X.TT x.1` using `by show X.p ^ (segG X.TT x.1 - (segDists X.TT x.1).get x.2) * _ = _`. Rewrite using `[← pow_add, Nat.sub_add_cancel hdG.le]`. Establish `hPle : (X.seg C0 CE1 CE2 x.1).P X.p x.2 ≤ X.p ^ segG X.TT x.1`. Rewrite using `[← hPd]`. Conclude with `Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)`.

Simplify using `only [dgMk, dgKS, dX]`. Use `split_ifs with ha hb hb`. Conclude with `absurd (ha.trans hb.symm) (by simp)`. Rewrite using `[mul_one, add_zero, hPd]`. Conclude with `hpG _`.

Rewrite using `[mul_zero, zero_add, mul_one]`. Conclude with `hPle.trans (hpG _)`. Simplify using the standard rewrite rules. Simplify using `only [dgMk, dgKW, dX] split_ifs with ha hb hb`. Conclude with `absurd (ha.trans hb.symm) (by simp [Ne.symm (hso x.1 x.2.1)])`.

Simplify using `using h1`. Simplify using `using hdl x.1 x.2.1`. Simplify using the standard rewrite rules. Simplify using `only [dgMk, dgKS, dX] split_ifs with ha hb hb`. Conclude with `absurd (ha.trans hb.symm) (by simp)`.

Simplify using `using hdl x.1 x.2`. Simplify using `using h1`. Simplify using the standard rewrite rules. Simplify using `only [dgMk, dgLoc, dX]`. Distinguish the cases in `hex : ∃ j0, (topStart X j0, true) = l`.

Take `⟨j0, hj0⟩` from `hex`. Rewrite using `[Finset.sum_eq_single j0]`. Rewrite using `[if_pos hj0, mul_one]`. Conclude with `(Nat.sub_le _ _).trans (hpG j0)`. Introduce `j _ hj`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Apply `topStart_inj X` to reduce the goal to its premises. Rewrite `h` using `[← hj0]`.

Conclude with `(Prod.mk.inj h).1`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j0) h`. Rewrite using `[Finset.sum_eq_zero]`. Conclude with `Nat.zero_le _`.

Introduce `j _`. Rewrite using `[if_neg (fun h => hex ⟨j, h⟩), mul_zero]`.
-/
theorem dgMk_le (hD : D1num X) (hG : ∀ j, segG X.TT j ≤ X.G') (C0 CE1 CE2 : ℝ) (a : IM X) (l : X.TT × Bool) :
    dgMk C0 CE1 CE2 X a l ≤ X.p ^ X.G' := by
  have hp : 1 ≤ X.p := hD.1.one_lt.le
  have hpG : ∀ j, X.p ^ segG X.TT j ≤ X.p ^ X.G' := fun j => Nat.pow_le_pow_right hp (hG j)
  have h1 : 1 ≤ X.p ^ X.G' := Nat.one_le_pow _ _ hp
  have hdl : ∀ j i, X.p ^ (segDists X.TT j).get i ≤ X.p ^ X.G' := fun j i => (pd_le hD j i).trans (hpG j)
  have hso : ∀ j i, topStart X j ≠ topOdd X j i := by
    intro j i h
    have h2 : (segStart X.TT j).val = (segPos X.TT j i).val := congrArg (fun x : X.TT => (x.val : ℕ)) h
    exact (pos_mem X.TT j i).2 (h2 ▸ (start_mem X.TT j).2)
  rcases a with x | x | x | x
  · obtain ⟨-, hdG⟩ := dist_pos_lt X.TT x.1 x.2
    have hPd : (X.seg C0 CE1 CE2 x.1).P X.p x.2 * X.p ^ (segDists X.TT x.1).get x.2 = X.p ^ segG X.TT x.1 := by
      show X.p ^ (segG X.TT x.1 - (segDists X.TT x.1).get x.2) * _ = _
      rw [← pow_add, Nat.sub_add_cancel hdG.le]
    have hPle : (X.seg C0 CE1 CE2 x.1).P X.p x.2 ≤ X.p ^ segG X.TT x.1 := by
      rw [← hPd]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · rw [mul_one, add_zero, hPd]
      exact hpG _
    · rw [mul_zero, zero_add, mul_one]
      exact hPle.trans (hpG _)
    · simp
  · simp only [dgMk, dgKW, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp [Ne.symm (hso x.1 x.2.1)])
    · simpa using h1
    · simpa using hdl x.1 x.2.1
    · simp
  · simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · simpa using hdl x.1 x.2
    · simpa using h1
    · simp
  · simp only [dgMk, dgLoc, dX]
    by_cases hex : ∃ j0, (topStart X j0, true) = l
    · obtain ⟨j0, hj0⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0, mul_one]
        exact (Nat.sub_le _ _).trans (hpG j0)
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        apply hj
        apply topStart_inj X
        rw [← hj0] at h
        exact (Prod.mk.inj h).1
      · intro h
        exact absurd (Finset.mem_univ j0) h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j _
        rw [if_neg (fun h => hex ⟨j, h⟩), mul_zero]

/- English proof (translation)
Apply the tactic sequence `rcases a with x | x | x | x <;>`. Simplify using `[dgMk, dgKS, dgKW, dgLoc, dX, topOdd_ne_endAny]`.
-/
theorem dgMk_Y (C0 CE1 CE2 : ℝ) (a : IM X) (j' : Fin (numSeg X.TT)) : dgMk C0 CE1 CE2 X a (topEnd X j', false) = 0 := by
  rcases a with x | x | x | x <;>
    simp [dgMk, dgKS, dgKW, dgLoc, dX, topOdd_ne_endAny]

end Deg

section Sums

variable {X : Loc}

/- English proof (translation)
Unfold `bMk`. Simplify using `only [Finsupp.single_add, smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]`. Use extensionality with `k`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]`. Distinguish the cases in `hs : ((topStart X j, true), (0 : Fin (X.m + 1))) = k`.

Substitute `hs` using the available equality. Simplify using `[Finset.mul_sum, mul_add, Finset.sum_add_distrib, Fin.succ_ne_zero]`. Apply the tactic sequence `try simp only [mul_comm, mul_left_comm]`. Apply the tactic sequence `try abel`. Apply the tactic sequence `try ring_nf`.

Apply the tactic sequence `simp only [hs, if_false, Finset.sum_const_zero, zero_add, add_zero] try simp only [mul_comm, mul_left_comm] try abel try ring_nf`.
-/
theorem bMk_eq (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    (∑ i : Fin (segS X.TT j), (β j).sg i • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j) +
        Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, (β j).rz i c.succ • ((Finsupp.single ((topOdd X j i, true), c.succ) 1 +
        Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), (β j).ry i 0 • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) +
        Finsupp.single ((topOdd X j i, false), 0) 1 : MonH X))) +
      Finsupp.single ((topStart X j, true), 0) (X.c * (X.m * (X.p ^ segG X.TT j - 1))))) = bMk C0 CE1 CE2 X β j := by
  unfold bMk
  simp only [Finsupp.single_add, smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  ext k
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  by_cases hs : ((topStart X j, true), (0 : Fin (X.m + 1))) = k
  · subst hs
    simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Fin.succ_ne_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf
  · simp only [hs, if_false, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf

/- English proof (translation)
Simplify using `only [← bMk_eq C0 CE1 CE2 β, Finset.sum_add_distrib]`. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]`. Use `congr 1`. Rewrite using `[Fintype.sum_sigma]`. Both sides reduce to the same expression.

Use `congr 1`. Rewrite using `[Fintype.sum_sigma]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.

Use `congr 1`. Rewrite using `[Fintype.sum_sigma]`. Both sides reduce to the same expression. Simplify using `only [multMk, aMk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_aMk (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) :
    ∑ a, multMk X β a • aMk C0 CE1 CE2 X a = ∑ j, bMk C0 CE1 CE2 X β j := by
  simp only [← bMk_eq C0 CE1 CE2 β, Finset.sum_add_distrib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  · simp only [multMk, aMk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring

end Sums

end Formalism.MainNotions.ColumnSystems.Pf
