import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section H

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

def hTop (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) : RHH O X := hKey O (X.m + 1) (x, true) (x, false)

def dgH {X : Loc} (x : X.TT) : X.TT × Bool → ℕ := fun l => dX (x, true) l + dX (x, false) l

def EhatT (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) (P : ℕ) : RHH O X :=
  MvPolynomial.X ((x, true), 0) ^ P * MvPolynomial.X ((x, false), 0) ^ P +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) ^ P * MvPolynomial.X ((x, false), c.succ) ^ P

/- English proof (translation)
Rewrite using `[hTop, hKey, Fin.sum_univ_succ]`.
-/
theorem hTop_eq (x : X.TT) : hTop O X x = MvPolynomial.X ((x, true), 0) * MvPolynomial.X ((x, false), 0) +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) * MvPolynomial.X ((x, false), c.succ) := by
  rw [hTop, hKey, Fin.sum_univ_succ]

/- English proof (translation)
Rewrite using `[EhatT, hTop_eq]`. Simplify using `only [pow_one]`.
-/
theorem EhatT_one (x : X.TT) : EhatT O X x 1 = hTop O X x := by
  rw [EhatT, hTop_eq]
  simp only [pow_one]

/- English proof (translation)
Rewrite using `[show (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P = monomial (P • (Finsupp.single ((x, true), a) 1 + Finsupp.single ((x, false), a) 1)) 1 by`. Rewrite using `[MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_pow, one_mul, one_pow]]`. Rewrite using `[Pol, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm'` using `support_monomial_subset hm`.

Rewrite `hm'` using `[Finset.mem_singleton]`. Substitute `hm'` using the available equality. Introduce `l`. Simplify using `only [multideg, dgH, dX, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]`. Apply the tactic sequence `congr 1 <;> split_ifs with h <;> simp [h]`.
-/
private theorem X_true_mul_X_false_pow_mem_Pol (x : X.TT) (a : Fin (X.m + 1)) (P : ℕ) :
    (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P ∈
      Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (fun l => P * dgH x l) := by
  classical
  rw [show (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P =
      monomial (P • (Finsupp.single ((x, true), a) 1 + Finsupp.single ((x, false), a) 1)) 1 by
    rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_pow, one_mul, one_pow]]
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro l
  simp only [multideg, dgH, dX, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  congr 1 <;> split_ifs with h <;> simp [h]

/- English proof (translation)
Establish `e : hTop O X x = ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ 1`. Rewrite using `[hTop_eq, Fin.sum_univ_succ]`. Simplify using `only [pow_one]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ (fun a _ => ?_)` and prove the remaining obligations.

Establish `h` using `X_true_mul_X_false_pow_mem_Pol (O := O) x a 1`. Simplify using `only [one_mul] at h`. Conclude with `h`.
-/
theorem hTop_pol (x : X.TT) : hTop O X x ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH x) := by
  have e : hTop O X x = ∑ a : Fin (X.m + 1),
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ 1 := by
    rw [hTop_eq, Fin.sum_univ_succ]
    simp only [pow_one]
  rw [e]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  have h := X_true_mul_X_false_pow_mem_Pol (O := O) x a 1
  simp only [one_mul] at h
  exact h

/- English proof (translation)
Rewrite using `[hTop_eq]`. Establish `hpair : ∀ a : Fin (X.m + 1), IsWeightedHomogeneous (wN X) (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) 1`. Introduce `a`. Establish `h1` using `(isWeightedHomogeneous_X (KK O) (wN X) ((x, true), a)).mul (isWeightedHomogeneous_X (KK O) (wN X) ((x, false), a))`. Establish `hw : wN X ((x, true), a) + wN X ((x, false), a) = 1`.

Break down `Nat.lt_or_ge a.val 1 with h | h` into its components or cases. Establish `h' : ¬ 1 ≤ a.val` using `by omega`. Simplify using `[wN, h, h']`. Establish `h' : ¬ a.val < 1` using `by omega`. Simplify using `[wN, h, h']`.

Rewrite `h1` using `[hw]`. Then use the resulting hypothesis. Use `(hpair 0).add (IsWeightedHomogeneous.sum _ _ _ (fun c _ => hpair c.succ))` and prove the remaining obligations.
-/
theorem hTop_nd (x : X.TT) : IsWeightedHomogeneous (wN X) (hTop O X x) 1 := by
  rw [hTop_eq]
  have hpair : ∀ a : Fin (X.m + 1), IsWeightedHomogeneous (wN X)
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) 1 := by
    intro a
    have h1 := (isWeightedHomogeneous_X (KK O) (wN X) ((x, true), a)).mul
      (isWeightedHomogeneous_X (KK O) (wN X) ((x, false), a))
    have hw : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
      rcases Nat.lt_or_ge a.val 1 with h | h
      · have h' : ¬ 1 ≤ a.val := by omega
        simp [wN, h, h']
      · have h' : ¬ a.val < 1 := by omega
        simp [wN, h, h']
    rwa [hw] at h1
  refine (hpair 0).add (IsWeightedHomogeneous.sum _ _ _ (fun c _ => hpair c.succ))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∀ m, ∃ a : O, (MvPolynomial.X v : RHH O X).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a)`. Introduce `m`. Rewrite using `[MvPolynomial.coeff_X']`. Use `split_ifs`. Conclude with `⟨1, by simp⟩`.

Conclude with `⟨0, by simp⟩`.
-/
private theorem X_mem_intSub' (v : VarH X) : (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
  classical
  change ∀ m, ∃ a : O, (MvPolynomial.X v : RHH O X).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a)
  intro m
  rw [MvPolynomial.coeff_X']
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/- English proof (translation)
Rewrite using `[hTop_eq]`. Conclude with `add_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) (sum_mem fun c _ => mul_mem (X_mem_intSub' _) (X_mem_intSub' _))`.
-/
theorem hTop_int (x : X.TT) : hTop O X x ∈ intSub O (VarH X) := by
  rw [hTop_eq]
  exact add_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _))
    (sum_mem fun c _ => mul_mem (X_mem_intSub' _) (X_mem_intSub' _))

/- English proof (translation)
Establish `h` using `hTop_int (O := O) x`. Express the relevant statement in the definitionally equal form `∀ m, ∃ a : O, (hTop O X x).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a) at h`. Introduce `m`. Take `⟨a, ha⟩` from `h m`. Conclude with `⟨a, by rw [ha, pow_zero, one_mul]⟩`.
-/
theorem hTop_inA (x : X.TT) : InA (hTop O X x) := by
  have h := hTop_int (O := O) x
  change ∀ m, ∃ a : O, (hTop O X x).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a) at h
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [ha, pow_zero, one_mul]⟩

/- English proof (translation)
Rewrite using `[identity_lift_normal_homog w (hTop_nd x), pow_one]`.
-/
theorem hTop_lift (w : O) (x : X.TT) : lift1 X O w (hTop O X x) = w • hTop O X x := by
  rw [identity_lift_normal_homog w (hTop_nd x), pow_one]

/- English proof (translation)
Conclude with `hook_key_order_ge_one w (hhLetters X.TT) 1 g hg (x, true) (x, false) rfl rfl rfl`.
-/
theorem hTop_ord (w : O) (x : X.TT) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (hTop O X x) 1 := by
  exact hook_key_order_ge_one w (hhLetters X.TT) 1 g hg (x, true) (x, false) rfl rfl rfl

/- English proof (translation)
The claim follows from `IsFac.of_exact (e := 1) (r := 0) (hTop_inA x) (fun g hg => hTop_ord w x g hg) le_rfl (hTop_inA x) ((inA_iff_wj w).2 (wjSub w 0).zero_mem) (by have := hTop_lift w x rw [smul_zero, add_zero, pow_one] exact this) sgHom := ndHom_iff.2 (hTop_nd x) liftPol := identity_lift_mem_Pol _ (h …`.
-/
theorem softOK_hTop (w : O) (x : X.TT) : SoftOK w (hTop O X x) 1 (hTop O X x) (dgH x) where
  fac := IsFac.of_exact (e := 1) (r := 0) (hTop_inA x) (fun g hg => hTop_ord w x g hg) le_rfl (hTop_inA x)
    ((inA_iff_wj w).2 (wjSub w 0).zero_mem) (by
      have := hTop_lift w x
      rw [smul_zero, add_zero, pow_one]
      exact this)
  sgHom := ndHom_iff.2 (hTop_nd x)
  liftPol := identity_lift_mem_Pol _ (hTop_pol x)
  sgPol := hTop_pol x

/- English proof (translation)
Rewrite using `[EhatT, Fin.sum_univ_succ]`. Simplify using `only [mul_pow]`.
-/
theorem EhatT_eq_sum (x : X.TT) (P : ℕ) :
    EhatT O X x P = ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P := by
  rw [EhatT, Fin.sum_univ_succ]
  simp only [mul_pow]

/- English proof (translation)
Rewrite using `[EhatT_eq_sum]`. Conclude with `sum_mem fun a _ => pow_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) _`.
-/
theorem EhatT_int (x : X.TT) (P : ℕ) : EhatT O X x P ∈ intSub O (VarH X) := by
  rw [EhatT_eq_sum]
  exact sum_mem fun a _ => pow_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) _

/- English proof (translation)
Rewrite using `[EhatT_eq_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)` and prove the remaining obligations. Establish `h1` using `((isWeightedHomogeneous_X (KK O) wt ((x, true), a)).mul (isWeightedHomogeneous_X (KK O) wt ((x, false), a))).pow P`. Rewrite `h1` using `[h a, smul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem EhatT_wh (wt : VarH X → ℕ) (n : ℕ) (x : X.TT) (P : ℕ) (h : ∀ a, wt ((x, true), a) + wt ((x, false), a) = n) :
    IsWeightedHomogeneous wt (EhatT O X x P) (P * n) := by
  rw [EhatT_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  have h1 := ((isWeightedHomogeneous_X (KK O) wt ((x, true), a)).mul
    (isWeightedHomogeneous_X (KK O) wt ((x, false), a))).pow P
  rwa [h a, smul_eq_mul] at h1

/- English proof (translation)
Use `set D : MvPolynomial (VarH X) O := (∑ a : Fin (X.m + 1), MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) - ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) with hDdef`. Establish `hD : hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e) = MvPolynomial.map (algebraMap O (KK O)) D`. Rewrite using `[EhatT_eq_sum, ← EhatT_one, EhatT_eq_sum, hDdef]`. Simplify using `only [map_sub, map_pow, map_sum, map_mul, map_X, pow_one]`. Rewrite using `[hD]`.

Apply `Formalism.MainNotions.G.WittFrameLocaliserOrders.residue_zero_mem_order_one S` to reduce the goal to its premises. Establish `hp0 : ((X.p : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `S.p_mem`. Use `haveI : CharP (IsLocalRing.ResidueField O) X.p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0`.

Rewrite using `[hDdef]`. Simplify using `only [map_sub, map_pow, map_sum, map_mul, map_X]`. Rewrite using `[sum_pow_char_pow, sub_self]`.
-/
theorem hpow_congr (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    InWj S.w (hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e)) 1 := by
  classical
  set D : MvPolynomial (VarH X) O :=
    (∑ a : Fin (X.m + 1), MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) -
      ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) with hDdef
  have hD : hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e) = MvPolynomial.map (algebraMap O (KK O)) D := by
    rw [EhatT_eq_sum, ← EhatT_one, EhatT_eq_sum, hDdef]
    simp only [map_sub, map_pow, map_sum, map_mul, map_X, pow_one]
  rw [hD]
  apply Formalism.MainNotions.G.WittFrameLocaliserOrders.residue_zero_mem_order_one S
  have hp0 : ((X.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  haveI : CharP (IsLocalRing.ResidueField O) X.p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  rw [hDdef]
  simp only [map_sub, map_pow, map_sum, map_mul, map_X]
  rw [sum_pow_char_pow, sub_self]

/- English proof (translation)
Use `((softOK_hTop S.w x).pow (X.p ^ e)).fac` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this.congr_sg (hpow_congr S hS x e) ((mem_intSub O _).1 (EhatT_int x _))`. Use `sgHom := ndHom_iff.2 (by`. Use `EhatT_wh (O := O) (wN X) 1 x (X.p ^ e) (wN_pair x)` as an intermediate fact.

Rewrite using `[mul_one] at this)` and apply the resulting hypothesis. Use `liftPol := ((softOK_hTop S.w x).pow (X.p ^ e)).liftPol`. Use `sgPol := mem_Pol_iff.2 fun l => EhatT_wh (wL X l) _ x _ fun _ => rfl`.
-/
theorem softH (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    SoftOK S.w (hTop O X x ^ (X.p ^ e)) (X.p ^ e) (EhatT O X x (X.p ^ e)) (fun l => X.p ^ e * dgH x l) where
  fac := by
    have := ((softOK_hTop S.w x).pow (X.p ^ e)).fac
    rw [mul_one] at this
    exact this.congr_sg (hpow_congr S hS x e) ((mem_intSub O _).1 (EhatT_int x _))
  sgHom := ndHom_iff.2 (by
    have := EhatT_wh (O := O) (wN X) 1 x (X.p ^ e) (wN_pair x)
    rwa [mul_one] at this)
  liftPol := ((softOK_hTop S.w x).pow (X.p ^ e)).liftPol
  sgPol := mem_Pol_iff.2 fun l => EhatT_wh (wL X l) _ x _ fun _ => rfl

/- English proof (translation)
Conclude with `softH S hS (topOdd X j i) _`.
-/
theorem softHseg (S : UniformizedDVR X.p O) (hS : S.SqP) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (hTop O X (topOdd X j i) ^ ((X.seg C0 CE1 CE2 j).P X.p i)) ((X.seg C0 CE1 CE2 j).P X.p i)
      (EhatT O X (topOdd X j i) ((X.seg C0 CE1 CE2 j).P X.p i))
      (fun l => (X.seg C0 CE1 CE2 j).P X.p i * dgH (topOdd X j i) l) := by
  exact softH S hS (topOdd X j i) _

/- English proof (translation)
Rewrite using `[sgKS, mul_pow, ← pow_mul]`.
-/
theorem sgKS_pow (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (P : ℕ) :
    sgKS O X j i ^ P = MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i * P) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ P := by
  rw [sgKS, mul_pow, ← pow_mul]

end H

end Formalism.MainNotions.ColumnSystems.Pf
