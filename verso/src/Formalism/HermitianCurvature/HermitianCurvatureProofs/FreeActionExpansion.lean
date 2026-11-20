import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionUpdateSums

namespace Formalism.FourierDecayAlt.P.FreeActionExpansion

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix

section Ops

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Establish `h0 : (io (0 : A) : SlopeTestRemainingChoices S A) = 0` using `map_zero (Matrix.scalar (Ix S))`. Establish `h1 : (io (1 : A) : SlopeTestRemainingChoices S A) = 1` using `map_one (Matrix.scalar (Ix S))`. Establish `hn : (io (-1 : A) : SlopeTestRemainingChoices S A) = -1`. Rewrite using `[show (io (-1 : A) : SlopeTestRemainingChoices S A) = Matrix.scalar (Ix S) (-1 : A) from rfl, map_neg, map_one]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, lift0, h0, h1, hn]`.
-/
theorem J_lift : (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) = lift0 (Formalism.YangianSpanCharacter.T.J A) := by
  have h0 : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := map_zero (Matrix.scalar (Ix S))
  have h1 : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := map_one (Matrix.scalar (Ix S))
  have hn : (io (-1 : A) : SlopeTestRemainingChoices S A) = -1 := by
    rw [show (io (-1 : A) : SlopeTestRemainingChoices S A) = Matrix.scalar (Ix S) (-1 : A) from rfl, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, lift0, h0, h1, hn]

/- English proof (translation)
Use `Matrix.ext fun z z' => ?_` and prove the remaining obligations. Simplify using `only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Conclude with `(Algebra.commutes c (C z z')).symm`.
-/
theorem comm_io_alg (C : SlopeTestRemainingChoices S A) (c : ℂ) : Commute C (io (algebraMap ℂ A c)) := by
  refine Matrix.ext fun z z' => ?_
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (Algebra.commutes c (C z z')).symm

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩`. Conclude with `⟨0, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩`. Conclude with `⟨s, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩`. Conclude with `⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩`.
-/
theorem uinv_alg (s : ℂ) (i j : Fin 2) :
    ∃ c : ℂ, (Formalism.YangianSpanCharacter.T.Uinv (A := A) s) i j = algebraMap ℂ A c := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨0, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨s, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ C hC fun i j => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `uinv_alg (A := A) s i j`. Simplify using `only [lift0, Matrix.map_apply, hc]`. Conclude with `comm_io_alg C c`.
-/
theorem comm_ins_uinv {a : S} {C : SlopeTestRemainingChoices S A} (hC : FreeOf a C) (s : ℂ) :
    Commute C (ins a (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s))) := by
  refine Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ C hC fun i j => ?_
  obtain ⟨c, hc⟩ := uinv_alg (A := A) s i j
  simp only [lift0, Matrix.map_apply, hc]
  exact comm_io_alg C c

/- English proof (translation)
Introduce `_ _` and use `Commute.one_right _`.
-/
theorem freeOf_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _ _`. Conclude with `freeOf_one a`. Consider the case `cons l L ih`.

Introduce `hL ha`. Rewrite `ha` using `[List.map_cons, List.mem_cons, not_or]`. Establish `hpl : l.plus = true` using `hL l (by simp)`. Simplify using `only [JL, hpl, if_true, J_lift]`. Use `freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ?_ ha.2)` and prove the remaining obligations.

Conclude with `fun l' h => hL l' (by simp [h])`.
-/
theorem freeOf_JL (a : S) : ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true) →
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (JL L : SlopeTestRemainingChoices S A) := by
  intro L
  induction L with
  | nil => intro _ _; exact freeOf_one a
  | cons l L ih =>
    intro hL ha
    rw [List.map_cons, List.mem_cons, not_or] at ha
    have hpl : l.plus = true := hL l (by simp)
    simp only [JL, hpl, if_true, J_lift]
    refine freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ?_ ha.2)
    exact fun l' h => hL l' (by simp [h])

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _`. Conclude with `freeOf_one a`. Consider the case `cons l L ih`.

Introduce `ha`. Rewrite `ha` using `[List.map_cons, List.mem_cons, not_or]`. Simplify using `only [UUiw]`. Conclude with `freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ha.2)`.
-/
theorem freeOf_UUiw (a : S) (s : ℂ) : ∀ L : List (Letter ℂ S),
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (UUiw s L : SlopeTestRemainingChoices S A) := by
  intro L
  induction L with
  | nil => intro _; exact freeOf_one a
  | cons l L ih =>
    intro ha
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [UUiw]
    exact freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ha.2)

end Ops

section Vec

variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]

/- English proof (translation)
Establish `h : ∀ z', (ins a (lift0 M) : SlopeTestRemainingChoices S A) z z' = ∑ j, if z' = Function.update z a j then M (z a) j else 0`. Introduce `z'`. Unfold `ins lift0`. Simplify using `only [Matrix.sum_apply, Matrix.map_apply]`. Establish `hm : ∀ i j, (((eU a i j : SlopeTestRemainingChoices S A) * (io (M i j) : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A)) z z' = if z a = i ∧ z' = Function.update z a j then M i j else 0`.

Introduce `i j`. Simplify using `only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Formalism.FourierDecayAlt.P.Wd1.eU_apply, ite_mul, one_mul, zero_mul]`. Simplify using `only [hm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single (z a)]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[Ne.symm hi]`. Simplify using the standard rewrite rules.

Unfold `act`. Simplify using `only [h, Finset.sum_smul, ite_smul, zero_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem act_ins (a : S) (M : M2 A) (Ψ : Ix S → V) (z : Ix S) :
    act (ins a (lift0 M)) Ψ z = ∑ j, M (z a) j • Ψ (Function.update z a j) := by
  have h : ∀ z', (ins a (lift0 M) : SlopeTestRemainingChoices S A) z z' =
      ∑ j, if z' = Function.update z a j then M (z a) j else 0 := by
    intro z'
    unfold ins lift0
    simp only [Matrix.sum_apply, Matrix.map_apply]
    have hm : ∀ i j, (((eU a i j : SlopeTestRemainingChoices S A) * (io (M i j) : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A)) z z' =
        if z a = i ∧ z' = Function.update z a j then M i j else 0 := by
      intro i j
      simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Formalism.FourierDecayAlt.P.Wd1.eU_apply, ite_mul,
        one_mul, zero_mul]
    simp only [hm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (z a)]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  unfold act
  simp only [h, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _ u hu`. Conclude with `hx u hu`. Consider the case `cons l L ih`.

Introduce `ha u hu`. Rewrite `ha` using `[List.map_cons, List.mem_cons, not_or]`. Simplify using `only [letters, placeV]`. Rewrite using `[ih ha.2 _ (by rw [Function.update_of_ne ha.1]; exact hu), smul_zero]`.
-/
theorem letters_zero (P Q : A[X]) (a : S) (x : Ix S → V) (hx : ∀ u, u a ≠ 0 → x u = 0) :
    ∀ L : List (Letter ℂ S), a ∉ L.map Letter.intersection_update_fsHerm_neg_one → ∀ u, u a ≠ 0 → letters P Q L x u = 0 := by
  intro L
  induction L with
  | nil => intro _ u hu; exact hx u hu
  | cons l L ih =>
    intro ha u hu
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [letters, placeV]
    rw [ih ha.2 _ (by rw [Function.update_of_ne ha.1]; exact hu), smul_zero]

end Vec

section Main

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

/- English proof (translation)
The claim follows from `sum_position a (fun u => ρ.β (Ψ u) (Ψ' u))`.
-/
theorem pair_eq_sum_split_coord (a : S) (ρ : Rep A V) (Ψ Ψ' : Ix S → V) :
    pair ρ Ψ Ψ' = ∑ u, if u a = 0 then ρ.β (Ψ u) (Ψ' u) +
      ρ.β (Ψ (Function.update u a 1)) (Ψ' (Function.update u a 1)) else 0 :=
  sum_position a (fun u => ρ.β (Ψ u) (Ψ' u))

/- English proof (translation)
Establish `e : (P * (b + algebraMap ℂ A s * c)) • X = (P * b) • X + s • ((P * c) • X)`. Rewrite using `[mul_add, add_smul, ← mul_assoc P (algebraMap ℂ A s) c, ← Algebra.commutes s P, mul_assoc, mul_smul (algebraMap ℂ A s) (P * c) X, algebraMap_smul]`. Rewrite using `[e, act_add, act_smul]`.
-/
theorem act_lin (G : SlopeTestRemainingChoices S A) (X : Ix S → V) (P b c : A) (s : ℂ) :
    act G ((P * (b + algebraMap ℂ A s * c)) • X) = act G ((P * b) • X) + s • act G ((P * c) • X) := by
  have e : (P * (b + algebraMap ℂ A s * c)) • X = (P * b) • X + s • ((P * c) • X) := by
    rw [mul_add, add_smul, ← mul_assoc P (algebraMap ℂ A s) c, ← Algebra.commutes s P, mul_assoc,
      mul_smul (algebraMap ℂ A s) (P * c) X, algebraMap_smul]
  rw [e, act_add, act_smul]

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_ _ _ P P'`. Simplify using `only [JL, one_mul, List.nil_append, letters, List.map_nil, F7.Fw, hΞ, frm]`.

Consider the case `cons l L ih`. Introduce `hL hnd hw P P'`. Take `⟨hpl, him⟩` from `hL l (by simp)`. Establish `hL' : ∀ l' ∈ L, l'.plus = true ∧ l'.pt.im = 0` using `fun l' h => hL l' (by simp [h])`. Rewrite `hnd` using `[List.map_cons, List.nodup_cons]`.

Establish `hw' : ∀ l' ∈ L, l'.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one` using `fun l' h => hw l' (by simp [h])`. Establish `haw : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one` using `hw l (by simp)`. Establish `haL : l.intersection_update_fsHerm_neg_one ∉ L.map Letter.intersection_update_fsHerm_neg_one` using `hnd.1`. Establish `hpt : l.pt = (l.pt.re : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Establish `hJL` using `freeOf_JL (A := A) l.intersection_update_fsHerm_neg_one L (fun l' h => (hL' l' h).1) haL`.

Establish `hRR` using `(Formalism.FourierDecayAlt.P.word_free_of_unused_positions ℂ A S QQ w l.intersection_update_fsHerm_neg_one haw).1`. Establish `hUU` using `freeOf_UUiw (A := A) l.intersection_update_fsHerm_neg_one s (L ++ w) (by`. Rewrite using `[List.map_append, List.mem_append, not_or]`. Conclude with `⟨haL, haw⟩)`. Establish `hC : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * io f : SlopeTestRemainingChoices S A)` using `freeOf_mul (freeOf_mul hJL hRR) (freeOf_io l.intersection_update_fsHerm_neg_one f)`.

Establish `hG : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * Vw f s (L ++ w) : SlopeTestRemainingChoices S A)`. Unfold `Vw`. Conclude with `freeOf_mul (freeOf_mul hJL hRR) (freeOf_mul (freeOf_io l.intersection_update_fsHerm_neg_one f) hUU)`. Establish `hop : JL (l :: L) * RRw QQ w * Vw f s ((l :: L) ++ w) = ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A` using `A) s)) * (JL L * RRw QQ w * Vw f s (L ++ w))) := by`. Establish `hc` using `(comm_ins_uinv hC s).eq`.

Simplify using `only [JL, hpl, if_true, J_lift, Vw, List.cons_append, UUiw]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hop, act_mul, act_mul]`. Establish `hx0 : ∀ u, u l.intersection_update_fsHerm_neg_one ≠ 0 → x u = 0` using `fun u hu => hx u ⟨l.intersection_update_fsHerm_neg_one, haw, hu⟩`. Establish `hX` using `letters_zero vA vB l.intersection_update_fsHerm_neg_one x hx0 L haL`.

Establish `hX'` using `letters_zero vAv vBv l.intersection_update_fsHerm_neg_one x hx0 (L.map dl) (by`. Rewrite using `[List.map_map, show (Letter.intersection_update_fsHerm_neg_one ∘ dl : Letter ℂ S → S) = Letter.intersection_update_fsHerm_neg_one from` and apply the resulting hypothesis. Apply the tactic sequence `funext fun l' => by by_cases h : l'.plus <;> simp [dl, h]])`. Establish `hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩` using `by simp [dl, hpl]`. Establish `hΦ : P • letters vA vB (l :: L) x = fun u => (fun i : Fin 2 => P * (if i = 0 then evC vA l.pt else evC vB l.pt)) (u l.intersection_update_fsHerm_neg_one) • letters vA vB L x (Function.update u l.intersection_update_fsHerm_neg_one 0)`.

Use function extensionality and compare the values at `u`. Simplify using `only [letters, placeV, Pi.smul_apply, mul_smul]`. Establish `hΦ' : P' • letters vAv vBv ((l :: L).map dl) x = fun u => (P' * (if u l.intersection_update_fsHerm_neg_one = 0 then evC vAv (l.pt + 1) else evC vBv (l.pt + 1))) • letters vAv vBv (L.map dl) x (Function.update u l.intersection_update_fsHerm_neg_one 0)`. Use function extensionality and compare the values at `u`. Simplify using `only [List.map_cons, letters, hdl, placeV, Pi.smul_apply, mul_smul]`.

Rewrite using `[hΦ, hΦ']`. Use `set X := letters vA vB L x with hXdef`. Use `set X' := letters vAv vBv (L.map dl) x with hX'def`. Use `set G := JL L * RRw QQ w * Vw f s (L ++ w) with hGdef`. Use `set C : Fin 2 → A := fun i => P * (if i = 0 then evC vA l.pt else evC vB l.pt) with hCdef`.

Establish `h1 : act G (fun u => C (u l.intersection_update_fsHerm_neg_one) • X (Function.update u l.intersection_update_fsHerm_neg_one 0)) = fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0)` using `funext (act_place hG X hX C)`. Rewrite using `[h1]`. Establish `hv0 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 → act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A` using `A) s))) (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) u = s • act G (C 0 • X) u + act G (C 1 • X) u := by`. Introduce `u hu`. Rewrite using `[act_ins, Fin.sum_univ_two, act_ins, act_ins]`.

Simplify using `[hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu, algebraMap_smul]`. Establish `hv1 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 → act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A` using `A) s))) (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) (Function.update u l.intersection_update_fsHerm_neg_one 1) = -act G (C 0 • X) u := by`. Introduce `u hu`. Rewrite using `[act_ins, Fin.sum_univ_two, act_ins, act_ins]`. Simplify using `[hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu]`.

Establish `eA : F7.evR vA l.pt.re = evC vA l.pt` using `by unfold F7.evR evC; rw [← hpt]`. Establish `eB : F7.evR vB l.pt.re = evC vB l.pt` using `by unfold F7.evR evC; rw [← hpt]`. Establish `eAv : F7.evR vAv (l.pt.re + 1) = evC vAv (l.pt + 1)`. Unfold `F7.evR evC`. Rewrite using `[Complex.ofReal_add, Complex.ofReal_one, ← hpt]`.

Establish `eBv : F7.evR vBv (l.pt.re + 1) = evC vBv (l.pt + 1)`. Unfold `F7.evR evC`. Rewrite using `[Complex.ofReal_add, Complex.ofReal_one, ← hpt]`. Simplify using `only [List.map_cons, F7.Fw]`. Rewrite using `[← ih hL' hnd.2 hw', ← ih hL' hnd.2 hw', eA, eB, eAv, eBv, act_lin]`.

Rewrite using `[pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u l.intersection_update_fsHerm_neg_one = 0`. Rewrite using `[if_pos hu, if_pos hu, if_pos hu, hv0 u hu, hv1 u hu]`. Establish `hX'1 : X' (Function.update u l.intersection_update_fsHerm_neg_one 1) = 0` using `hX' _ (by simp)`.

Simplify using `only [Pi.smul_apply, hX'1, smul_zero, map_zero, add_zero, Function.update_self, Function.update_idem, update_zero_of _ u hu, hu, if_true, hCdef]`. Simplify using `only [show ((1 : Fin 2) = 0) = False from by decide, if_false, Pi.add_apply, Pi.smul_apply, map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hu, if_neg hu, if_neg hu, sub_zero]`.
-/
theorem expand (ρ : Rep A V) (QQ : ℂ → M2 A) (f : A) (s : ℂ) (w : List (Letter ℂ S))
    (vA vB vAv vBv : A[X]) (x : Ix S → V) (Ξ : F7.Sesq (Ix S → V))
    (hΞ : ∀ X X', Ξ X X' = frm ρ (RRw QQ w * Vw f s w) X X') (hx : SupportedOnUsedSlots w x) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ l.pt.im = 0) → (L.map Letter.intersection_update_fsHerm_neg_one).Nodup →
      (∀ l ∈ L, l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) → ∀ P P' : A,
      pair ρ (act (JL L * RRw QQ w * Vw f s (L ++ w)) (P • letters vA vB L x))
          (P' • letters vAv vBv (L.map dl) x) =
        F7.Fw Ξ x x (L.map fun l => ((⟨vA, vB, vAv, vBv, s⟩ : F7.Dat A), l.pt.re)) P P' := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ P P'
    simp only [JL, one_mul, List.nil_append, letters, List.map_nil, F7.Fw, hΞ, frm]
  | cons l L ih =>
    intro hL hnd hw P P'
    obtain ⟨hpl, him⟩ := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true ∧ l'.pt.im = 0 := fun l' h => hL l' (by simp [h])
    rw [List.map_cons, List.nodup_cons] at hnd
    have hw' : ∀ l' ∈ L, l'.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one := fun l' h => hw l' (by simp [h])
    have haw : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one := hw l (by simp)
    have haL : l.intersection_update_fsHerm_neg_one ∉ L.map Letter.intersection_update_fsHerm_neg_one := hnd.1
    have hpt : l.pt = (l.pt.re : ℂ) := Complex.ext (by simp) (by simp [him])

    have hJL := freeOf_JL (A := A) l.intersection_update_fsHerm_neg_one L (fun l' h => (hL' l' h).1) haL
    have hRR := (Formalism.FourierDecayAlt.P.word_free_of_unused_positions ℂ A S QQ w l.intersection_update_fsHerm_neg_one haw).1
    have hUU := freeOf_UUiw (A := A) l.intersection_update_fsHerm_neg_one s (L ++ w) (by
      rw [List.map_append, List.mem_append, not_or]; exact ⟨haL, haw⟩)
    have hC : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * io f : SlopeTestRemainingChoices S A) :=
      freeOf_mul (freeOf_mul hJL hRR) (freeOf_io l.intersection_update_fsHerm_neg_one f)
    have hG : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * Vw f s (L ++ w) : SlopeTestRemainingChoices S A) := by
      unfold Vw; exact freeOf_mul (freeOf_mul hJL hRR) (freeOf_mul (freeOf_io l.intersection_update_fsHerm_neg_one f) hUU)
    have hop : JL (l :: L) * RRw QQ w * Vw f s ((l :: L) ++ w) =
        ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)) *
          (JL L * RRw QQ w * Vw f s (L ++ w))) := by
      have hc := (comm_ins_uinv hC s).eq
      simp only [JL, hpl, if_true, J_lift, Vw, List.cons_append, UUiw]
      calc ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * JL L * RRw QQ w *
            (io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) * UUiw s (L ++ w)))
          = ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * ((JL L * RRw QQ w * io f) *
              ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) * UUiw s (L ++ w)) := by simp only [mul_assoc]
        _ = ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) *
              (JL L * RRw QQ w * io f) * UUiw s (L ++ w)) := by rw [hc]
        _ = _ := by simp only [mul_assoc]
    rw [hop, act_mul, act_mul]

    have hx0 : ∀ u, u l.intersection_update_fsHerm_neg_one ≠ 0 → x u = 0 := fun u hu => hx u ⟨l.intersection_update_fsHerm_neg_one, haw, hu⟩
    have hX := letters_zero vA vB l.intersection_update_fsHerm_neg_one x hx0 L haL
    have hX' := letters_zero vAv vBv l.intersection_update_fsHerm_neg_one x hx0 (L.map dl) (by
      rwa [List.map_map, show (Letter.intersection_update_fsHerm_neg_one ∘ dl : Letter ℂ S → S) = Letter.intersection_update_fsHerm_neg_one from
        funext fun l' => by by_cases h : l'.plus <;> simp [dl, h]])
    have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hpl]
    have hΦ : P • letters vA vB (l :: L) x = fun u =>
        (fun i : Fin 2 => P * (if i = 0 then evC vA l.pt else evC vB l.pt)) (u l.intersection_update_fsHerm_neg_one) •
          letters vA vB L x (Function.update u l.intersection_update_fsHerm_neg_one 0) := by
      funext u
      simp only [letters, placeV, Pi.smul_apply, mul_smul]
    have hΦ' : P' • letters vAv vBv ((l :: L).map dl) x = fun u =>
        (P' * (if u l.intersection_update_fsHerm_neg_one = 0 then evC vAv (l.pt + 1) else evC vBv (l.pt + 1))) •
          letters vAv vBv (L.map dl) x (Function.update u l.intersection_update_fsHerm_neg_one 0) := by
      funext u
      simp only [List.map_cons, letters, hdl, placeV, Pi.smul_apply, mul_smul]
    rw [hΦ, hΦ']
    set X := letters vA vB L x with hXdef
    set X' := letters vAv vBv (L.map dl) x with hX'def
    set G := JL L * RRw QQ w * Vw f s (L ++ w) with hGdef
    set C : Fin 2 → A := fun i => P * (if i = 0 then evC vA l.pt else evC vB l.pt) with hCdef
    have h1 : act G (fun u => C (u l.intersection_update_fsHerm_neg_one) • X (Function.update u l.intersection_update_fsHerm_neg_one 0)) =
        fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0) := funext (act_place hG X hX C)
    rw [h1]
    have hv0 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 →
        act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)))
          (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) u =
        s • act G (C 0 • X) u + act G (C 1 • X) u := by
      intro u hu
      rw [act_ins, Fin.sum_univ_two, act_ins, act_ins]
      simp [hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu, algebraMap_smul]
    have hv1 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 →
        act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)))
          (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) (Function.update u l.intersection_update_fsHerm_neg_one 1) =
        -act G (C 0 • X) u := by
      intro u hu
      rw [act_ins, Fin.sum_univ_two, act_ins, act_ins]
      simp [hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu]
    have eA : F7.evR vA l.pt.re = evC vA l.pt := by unfold F7.evR evC; rw [← hpt]
    have eB : F7.evR vB l.pt.re = evC vB l.pt := by unfold F7.evR evC; rw [← hpt]
    have eAv : F7.evR vAv (l.pt.re + 1) = evC vAv (l.pt + 1) := by
      unfold F7.evR evC; rw [Complex.ofReal_add, Complex.ofReal_one, ← hpt]
    have eBv : F7.evR vBv (l.pt.re + 1) = evC vBv (l.pt + 1) := by
      unfold F7.evR evC; rw [Complex.ofReal_add, Complex.ofReal_one, ← hpt]
    simp only [List.map_cons, F7.Fw]
    rw [← ih hL' hnd.2 hw', ← ih hL' hnd.2 hw', eA, eB, eAv, eBv, act_lin]
    rw [pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u l.intersection_update_fsHerm_neg_one = 0
    · rw [if_pos hu, if_pos hu, if_pos hu, hv0 u hu, hv1 u hu]
      have hX'1 : X' (Function.update u l.intersection_update_fsHerm_neg_one 1) = 0 := hX' _ (by simp)
      simp only [Pi.smul_apply, hX'1, smul_zero, map_zero, add_zero, Function.update_self,
        Function.update_idem, update_zero_of _ u hu, hu, if_true, hCdef]
      simp only [show ((1 : Fin 2) = 0) = False from by decide, if_false, Pi.add_apply, Pi.smul_apply, map_add, map_neg,
        map_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg hu, if_neg hu, if_neg hu, sub_zero]

end Main

end Formalism.FourierDecayAlt.P.FreeActionExpansion
