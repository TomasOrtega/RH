import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpTanP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedHomOfFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Core

variable {H E : Type} [Group H] [Field E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `adj X = -X ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h a b`. Use `congrFun (congrFun h a) b` as an intermediate fact. Rewrite `this` using `[adj_apply, Matrix.neg_apply]`. Then use the resulting hypothesis.

Introduce `h`. Use extensionality with `a b`. Rewrite using `[adj_apply, Matrix.neg_apply]`. Conclude with `h a b`.
-/
private theorem mem_sp4_iff {X : M4 E} : X ∈ sp4 E ↔ ∀ a b, (sgn a * sgn b) • X b.rev a.rev = -X a b := by
  change adj X = -X ↔ _
  constructor
  · intro h a b
    have := congrFun (congrFun h a) b
    rwa [adj_apply, Matrix.neg_apply] at this
  · intro h
    ext a b
    rw [adj_apply, Matrix.neg_apply]
    exact h a b

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, TrivSqZeroExt.snd_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`.
-/
private theorem dualNumber_matrix_mul_snd_apply (P Q : Matrix (Fin 4) (Fin 4) (DualNumber E)) (a b : Fin 4) :
    ((P * Q) a b).snd = ∑ c, ((P a c).fst * (Q c b).snd + (P a c).snd * (Q c b).fst) := by
  rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, TrivSqZeroExt.fst_sum]`. Both sides reduce to the same expression.
-/
private theorem dualNumber_matrix_mul_fst_apply (P Q : Matrix (Fin 4) (Fin 4) (DualNumber E)) (a b : Fin 4) :
    ((P * Q) a b).fst = ∑ c, (P a c).fst * (Q c b).fst := by
  rw [Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩ g h a b`. Establish `key` using `congrArg (fun M => (M a b).snd) (r.map_mul g h)`. Simplify using `only [dualNumber_matrix_mul_snd_apply, hr, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Units.val_mul] at key`. Establish `h1` using `Units.ne_zero (χ b g)`.

Establish `h2` using `Units.ne_zero (χ b h)`. Clear the denominators using the available nonvanishing facts. Apply `mul_right_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `key`. Introduce `hc`.

Establish `h1 : ∀ a b, γ 1 a b = 0`. Introduce `a b`. Use `hc 1 1 a b` as an intermediate fact. Simplify using `using this`. Use `⟨{ toFun := fun g => Matrix.of fun a b => (⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩ : DualNumber E) map_one' := ?_ map_mul' := ?_ }, fun g a b => rfl⟩` and prove the remaining obligations.

Use `Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Use `show (if a = b then ((χ a 1 : Eˣ) : E) else 0) = _`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[Matrix.one_apply_eq]`.

Simplify using `[Matrix.one_apply_ne hab, hab]`. Use `show γ 1 a b * ((χ b 1 : Eˣ) : E) = _`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[Matrix.one_apply_eq, h1]`.

Simplify using `[Matrix.one_apply_ne hab, h1]`. Introduce `g h`. Use `Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[dualNumber_matrix_mul_fst_apply] show (if a = b then ((χ a (g * h) : Eˣ) : E) else 0) = ∑ c, (if a = c then ((χ a g : Eˣ) : E) else 0) * (if c = b then ((χ c h : Eˣ) : E) else 0)`. Simplify using `only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Units.val_mul]`.

Use `split_ifs with hab`. Substitute `hab` using the available equality. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[dualNumber_matrix_mul_snd_apply] show γ (g * h) a b * ((χ b (g * h) : Eˣ) : E) = ∑ c, ((if a = c then ((χ a g : Eˣ) : E) else 0) * (γ h c b * ((χ b h : Eˣ) : E)) + (γ g a c * ((χ c g : Eˣ) : E)) * (if c = b then ((χ c h : Eˣ) : E) else 0))`.

Simplify using `only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Units.val_mul, hc g h a b]`. Establish `h2` using `Units.ne_zero (χ b g)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hom_iff (χ : Fin 4 → H →* Eˣ) (γ : H → M4 E) :
    (∃ r : H →* M4 (DualNumber E), ∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) ↔
      ∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b := by
  constructor
  · rintro ⟨r, hr⟩ g h a b
    have key := congrArg (fun M => (M a b).snd) (r.map_mul g h)
    simp only [dualNumber_matrix_mul_snd_apply, hr, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul,
      Units.val_mul] at key
    have h1 := Units.ne_zero (χ b g)
    have h2 := Units.ne_zero (χ b h)
    field_simp
    apply mul_right_cancel₀ h2
    linear_combination key
  · intro hc
    have h1 : ∀ a b, γ 1 a b = 0 := by
      intro a b
      have := hc 1 1 a b
      simpa using this
    refine ⟨{ toFun := fun g => Matrix.of fun a b => (⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩ : DualNumber E)
              map_one' := ?_
              map_mul' := ?_ }, fun g a b => rfl⟩
    · refine Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_
      · show (if a = b then ((χ a 1 : Eˣ) : E) else 0) = _
        by_cases hab : a = b
        · subst hab
          simp [Matrix.one_apply_eq]
        · simp [Matrix.one_apply_ne hab, hab]
      · show γ 1 a b * ((χ b 1 : Eˣ) : E) = _
        by_cases hab : a = b
        · subst hab
          simp [Matrix.one_apply_eq, h1]
        · simp [Matrix.one_apply_ne hab, h1]
    · intro g h
      refine Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_
      · rw [dualNumber_matrix_mul_fst_apply]
        show (if a = b then ((χ a (g * h) : Eˣ) : E) else 0) =
          ∑ c, (if a = c then ((χ a g : Eˣ) : E) else 0) * (if c = b then ((χ c h : Eˣ) : E) else 0)
        simp only [ite_mul, mul_ite, zero_mul, mul_zero,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Units.val_mul]
        split_ifs with hab
        · subst hab
          rfl
        · rfl
      · rw [dualNumber_matrix_mul_snd_apply]
        show γ (g * h) a b * ((χ b (g * h) : Eˣ) : E) =
          ∑ c, ((if a = c then ((χ a g : Eˣ) : E) else 0) * (γ h c b * ((χ b h : Eˣ) : E)) +
            (γ g a c * ((χ c g : Eˣ) : E)) * (if c = b then ((χ c h : Eˣ) : E) else 0))
        simp only [ite_mul, mul_ite, zero_mul, mul_zero,
          Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul,
          Units.val_mul, hc g h a b]
        have h2 := Units.ne_zero (χ b g)
        field_simp
        ring

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_fib : ∀ a b a' b' : Fin 4, a ≠ b → wt a' b' = wt a b →
    (a' = a ∧ b' = b) ∨ (a' = b.rev ∧ b' = a.rev) := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_root : ∀ j ∈ wts, j ≠ 0 → ∃ a b : Fin 4, a ≠ b ∧ wt a b = j := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem sgn_sq : ∀ a b : Fin 4, sgn a * sgn b * (sgn a * sgn b) = 1 := by decide

/- English proof (translation)
Use `⟨Matrix.of fun i j => if i = a ∧ j = b then (1 : E) else if i = b.rev ∧ j = a.rev then -((sgn a * sgn b : ℤ) : E) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [mem_sp4_iff] fin_cases a <;> fin_cases b <;> intro a' b' <;> fin_cases a' <;> fin_cases b' <;> simp [sgn] <;> norm_num`. Simplify using the standard rewrite rules. Introduce `a' b' h`. Establish `h1 : ¬ (a' = a ∧ b' = b)`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h rfl`. Establish `h2 : ¬ (a' = b.rev ∧ b' = a.rev)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h (wt_rev a b)`.

Simplify using `[h1, h2]`.
-/
private theorem ex_root [CharZero E] (a b : Fin 4) :
    ∃ X ∈ sp4 E, X a b ≠ 0 ∧ ∀ a' b', wt a' b' ≠ wt a b → X a' b' = 0 := by
  refine ⟨Matrix.of fun i j => if i = a ∧ j = b then (1 : E) else if i = b.rev ∧ j = a.rev then -((sgn a * sgn b : ℤ) : E) else 0, ?_, ?_, ?_⟩
  · rw [mem_sp4_iff]
    fin_cases a <;> fin_cases b <;> intro a' b' <;> fin_cases a' <;> fin_cases b' <;> simp [sgn] <;> norm_num
  · simp
  · intro a' b' h
    have h1 : ¬ (a' = a ∧ b' = b) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    have h2 : ¬ (a' = b.rev ∧ b' = a.rev) := by
      rintro ⟨rfl, rfl⟩
      exact h (wt_rev a b)
    simp [h1, h2]

variable [TopologicalSpace H] [TopologicalSpace E] [IsTopologicalRing E]

private def Q (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (j : ℤ × ℤ) (γ : H → M4 E) : Prop :=
  (∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b) ∧ (∀ g, γ g ∈ sp4 E) ∧
    (∃ X ∈ sp4 E, ∀ g a b, a ≠ b → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧ (∀ s, I s → ∀ a, γ s a a = 0) ∧
      (∀ a b, Continuous fun g => γ g a b) ∧ ∀ g a b, wt a b ≠ j → γ g a b = 0

/- English proof (translation)
Take `⟨X0, hX0, hX0ab, hX0w⟩` from `ex_root (E := E) a b`. Establish `hwab : wt a b ≠ 0` using `fun h => hab ((wt_eq_zero a b).1 h)`. Take `⟨v0, hv0⟩ : ∃ v0 : H → M4 E, ∀ g a' b', v0 g a' b' = if a' = b' then 0 else (1 - (χ a' g : E) / χ b' g) * X0 a' b'` from `⟨fun g => Matrix.of fun a' b' => if a' = b' then 0 else (1 - (χ a' g : E) / χ b' g) * X0 a' b', fun _ _ _ => rfl⟩`. Establish `hQ : Q χ I (wt a b) v0`. Unfold `Q`.

Use `⟨?_, ?_, ⟨X0, hX0, fun g a' b' h => by rw [hv0, if_neg h]⟩, fun s _ a' => by rw [hv0, if_pos rfl], ?_, ?_⟩` and prove the remaining obligations. Introduce `g h a' b'`. Rewrite using `[hv0, hv0, hv0]`. Distinguish the cases in `h' : a' = b'`. Simplify using `[h']`.

Simplify using `only [if_neg h', map_mul, Units.val_mul]`. Establish `h1` using `Units.ne_zero (χ b' g)`. Establish `h2` using `Units.ne_zero (χ b' h)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Introduce `g`. Rewrite using `[mem_sp4_iff]`. Introduce `a' b'`. Rewrite using `[hv0, hv0]`. Distinguish the cases in `h' : a' = b'`.

Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Establish `h'' : b'.rev ≠ a'.rev` using `fun e => h' (Fin.rev_injective e).symm`. Rewrite using `[if_neg h', if_neg h'']`. Establish `hr : (χ b'.rev g : E) / χ a'.rev g = (χ a' g : E) / χ b' g`.

Establish `e1` using `hθ g a'`. Establish `e2` using `hθ g b'`. Establish `n1` using `Units.ne_zero (χ a'.rev g)`. Establish `n2` using `Units.ne_zero (χ b' g)`. Rewrite using `[div_eq_div_iff n1 n2]`.

Take the linear combination `e2 - e1`. Establish `hs` using `(mem_sp4_iff.1 hX0) a' b'`. Rewrite using `[hr]`. Rewrite `hs`, the goal using `[zsmul_eq_mul]`. Take the linear combination `(1 - (χ a' g : E) / χ b' g) * hs`.

Introduce `a' b'`. Distinguish the cases in `h' : a' = b'`. Simplify using `only [hv0, if_pos h']`. Conclude with `continuous_const`. Simplify using `only [hv0, if_neg h']`.

Conclude with `(continuous_const.sub (hc a' b')).mul continuous_const`. Introduce `g a' b' hw`. Rewrite using `[hv0]`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[hX0w a' b' hw, mul_zero]`. Establish `hv0S : v0 ∈ S` using `(hS v0).2 hQ`. Establish `hne0 : (⟨v0, hv0S⟩ : S) ≠ 0`. Introduce `h`. Establish `h1 : v0 g0 a b = 0`.

Use `congrArg (fun w : S => (w : H → M4 E) g0 a b) h` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[hv0, if_neg hab]`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Apply `h0` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Establish `hb` using `Units.ne_zero (χ b g0)`. Establish `: (χ a g0 : E) / χ b g0 = 1` using `by linear_combination -h2`. Conclude with `(div_eq_one_iff_eq hb).1 this`. Conclude with `hX0ab h2`.

Use `(finrank_eq_one_iff_of_nonzero' _ hne0).2 fun w => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `w`. Establish `hwQ` using `(hS w).1 hw`. Unfold `Q at hwQ`. Take `⟨-, -, ⟨Xw, hXw, hXwe⟩, -, -, hwsupp⟩` from `hwQ`.

Use `⟨Xw a b / X0 a b, Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)⟩` and prove the remaining obligations. Use `show Xw a b / X0 a b * v0 g a' b' = w g a' b'`. Rewrite using `[hv0]`. Distinguish the cases in `h' : a' = b'`. Substitute `h'` using the available equality.

Rewrite using `[if_pos rfl, mul_zero]`. Conclude with `(hwsupp g a' a' (by rw [(wt_eq_zero a' a').2 rfl]; exact hwab.symm)).symm`. Rewrite using `[if_neg h', hXwe g a' b' h']`. Distinguish the cases in `hw' : wt a' b' = wt a b`. Break down `wt_fib a b a' b' hab hw' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Clear the denominators using the available nonvanishing facts. Establish `s1` using `(mem_sp4_iff.1 hXw) a b`. Establish `s2` using `(mem_sp4_iff.1 hX0) a b`. Rewrite `s1`, `s2` using `[zsmul_eq_mul]`. Establish `hsq : ((sgn a * sgn b : ℤ) : E) * ((sgn a * sgn b : ℤ) : E) = 1`.

Rewrite using `[← Int.cast_mul, sgn_sq]`. Simplify using the standard rewrite rules. Establish `e1 : Xw b.rev a.rev = -((sgn a * sgn b : ℤ) : E) * Xw a b`. Take the linear combination `((sgn a * sgn b : ℤ) : E) * s1 - Xw b.rev a.rev * hsq`. Establish `e2 : X0 b.rev a.rev = -((sgn a * sgn b : ℤ) : E) * X0 a b`.

Take the linear combination `((sgn a * sgn b : ℤ) : E) * s2 - X0 b.rev a.rev * hsq`. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hX0w a' b' hw', ← hXwe g a' b' h', hwsupp g a' b' hw']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dim_root [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a b, Continuous fun g => (χ a g : E) / χ b g)
    (a b : Fin 4) (hab : a ≠ b) (g0 : H) (h0 : χ a g0 ≠ χ b g0) (S : Submodule E (H → M4 E))
    (hS : ∀ γ, γ ∈ S ↔ Q χ I (wt a b) γ) : finrank E S = 1 := by
  obtain ⟨X0, hX0, hX0ab, hX0w⟩ := ex_root (E := E) a b
  have hwab : wt a b ≠ 0 := fun h => hab ((wt_eq_zero a b).1 h)
  obtain ⟨v0, hv0⟩ : ∃ v0 : H → M4 E, ∀ g a' b', v0 g a' b' =
      if a' = b' then 0 else (1 - (χ a' g : E) / χ b' g) * X0 a' b' :=
    ⟨fun g => Matrix.of fun a' b' => if a' = b' then 0 else (1 - (χ a' g : E) / χ b' g) * X0 a' b',
      fun _ _ _ => rfl⟩
  have hQ : Q χ I (wt a b) v0 := by
    unfold Q
    refine ⟨?_, ?_, ⟨X0, hX0, fun g a' b' h => by rw [hv0, if_neg h]⟩, fun s _ a' => by rw [hv0, if_pos rfl], ?_, ?_⟩
    · intro g h a' b'
      rw [hv0, hv0, hv0]
      by_cases h' : a' = b'
      · simp [h']
      · simp only [if_neg h', map_mul, Units.val_mul]
        have h1 := Units.ne_zero (χ b' g)
        have h2 := Units.ne_zero (χ b' h)
        field_simp
        ring
    · intro g
      rw [mem_sp4_iff]
      intro a' b'
      rw [hv0, hv0]
      by_cases h' : a' = b'
      · subst h'
        simp
      · have h'' : b'.rev ≠ a'.rev := fun e => h' (Fin.rev_injective e).symm
        rw [if_neg h', if_neg h'']
        have hr : (χ b'.rev g : E) / χ a'.rev g = (χ a' g : E) / χ b' g := by
          have e1 := hθ g a'
          have e2 := hθ g b'
          have n1 := Units.ne_zero (χ a'.rev g)
          have n2 := Units.ne_zero (χ b' g)
          rw [div_eq_div_iff n1 n2]
          linear_combination e2 - e1
        have hs := (mem_sp4_iff.1 hX0) a' b'
        rw [hr]
        rw [zsmul_eq_mul] at hs ⊢
        linear_combination (1 - (χ a' g : E) / χ b' g) * hs
    · intro a' b'
      by_cases h' : a' = b'
      · simp only [hv0, if_pos h']
        exact continuous_const
      · simp only [hv0, if_neg h']
        exact (continuous_const.sub (hc a' b')).mul continuous_const
    · intro g a' b' hw
      rw [hv0]
      split_ifs
      · rfl
      · rw [hX0w a' b' hw, mul_zero]
  have hv0S : v0 ∈ S := (hS v0).2 hQ
  have hne0 : (⟨v0, hv0S⟩ : S) ≠ 0 := by
    intro h
    have h1 : v0 g0 a b = 0 := by
      have := congrArg (fun w : S => (w : H → M4 E) g0 a b) h
      simpa using this
    rw [hv0, if_neg hab] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · apply h0
      apply Units.ext
      have hb := Units.ne_zero (χ b g0)
      have : (χ a g0 : E) / χ b g0 = 1 := by linear_combination -h2
      exact (div_eq_one_iff_eq hb).1 this
    · exact hX0ab h2
  refine (finrank_eq_one_iff_of_nonzero' _ hne0).2 fun w => ?_
  obtain ⟨w, hw⟩ := w
  have hwQ := (hS w).1 hw
  unfold Q at hwQ
  obtain ⟨-, -, ⟨Xw, hXw, hXwe⟩, -, -, hwsupp⟩ := hwQ
  refine ⟨Xw a b / X0 a b, Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)⟩
  show Xw a b / X0 a b * v0 g a' b' = w g a' b'
  rw [hv0]
  by_cases h' : a' = b'
  · subst h'
    rw [if_pos rfl, mul_zero]
    exact (hwsupp g a' a' (by rw [(wt_eq_zero a' a').2 rfl]; exact hwab.symm)).symm
  · rw [if_neg h', hXwe g a' b' h']
    by_cases hw' : wt a' b' = wt a b
    · rcases wt_fib a b a' b' hab hw' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · field_simp
      · have s1 := (mem_sp4_iff.1 hXw) a b
        have s2 := (mem_sp4_iff.1 hX0) a b
        rw [zsmul_eq_mul] at s1 s2
        have hsq : ((sgn a * sgn b : ℤ) : E) * ((sgn a * sgn b : ℤ) : E) = 1 := by
          rw [← Int.cast_mul, sgn_sq]
          simp
        have e1 : Xw b.rev a.rev = -((sgn a * sgn b : ℤ) : E) * Xw a b := by
          linear_combination ((sgn a * sgn b : ℤ) : E) * s1 - Xw b.rev a.rev * hsq
        have e2 : X0 b.rev a.rev = -((sgn a * sgn b : ℤ) : E) * X0 a b := by
          linear_combination ((sgn a * sgn b : ℤ) : E) * s2 - X0 b.rev a.rev * hsq
        rw [e1, e2]
        field_simp
    · rw [hX0w a' b' hw', ← hXwe g a' b' h', hwsupp g a' b' hw']
      ring

/- English proof (translation)
Establish `key : ∀ γ, Q χ I 0 γ → (∀ g a b, a ≠ b → γ g a b = 0) ∧ (∀ g h a, γ (g * h) a a = γ g a a + γ h a a) ∧ (∀ g a, γ g a.rev a.rev = -γ g a a) ∧ (∀ a, Continuous fun g => γ g a a) ∧ (∀ g, I g → ∀ a, γ g a a = 0)`. Introduce and unpack `γ ⟨hco, hsp, -, hI, hcont, hwt⟩`. Use `⟨fun g a b hab => hwt g a b (fun h => hab ((wt_eq_zero a b).1 h)), fun g h a => ?_, fun g a => ?_, fun a => hcont a a, hI⟩` and prove the remaining obligations. Rewrite using `[hco g h a a, div_self (Units.ne_zero _), one_mul]`. Establish `h1` using `(mem_sp4_iff.1 (hsp g)) a a`.

Apply the tactic sequence `have h2 : sgn a * sgn a = 1 := by fin_cases a <;> decide`. Rewrite `h1` using `[h2, one_smul]`. Conclude with `h1`. Set `L : S →ₗ[E] E × E` to `{ toFun := fun γ => ((γ : H → M4 E) σ 0 0, (γ : H → M4 E) σ 1 1) map_add' := fun x y => rfl map_smul' := fun c x => rfl }`. Establish `hinj : Function.Injective L`.

Use `(injective_iff_map_eq_zero L).2 fun γ hγ => ?_` and prove the remaining obligations. Take `⟨hoff, hadd, hrev, hc, hI0⟩` from `key γ ((hS γ).1 γ.2)`. Establish `h0 : (γ : H → M4 E) σ 0 0 = 0` using `congrArg Prod.fst hγ`. Establish `h1 : (γ : H → M4 E) σ 1 1 = 0` using `congrArg Prod.snd hγ`. Establish `u0` using `hun (fun g => (γ : H → M4 E) g 0 0) (hc 0) (fun g h => hadd g h 0) (fun g hg => hI0 g hg 0) h0`.

Establish `u1` using `hun (fun g => (γ : H → M4 E) g 1 1) (hc 1) (fun g h => hadd g h 1) (fun g hg => hI0 g hg 1) h1`. Establish `d0 : ∀ g, (γ : H → M4 E) g 0 0 = 0` using `fun g => congrFun u0 g`. Establish `d1 : ∀ g, (γ : H → M4 E) g 1 1 = 0` using `fun g => congrFun u1 g`. Establish `d2 : ∀ g, (γ : H → M4 E) g 2 2 = 0`. Introduce `g`.

Establish `h` using `hrev g 1`. Establish `e : Fin.rev (1 : Fin 4) = 2` using `by decide`. Rewrite `h` using `[e, d1 g, neg_zero]`. Conclude with `h`. Establish `d3 : ∀ g, (γ : H → M4 E) g 3 3 = 0`.

Introduce `g`. Establish `h` using `hrev g 0`. Establish `e : Fin.rev (0 : Fin 4) = 3` using `by decide`. Rewrite `h` using `[e, d0 g, neg_zero]`. Conclude with `h`.

Use `Subtype.ext (funext fun g => Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `show (γ : H → M4 E) g a b = 0`. Distinguish the cases in `hab : a = b`. Substitute `hab fin_cases a` using the available equality. Conclude with `d0 g`.

Conclude with `d1 g`. Conclude with `d2 g`. Conclude with `d3 g`. Conclude with `hoff g a b hab`. Establish `hsurj : Function.Surjective L`.

Introduce and unpack `⟨e0, e1⟩`. Take `⟨u, hu, hua, huI, huσ⟩` from `hex e0`. Take `⟨u', hu', hua', huI', huσ'⟩` from `hex e1`. Set `d : H → Fin 4 → E` to `fun g => ![u g, u' g, -u' g, -u g]`. Set `γ : H → M4 E` to `fun g => Matrix.of fun a b => if a = b then d g a else 0`.

Establish `hγ : ∀ g a b, γ g a b = if a = b then d g a else 0` using `fun g a b => rfl`. Establish `hdadd : ∀ g h a, d (g * h) a = d g a + d h a`. Introduce `g h a`. Apply the tactic sequence `fin_cases a <;> simp [d, hua, hua'] <;> ring`. Establish `hdrev : ∀ g a, d g a.rev = -d g a`.

Introduce `g a`. Apply the tactic sequence `fin_cases a <;> simp [d] <;> rfl`. Establish `hdI : ∀ g, I g → ∀ a, d g a = 0`. Introduce `g hg a`. Apply the tactic sequence `fin_cases a <;> simp [d, huI g hg, huI' g hg]`.

Establish `hdc : ∀ a, Continuous fun g => d g a`. Introduce `a`. Use `fin_cases a`. Conclude with `hu`. Conclude with `hu'`.

Conclude with `hu'.neg`. Conclude with `hu.neg`. Establish `hQ : Q χ I 0 γ`. Use `⟨fun g h a b => ?_, fun g => ?_, ⟨0, zero_mem _, fun g a b hab => ?_⟩, fun s hs a => ?_, fun a b => ?_, fun g a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[hγ, hγ, hγ]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, if_pos rfl, div_self (Units.ne_zero _), one_mul, hdadd]`. Rewrite using `[if_neg hab, if_neg hab, if_neg hab, mul_zero, add_zero]`. Rewrite using `[mem_sp4_iff]`.

Introduce `a b`. Rewrite using `[hγ, hγ]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, hdrev]`.

Apply the tactic sequence `have h2 : sgn a * sgn a = 1 := by fin_cases a <;> decide`. Rewrite using `[h2, one_smul]`. Establish `hne : b.rev ≠ a.rev` using `fun h => hab (Fin.rev_injective h).symm`. Rewrite using `[if_neg hne, if_neg hab, smul_zero, neg_zero]`. Rewrite using `[hγ, if_neg hab] show (0 : E) = _ * (0 : E)`.

Rewrite using `[mul_zero]`. Rewrite using `[hγ, if_pos rfl]`. Conclude with `hdI s hs a`. Use `show Continuous fun g => if a = b then d g a else 0`. Distinguish the cases in `hab : a = b`.

Simplify using `only [if_pos hab]`. Conclude with `hdc a`. Simplify using `only [if_neg hab]`. Conclude with `continuous_const`. Establish `hne : a ≠ b` using `fun h => hab (by rw [h]; exact (wt_eq_zero b b).2 rfl)`.

Rewrite using `[hγ, if_neg hne]`. Use `⟨⟨γ, (hS γ).2 hQ⟩, ?_⟩` and prove the remaining obligations. Use `show (γ σ 0 0, γ σ 1 1) = (e0, e1)`. Rewrite using `[hγ, hγ, if_pos rfl, if_pos rfl]`. Simplify using `[d, huσ, huσ']`.

Establish `e` using `LinearEquiv.ofBijective L ⟨hinj, hsurj⟩`. Rewrite using `[e.finrank_eq]`. Simplify using the standard rewrite rules.
-/
private theorem dim_zero (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (σ : H)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (S : Submodule E (H → M4 E)) (hS : ∀ γ, γ ∈ S ↔ Q χ I 0 γ) : finrank E S = 2 := by
  have key : ∀ γ, Q χ I 0 γ → (∀ g a b, a ≠ b → γ g a b = 0) ∧ (∀ g h a, γ (g * h) a a = γ g a a + γ h a a) ∧
      (∀ g a, γ g a.rev a.rev = -γ g a a) ∧ (∀ a, Continuous fun g => γ g a a) ∧ (∀ g, I g → ∀ a, γ g a a = 0) := by
    rintro γ ⟨hco, hsp, -, hI, hcont, hwt⟩
    refine ⟨fun g a b hab => hwt g a b (fun h => hab ((wt_eq_zero a b).1 h)), fun g h a => ?_, fun g a => ?_,
      fun a => hcont a a, hI⟩
    · rw [hco g h a a, div_self (Units.ne_zero _), one_mul]
    · have h1 := (mem_sp4_iff.1 (hsp g)) a a
      have h2 : sgn a * sgn a = 1 := by
        fin_cases a <;> decide
      rw [h2, one_smul] at h1
      exact h1
  let L : S →ₗ[E] E × E :=
    { toFun := fun γ => ((γ : H → M4 E) σ 0 0, (γ : H → M4 E) σ 1 1)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun γ hγ => ?_
    obtain ⟨hoff, hadd, hrev, hc, hI0⟩ := key γ ((hS γ).1 γ.2)
    have h0 : (γ : H → M4 E) σ 0 0 = 0 := congrArg Prod.fst hγ
    have h1 : (γ : H → M4 E) σ 1 1 = 0 := congrArg Prod.snd hγ
    have u0 := hun (fun g => (γ : H → M4 E) g 0 0) (hc 0) (fun g h => hadd g h 0) (fun g hg => hI0 g hg 0) h0
    have u1 := hun (fun g => (γ : H → M4 E) g 1 1) (hc 1) (fun g h => hadd g h 1) (fun g hg => hI0 g hg 1) h1
    have d0 : ∀ g, (γ : H → M4 E) g 0 0 = 0 := fun g => congrFun u0 g
    have d1 : ∀ g, (γ : H → M4 E) g 1 1 = 0 := fun g => congrFun u1 g
    have d2 : ∀ g, (γ : H → M4 E) g 2 2 = 0 := by
      intro g
      have h := hrev g 1
      have e : Fin.rev (1 : Fin 4) = 2 := by decide
      rw [e, d1 g, neg_zero] at h
      exact h
    have d3 : ∀ g, (γ : H → M4 E) g 3 3 = 0 := by
      intro g
      have h := hrev g 0
      have e : Fin.rev (0 : Fin 4) = 3 := by decide
      rw [e, d0 g, neg_zero] at h
      exact h
    refine Subtype.ext (funext fun g => Matrix.ext fun a b => ?_)
    show (γ : H → M4 E) g a b = 0
    by_cases hab : a = b
    · subst hab
      fin_cases a
      · exact d0 g
      · exact d1 g
      · exact d2 g
      · exact d3 g
    · exact hoff g a b hab
  have hsurj : Function.Surjective L := by
    rintro ⟨e0, e1⟩
    obtain ⟨u, hu, hua, huI, huσ⟩ := hex e0
    obtain ⟨u', hu', hua', huI', huσ'⟩ := hex e1
    let d : H → Fin 4 → E := fun g => ![u g, u' g, -u' g, -u g]
    let γ : H → M4 E := fun g => Matrix.of fun a b => if a = b then d g a else 0
    have hγ : ∀ g a b, γ g a b = if a = b then d g a else 0 := fun g a b => rfl
    have hdadd : ∀ g h a, d (g * h) a = d g a + d h a := by
      intro g h a
      fin_cases a <;> simp [d, hua, hua'] <;> ring
    have hdrev : ∀ g a, d g a.rev = -d g a := by
      intro g a
      fin_cases a <;> simp [d] <;> rfl
    have hdI : ∀ g, I g → ∀ a, d g a = 0 := by
      intro g hg a
      fin_cases a <;> simp [d, huI g hg, huI' g hg]
    have hdc : ∀ a, Continuous fun g => d g a := by
      intro a
      fin_cases a
      · exact hu
      · exact hu'
      · exact hu'.neg
      · exact hu.neg
    have hQ : Q χ I 0 γ := by
      refine ⟨fun g h a b => ?_, fun g => ?_, ⟨0, zero_mem _, fun g a b hab => ?_⟩, fun s hs a => ?_,
        fun a b => ?_, fun g a b hab => ?_⟩
      · rw [hγ, hγ, hγ]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos rfl, if_pos rfl, div_self (Units.ne_zero _), one_mul, hdadd]
        · rw [if_neg hab, if_neg hab, if_neg hab, mul_zero, add_zero]
      · rw [mem_sp4_iff]
        intro a b
        rw [hγ, hγ]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos rfl, hdrev]
          have h2 : sgn a * sgn a = 1 := by
            fin_cases a <;> decide
          rw [h2, one_smul]
        · have hne : b.rev ≠ a.rev := fun h => hab (Fin.rev_injective h).symm
          rw [if_neg hne, if_neg hab, smul_zero, neg_zero]
      · rw [hγ, if_neg hab]
        show (0 : E) = _ * (0 : E)
        rw [mul_zero]
      · rw [hγ, if_pos rfl]
        exact hdI s hs a
      · show Continuous fun g => if a = b then d g a else 0
        by_cases hab : a = b
        · simp only [if_pos hab]
          exact hdc a
        · simp only [if_neg hab]
          exact continuous_const
      · have hne : a ≠ b := fun h => hab (by rw [h]; exact (wt_eq_zero b b).2 rfl)
        rw [hγ, if_neg hne]
    refine ⟨⟨γ, (hS γ).2 hQ⟩, ?_⟩
    show (γ σ 0 0, γ σ 1 1) = (e0, e1)
    rw [hγ, hγ, if_pos rfl, if_pos rfl]
    simp [d, huσ, huσ']
  have e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  rw [e.finrank_eq]
  simp

/- English proof (translation)
Set `Tq : (H → M4 E) ≃ₗ[E] (H → M4 E)` to `{ toFun := fun s g => Matrix.of fun a b => s g a b * ((χ b g : Eˣ) : E)⁻¹ invFun := fun γ g => Matrix.of fun a b => γ g a b * ((χ b g : Eˣ) : E) map_add' := fun s t => by`. Use function extensionality and compare the values at `g`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `show (s g a b + t g a b) * ((χ b g : Eˣ) : E)⁻¹ = s g a b * ((χ b g : Eˣ) : E)⁻¹ + t g a b * ((χ b g : Eˣ) : E)⁻¹`. Rewrite using `[add_mul]`.

Use the proof step `map_smul' := fun x s => by`. Use function extensionality and compare the values at `g`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `show (x * s g a b) * ((χ b g : Eˣ) : E)⁻¹ = x * (s g a b * ((χ b g : Eˣ) : E)⁻¹)`. Rewrite using `[mul_assoc]`.

Use `left_inv := fun s => by`. Use function extensionality and compare the values at `g`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `show s g a b * ((χ b g : Eˣ) : E)⁻¹ * ((χ b g : Eˣ) : E) = s g a b`. Rewrite using `[inv_mul_cancel_right₀ (Units.ne_zero _)]`.

Use `right_inv := fun γ => by`. Use function extensionality and compare the values at `g`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `show γ g a b * ((χ b g : Eˣ) : E) * ((χ b g : Eˣ) : E)⁻¹ = γ g a b`. Rewrite using `[mul_inv_cancel_right₀ (Units.ne_zero _)] }`.

Establish `hsymm : ∀ γ g a b, (Tq.symm γ) g a b = γ g a b * ((χ b g : Eˣ) : E)` using `fun _ _ _ _ => rfl`. Establish `hS' : ∀ γ, γ ∈ S.map (Tq : (H → M4 E) →ₗ[E] (H → M4 E)) ↔ Q χ I j γ`. Introduce `γ`. Rewrite using `[Submodule.mem_map_equiv, hS]`. Simplify using `only [hsymm]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨r, hr, hPr⟩, hcont, hsupp⟩`. Establish `hcg : ∀ a b, Continuous fun g => γ g a b`. Introduce `a b`. Use `(hcont a b).mul (hci b)` as an intermediate fact.

Use `this.congr fun g => ?_` and prove the remaining obligations. Use `show γ g a b * ((χ b g : Eˣ) : E) * ((χ b g : Eˣ) : E)⁻¹ = γ g a b`. Rewrite using `[mul_inv_cancel_right₀ (Units.ne_zero _)]`. Establish `hcoc` using `(hom_iff χ γ).1 ⟨r, hr⟩`. Take `⟨h1, h2, h3⟩` from `(hP γ r hr hcg).1 hPr`.

Use `⟨hcoc, h1, h2, h3, hcg, fun g a b hw => ?_⟩` and prove the remaining obligations. Use `hsupp g a b hw` as an intermediate fact. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (Units.ne_zero _)`.

Introduce and unpack `⟨hcoc, h1, h2, h3, hcg, hsupp⟩`. Take `⟨r, hr⟩` from `(hom_iff χ γ).2 hcoc`. Use `⟨⟨r, hr, (hP γ r hr hcg).2 ⟨h1, h2, h3⟩⟩, fun a b => (hcg a b).mul (hc b), fun g a b hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hsupp g a b hw, zero_mul]`. Rewrite using `[← LinearEquiv.finrank_map_eq Tq S]`.

Distinguish the cases in `h0 : j = 0`. Substitute `h0` using the available equality. Establish `: dimsP 0 = 2` using `by simp [dimsP]`. Rewrite using `[this]`. Conclude with `dim_zero χ I σ hex hun _ hS'`.

Distinguish the cases in `hw : j ∈ wts`. Take `⟨a, b, hab, hj⟩` from `wt_root j hw h0`. Take `⟨g0, hg0⟩` from `hne a b hab`. Establish `: dimsP j = 1` using `by simp [dimsP, h0, hw]`. Rewrite using `[this]`.

Establish `hc' : ∀ a b, Continuous fun g => ((χ a g : Eˣ) : E) / ((χ b g : Eˣ) : E)`. Introduce `a b`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(hc a).mul (hci b)`. Substitute `hj` using the available equality.

Conclude with `dim_root χ I θ hθ hc' a b hab g0 hg0 _ hS'`. Establish `: dimsP j = 0` using `by simp [dimsP, h0, hw]`. Rewrite using `[this]`. Establish `hbot : S.map (Tq : (H → M4 E) →ₗ[E] (H → M4 E)) = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `γ hγ`. Take `⟨-, -, -, -, -, hsupp⟩` from `(hS' γ).1 hγ`. Use function extensionality and compare the values at `g`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `hsupp g a b fun h => hw ?_` and prove the remaining obligations.

Rewrite using `[← h]`. Conclude with `wt_mem a b`. Rewrite using `[hbot]`. Conclude with `finrank_bot E _`.
-/
private theorem dim_core [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E) (σ : H)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a, Continuous fun g => (χ a g : E))
    (hci : ∀ a, Continuous fun g => (χ a g : E)⁻¹) (hne : ∀ a b, a ≠ b → ∃ g, χ a g ≠ χ b g)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (P : (H →* M4 (DualNumber E)) → Prop)
    (hP : ∀ (γ : H → M4 E) (r : H →* M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → (∀ a b, Continuous fun g => γ g a b) →
      (P r ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, a ≠ b → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧
        ∀ s, I s → ∀ a, γ s a a = 0))
    (j : ℤ × ℤ) (S : Submodule E (H → M4 E))
    (hS : ∀ s, s ∈ S ↔ (∃ r : H →* M4 (DualNumber E),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, s g a b⟩) ∧ P r) ∧
        (∀ a b, Continuous fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) : finrank E S = dimsP j := by
  let Tq : (H → M4 E) ≃ₗ[E] (H → M4 E) :=
    { toFun := fun s g => Matrix.of fun a b => s g a b * ((χ b g : Eˣ) : E)⁻¹
      invFun := fun γ g => Matrix.of fun a b => γ g a b * ((χ b g : Eˣ) : E)
      map_add' := fun s t => by
        funext g
        refine Matrix.ext fun a b => ?_
        show (s g a b + t g a b) * ((χ b g : Eˣ) : E)⁻¹ = s g a b * ((χ b g : Eˣ) : E)⁻¹ + t g a b * ((χ b g : Eˣ) : E)⁻¹
        rw [add_mul]
      map_smul' := fun x s => by
        funext g
        refine Matrix.ext fun a b => ?_
        show (x * s g a b) * ((χ b g : Eˣ) : E)⁻¹ = x * (s g a b * ((χ b g : Eˣ) : E)⁻¹)
        rw [mul_assoc]
      left_inv := fun s => by
        funext g
        refine Matrix.ext fun a b => ?_
        show s g a b * ((χ b g : Eˣ) : E)⁻¹ * ((χ b g : Eˣ) : E) = s g a b
        rw [inv_mul_cancel_right₀ (Units.ne_zero _)]
      right_inv := fun γ => by
        funext g
        refine Matrix.ext fun a b => ?_
        show γ g a b * ((χ b g : Eˣ) : E) * ((χ b g : Eˣ) : E)⁻¹ = γ g a b
        rw [mul_inv_cancel_right₀ (Units.ne_zero _)] }
  have hsymm : ∀ γ g a b, (Tq.symm γ) g a b = γ g a b * ((χ b g : Eˣ) : E) := fun _ _ _ _ => rfl
  have hS' : ∀ γ, γ ∈ S.map (Tq : (H → M4 E) →ₗ[E] (H → M4 E)) ↔ Q χ I j γ := by
    intro γ
    rw [Submodule.mem_map_equiv, hS]
    simp only [hsymm]
    constructor
    · rintro ⟨⟨r, hr, hPr⟩, hcont, hsupp⟩
      have hcg : ∀ a b, Continuous fun g => γ g a b := by
        intro a b
        have := (hcont a b).mul (hci b)
        refine this.congr fun g => ?_
        show γ g a b * ((χ b g : Eˣ) : E) * ((χ b g : Eˣ) : E)⁻¹ = γ g a b
        rw [mul_inv_cancel_right₀ (Units.ne_zero _)]
      have hcoc := (hom_iff χ γ).1 ⟨r, hr⟩
      obtain ⟨h1, h2, h3⟩ := (hP γ r hr hcg).1 hPr
      refine ⟨hcoc, h1, h2, h3, hcg, fun g a b hw => ?_⟩
      have := hsupp g a b hw
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (Units.ne_zero _)
    · rintro ⟨hcoc, h1, h2, h3, hcg, hsupp⟩
      obtain ⟨r, hr⟩ := (hom_iff χ γ).2 hcoc
      refine ⟨⟨r, hr, (hP γ r hr hcg).2 ⟨h1, h2, h3⟩⟩, fun a b => (hcg a b).mul (hc b), fun g a b hw => ?_⟩
      rw [hsupp g a b hw, zero_mul]
  rw [← LinearEquiv.finrank_map_eq Tq S]
  by_cases h0 : j = 0
  · subst h0
    have : dimsP 0 = 2 := by simp [dimsP]
    rw [this]
    exact dim_zero χ I σ hex hun _ hS'
  · by_cases hw : j ∈ wts
    · obtain ⟨a, b, hab, hj⟩ := wt_root j hw h0
      obtain ⟨g0, hg0⟩ := hne a b hab
      have : dimsP j = 1 := by simp [dimsP, h0, hw]
      rw [this]
      have hc' : ∀ a b, Continuous fun g => ((χ a g : Eˣ) : E) / ((χ b g : Eˣ) : E) := by
        intro a b
        simp only [div_eq_mul_inv]
        exact (hc a).mul (hci b)
      subst hj
      exact dim_root χ I θ hθ hc' a b hab g0 hg0 _ hS'
    · have : dimsP j = 0 := by simp [dimsP, h0, hw]
      rw [this]
      have hbot : S.map (Tq : (H → M4 E) →ₗ[E] (H → M4 E)) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro γ hγ
        obtain ⟨-, -, -, -, -, hsupp⟩ := (hS' γ).1 hγ
        funext g
        refine Matrix.ext fun a b => ?_
        refine hsupp g a b fun h => hw ?_
        rw [← h]
        exact wt_mem a b
      rw [hbot]
      exact finrank_bot E _

end Core

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Establish `hU : (fun x => g⁻¹ * x) ⁻¹' (φ.ker : Set H) ∈ nhds g`. Apply `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Use `show (φ.ker : Set H) ∈ nhds (g⁻¹ * g)`. Rewrite using `[inv_mul_cancel]`.

Conclude with `h.mem_nhds (one_mem _)`. Use `(continuousAt_const : ContinuousAt (fun _ : H => f (φ g)) g).congr ?_` and prove the remaining obligations. Use `filter_upwards [hU] with x hx`. Establish `hx' : φ (g⁻¹ * x) = 1` using `hx`. Rewrite `hx'` using `[map_mul, map_inv, inv_mul_eq_one]`.

Rewrite using `[hx']`.
-/
private theorem cont_of_open {H O E : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group O]
    [TopologicalSpace E] (φ : H →* O) (h : IsOpen (φ.ker : Set H)) (f : O → E) : Continuous fun g => f (φ g) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hU : (fun x => g⁻¹ * x) ⁻¹' (φ.ker : Set H) ∈ nhds g := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    show (φ.ker : Set H) ∈ nhds (g⁻¹ * g)
    rw [inv_mul_cancel]
    exact h.mem_nhds (one_mem _)
  refine (continuousAt_const : ContinuousAt (fun _ : H => f (φ g)) g).congr ?_
  filter_upwards [hU] with x hx
  have hx' : φ (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ j S hS`. Use `letI tE : TopologicalSpace E := moduleTopology ℚ_[l] E`. Use `haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩`. Use `haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective`.

Establish `hF` using `facts D hD`. Establish `hqT : q ∈ D.T` using `Finset.mem_insert_of_mem hq`. Set `σ : D.Gp q` to `⟨D.sg q, (hF.2.1 q hqT).1⟩`. Set `χ : Fin 4 → D.Gp q →* Eˣ` to `fun a => (Units.map (algebraMap c.O E : c.O →* E)).comp ((D.ps a).comp (D.Gp q).subtype)`. Establish `hχ : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.O)` using `fun a g => rfl`.

Establish `hQC : ∀ (f : D.Gp q → E), QCont l f ↔ Continuous f` using `fun f => Iff.rfl`. Establish `cZ : Continuous (algebraMap ℤ_[l] E)`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E, RingHom.coe_comp]`. Conclude with `(continuous_algebraMap ℚ_[l] E).comp (continuous_subtype_val : Continuous fun x : ℤ_[l] => (x : ℚ_[l]))`. Establish `cC : Continuous fun g : D.Gp q => algebraMap c.O E (chiO ℚ Ω l c.O g : c.O)`.

Establish `: (fun g : D.Gp q => algebraMap c.O E (chiO ℚ Ω l c.O g : c.O)) = fun g : D.Gp q => algebraMap ℤ_[l] E (cycZ ℚ Ω l g : ℤ_[l])`. Use function extensionality and compare the values at `g`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] c.O E]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `cZ.comp (Units.continuous_val.comp ((continuous_cycZ ℚ Ω l).comp continuous_subtype_val))`. Establish `cO : ∀ φ : G ℚ Ω →* c.Oˣ, IsOpen (φ.ker : Set (G ℚ Ω)) → Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O)`. Introduce `φ hφ`. Use `cont_of_open (φ.comp (D.Gp q).subtype) ?_ (fun u => algebraMap c.O E (u : c.O))` and prove the remaining obligations. Rewrite using `[← MonoidHom.comap_ker, Subgroup.coe_comap]`.

Conclude with `continuous_subtype_val.isOpen_preimage _ hφ`. Establish `cMul : ∀ φ ψ' : G ℚ Ω →* c.Oˣ, (Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O)) → (Continuous fun g : D.Gp q => algebraMap c.O E (ψ' g : c.O)) → Continuous fun g : D.Gp q => algebraMap c.O E ((φ * ψ') g : c.O)`. Introduce `φ ψ' h1 h2`. Simplify using `only [MonoidHom.mul_apply, Units.val_mul, map_mul]`. Conclude with `h1.mul h2`.

Establish `cInvO : ∀ φ : G ℚ Ω →* c.Oˣ, IsOpen (φ.ker : Set (G ℚ Ω)) → IsOpen ((φ⁻¹).ker : Set (G ℚ Ω))`. Introduce `φ hφ`. Establish `: ((φ⁻¹).ker : Set (G ℚ Ω)) = φ.ker`. Use extensionality with `g`. Simplify using `[MonoidHom.mem_ker]`.

Rewrite using `[this]`. Conclude with `hφ`. Establish `cPow : ∀ (φ : G ℚ Ω →* c.Oˣ) (n : ℕ), (Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O)) → Continuous fun g : D.Gp q => algebraMap c.O E ((φ ^ (n : ℤ)) g : c.O)`. Introduce `φ n h`. Simplify using `only [zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow]`.

Conclude with `h.pow n`. Establish `hc : ∀ a, Continuous fun g => (χ a g : E)`. Establish `cAl : Continuous fun g : D.Gp q => algebraMap c.O E (D.al g : c.O)` using `cMul _ _ (cMul _ _ cC (cO _ (cInvO _ hF.2.2.2.2.2.2.2.2.2.2.2.2.1))) (cO _ hD.xi_open)`. Establish `cPs : Continuous fun g : D.Gp q => algebraMap c.O E (D.Psi g : c.O)` using `cMul _ _ (cPow _ _ cC) (cO _ hD.psi_open)`. Introduce `a`.

Use `fin_cases a`. Conclude with `cMul _ _ cAl cPs`. Conclude with `cPs`. Conclude with `cAl`. Use `show Continuous fun g : D.Gp q => algebraMap c.O E ((1 : G ℚ Ω →* c.Oˣ) g : c.O)`.

Simplify using `only [MonoidHom.one_apply, Units.val_one, map_one]`. Conclude with `continuous_const`. Establish `hci : ∀ a, Continuous fun g => (χ a g : E)⁻¹`. Introduce `a`. Establish `: (fun g => (χ a g : E)⁻¹) = fun g => (χ a g⁻¹ : E)`.

Use function extensionality and compare the values at `g`. Rewrite using `[map_inv, Units.val_inv_eq_inv_val]`. Rewrite using `[this]`. Conclude with `(hc a).comp continuous_inv`. Set `θ : D.Gp q → E` to `fun g => algebraMap c.O E (D.th g : c.O)`.

Establish `hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g`. Introduce `g a`. Use `congrArg (fun φ : G ℚ Ω →* c.Oˣ => algebraMap c.O E ((φ (g : G ℚ Ω) : c.Oˣ) : c.O)) (hF.2.2.2.2.2.1 a)` as an intermediate fact. Simplify using `only [MonoidHom.mul_apply, Units.val_mul, map_mul] at this`. Rewrite using `[hχ, hχ, mul_comm]`.

Conclude with `this`. Establish `hI` using `UpperTheory.exists_unique_unramified_hom_of_frobenius_value l q (hF.1 q hq).1 (D.pl q) (hD.pl_over q (hF.1 q hq).1) σ (hD.sg_frob q hqT) E`. Establish `key : ∀ a b (x : D.Gp q), χ a x = χ b x → D.ps a x = D.ps b x`. Introduce `a b x h`. Apply `Units.ext` to reduce the goal to its premises.

Apply `IsFractionRing.injective c.O E` to reduce the goal to its premises. Rewrite using `[← hχ, ← hχ, h]`. Establish `hs : ∃ s ∈ D.Ip q, D.ψ s ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hmap : Subgroup.map D.ψ (D.Ip q) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `(Subgroup.mem_bot).2 (hcon s hs)`. Establish `hdvd` using `(Finset.mem_filter.1 hq).2.2`.

Rewrite `hdvd` using `[hmap, Subgroup.card_bot, Nat.dvd_one]`. Conclude with `(Fact.out : l.Prime).one_lt.ne' hdvd`. Take `⟨s, hsI, hψ⟩` from `hs`. Establish `hsv` using `hF.2.2.2.2.1 q hq s hsI`. Set `s' : D.Gp q` to `⟨s, Ine_le_Dec _ hsI⟩`.

Establish `hne : ∀ a b, a ≠ b → ∃ g, χ a g ≠ χ b g`. Introduce `a b hab`. Distinguish the cases in `hl : lamW a = lamW b`. Use `⟨s', fun h => ?_⟩` and prove the remaining obligations. Establish `h2` using `key a b s' h`.

Establish `v : ∀ i, D.ps i s = if i = 0 ∨ i = 1 then D.ψ s else 1`. Introduce `i`. Use `fin_cases i`. Use `show D.th s = _`. Simplify using `[hsv.2.2]`.

Use `show D.Psi s = _`. Simplify using `[hsv.2.1]`. Use `show D.al s = _`. Simplify using `[hsv.1]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `D.ps a s = D.ps b s at h2`. Rewrite `h2` using `[v, v]`. Establish `hψ' : 1 ≠ D.ψ s` using `fun e => hψ e.symm`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [lamW, hψ, hψ'] at hab hl h2`. Use `⟨σ, fun h => (hF.2.1 q hqT).2.2 a b hl ?_⟩` and prove the remaining obligations.

Establish `h2` using `key a b σ h`. Conclude with `congrArg (fun u : c.Oˣ => residue c.O (u : c.O)) h2`. Establish `r0e : ∀ (g : D.Gp q) a b, algebraMap c.O E (D.r0At q g a b) = if a = b then (χ a g : E) else 0`. Introduce `g a b`. Use `show algebraMap c.O E (Matrix.diagonal (fun i => (D.ps i g : c.O)) a b) = _`.

Rewrite using `[Matrix.diagonal_apply]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Both sides reduce to the same expression. Conclude with `map_zero _`.

Establish `hP : ∀ (γ : D.Gp q → M4 E) (r : D.Gp q →* M4 (DualNumber E)), (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → (∀ a b, Continuous fun g => γ g a b) → (EqP D q r ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, a ≠ b → γ g a b = (1 - (χ a g : E) / χ b g) * X …`. Introduce `γ r hr hcont`. Establish `hdual : IsFirstOrderDeformationOfRZero D q γ r`. Introduce `g a b`. Rewrite using `[hr g a b]`.

Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Conclude with `(r0e g a b).symm`. Use `show γ g a b * (χ b g : E) = (γ g * Matrix.map (Matrix.diagonal (fun i => (D.ps i g : c.O))) (algebraMap c.O E)) a b`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal]`. Both sides reduce to the same expression.

Rewrite using `[spTanP D hD q hq E γ r hdual hcont]`. Establish `hdiv : ∀ (g : D.Gp q) a b, algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) = (χ a g : E) / χ b g`. Introduce `g a b`. Rewrite using `[Units.val_mul, map_mul, map_units_inv, hχ, hχ, div_eq_mul_inv]`. Simplify using `only [hdiv]`.

Establish `hS' : ∀ s, s ∈ S ↔ (∃ r : D.Gp q →* M4 (DualNumber E), (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, s g a b⟩) ∧ EqP D q r) ∧ (∀ a b, Continuous fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0`. Introduce `s`. Rewrite using `[hS]`. Simplify using `only [r0e]`. Both sides reduce to the same expression.

Conclude with `dim_core χ (fun s => (s : G ℚ Ω) ∈ D.Ip q) θ σ hθ hc hci hne hI.1 hI.2 (EqP D q) hP j S hS'`.
-/
theorem UpperTheory.tangent_space_deformation_dual_numbers :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (q : ℕ), q ∈ D.Sb → ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (j : ℤ × ℤ) (S : Submodule E (D.Gp q → M4 E)), (∀ s, s ∈ S ↔ (∃ r' : D.Gp q →* M4 (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At q g a b), s g a b⟩) ∧ EqP D q r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) → finrank E ↥S = dimsP j := by
  intro Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ j S hS
  letI tE : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have hF := facts D hD
  have hqT : q ∈ D.T := Finset.mem_insert_of_mem hq
  let σ : D.Gp q := ⟨D.sg q, (hF.2.1 q hqT).1⟩
  let χ : Fin 4 → D.Gp q →* Eˣ := fun a => (Units.map (algebraMap c.O E : c.O →* E)).comp ((D.ps a).comp (D.Gp q).subtype)
  have hχ : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.O) := fun a g => rfl
  have hQC : ∀ (f : D.Gp q → E), QCont l f ↔ Continuous f := fun f => Iff.rfl
  have cZ : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E, RingHom.coe_comp]
    exact (continuous_algebraMap ℚ_[l] E).comp (continuous_subtype_val : Continuous fun x : ℤ_[l] => (x : ℚ_[l]))
  have cC : Continuous fun g : D.Gp q => algebraMap c.O E (chiO ℚ Ω l c.O g : c.O) := by
    have : (fun g : D.Gp q => algebraMap c.O E (chiO ℚ Ω l c.O g : c.O)) =
        fun g : D.Gp q => algebraMap ℤ_[l] E (cycZ ℚ Ω l g : ℤ_[l]) := by
      funext g
      rw [IsScalarTower.algebraMap_apply ℤ_[l] c.O E]
      rfl
    rw [this]
    exact cZ.comp (Units.continuous_val.comp ((continuous_cycZ ℚ Ω l).comp continuous_subtype_val))
  have cO : ∀ φ : G ℚ Ω →* c.Oˣ, IsOpen (φ.ker : Set (G ℚ Ω)) →
      Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O) := by
    intro φ hφ
    refine cont_of_open (φ.comp (D.Gp q).subtype) ?_ (fun u => algebraMap c.O E (u : c.O))
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact continuous_subtype_val.isOpen_preimage _ hφ
  have cMul : ∀ φ ψ' : G ℚ Ω →* c.Oˣ, (Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O)) →
      (Continuous fun g : D.Gp q => algebraMap c.O E (ψ' g : c.O)) →
      Continuous fun g : D.Gp q => algebraMap c.O E ((φ * ψ') g : c.O) := by
    intro φ ψ' h1 h2
    simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
    exact h1.mul h2
  have cInvO : ∀ φ : G ℚ Ω →* c.Oˣ, IsOpen (φ.ker : Set (G ℚ Ω)) → IsOpen ((φ⁻¹).ker : Set (G ℚ Ω)) := by
    intro φ hφ
    have : ((φ⁻¹).ker : Set (G ℚ Ω)) = φ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [this]
    exact hφ
  have cPow : ∀ (φ : G ℚ Ω →* c.Oˣ) (n : ℕ), (Continuous fun g : D.Gp q => algebraMap c.O E (φ g : c.O)) →
      Continuous fun g : D.Gp q => algebraMap c.O E ((φ ^ (n : ℤ)) g : c.O) := by
    intro φ n h
    simp only [zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow]
    exact h.pow n
  have hc : ∀ a, Continuous fun g => (χ a g : E) := by
    have cAl : Continuous fun g : D.Gp q => algebraMap c.O E (D.al g : c.O) :=
      cMul _ _ (cMul _ _ cC (cO _ (cInvO _ hF.2.2.2.2.2.2.2.2.2.2.2.2.1))) (cO _ hD.xi_open)
    have cPs : Continuous fun g : D.Gp q => algebraMap c.O E (D.Psi g : c.O) :=
      cMul _ _ (cPow _ _ cC) (cO _ hD.psi_open)
    intro a
    fin_cases a
    · exact cMul _ _ cAl cPs
    · exact cPs
    · exact cAl
    · show Continuous fun g : D.Gp q => algebraMap c.O E ((1 : G ℚ Ω →* c.Oˣ) g : c.O)
      simp only [MonoidHom.one_apply, Units.val_one, map_one]
      exact continuous_const
  have hci : ∀ a, Continuous fun g => (χ a g : E)⁻¹ := by
    intro a
    have : (fun g => (χ a g : E)⁻¹) = fun g => (χ a g⁻¹ : E) := by
      funext g
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [this]
    exact (hc a).comp continuous_inv
  let θ : D.Gp q → E := fun g => algebraMap c.O E (D.th g : c.O)
  have hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g := by
    intro g a
    have := congrArg (fun φ : G ℚ Ω →* c.Oˣ => algebraMap c.O E ((φ (g : G ℚ Ω) : c.Oˣ) : c.O)) (hF.2.2.2.2.2.1 a)
    simp only [MonoidHom.mul_apply, Units.val_mul, map_mul] at this
    rw [hχ, hχ, mul_comm]
    exact this
  have hI := UpperTheory.exists_unique_unramified_hom_of_frobenius_value l q (hF.1 q hq).1 (D.pl q) (hD.pl_over q (hF.1 q hq).1) σ (hD.sg_frob q hqT) E
  have key : ∀ a b (x : D.Gp q), χ a x = χ b x → D.ps a x = D.ps b x := by
    intro a b x h
    apply Units.ext
    apply IsFractionRing.injective c.O E
    rw [← hχ, ← hχ, h]
  have hs : ∃ s ∈ D.Ip q, D.ψ s ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hmap : Subgroup.map D.ψ (D.Ip q) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_bot).2 (hcon s hs)
    have hdvd := (Finset.mem_filter.1 hq).2.2
    rw [hmap, Subgroup.card_bot, Nat.dvd_one] at hdvd
    exact (Fact.out : l.Prime).one_lt.ne' hdvd
  obtain ⟨s, hsI, hψ⟩ := hs
  have hsv := hF.2.2.2.2.1 q hq s hsI
  let s' : D.Gp q := ⟨s, Ine_le_Dec _ hsI⟩
  have hne : ∀ a b, a ≠ b → ∃ g, χ a g ≠ χ b g := by
    intro a b hab
    by_cases hl : lamW a = lamW b
    · refine ⟨s', fun h => ?_⟩
      have h2 := key a b s' h
      have v : ∀ i, D.ps i s = if i = 0 ∨ i = 1 then D.ψ s else 1 := by
        intro i
        fin_cases i
        · show D.th s = _
          simp [hsv.2.2]
        · show D.Psi s = _
          simp [hsv.2.1]
        · show D.al s = _
          simp [hsv.1]
        · rfl
      change D.ps a s = D.ps b s at h2
      rw [v, v] at h2
      have hψ' : 1 ≠ D.ψ s := fun e => hψ e.symm
      fin_cases a <;> fin_cases b <;> simp [lamW, hψ, hψ'] at hab hl h2
    · refine ⟨σ, fun h => (hF.2.1 q hqT).2.2 a b hl ?_⟩
      have h2 := key a b σ h
      exact congrArg (fun u : c.Oˣ => residue c.O (u : c.O)) h2
  have r0e : ∀ (g : D.Gp q) a b, algebraMap c.O E (D.r0At q g a b) = if a = b then (χ a g : E) else 0 := by
    intro g a b
    show algebraMap c.O E (Matrix.diagonal (fun i => (D.ps i g : c.O)) a b) = _
    rw [Matrix.diagonal_apply]
    split_ifs with hab
    · subst hab
      rfl
    · exact map_zero _
  have hP : ∀ (γ : D.Gp q → M4 E) (r : D.Gp q →* M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → (∀ a b, Continuous fun g => γ g a b) →
      (EqP D q r ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, a ≠ b → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧
        ∀ t : D.Gp q, (t : G ℚ Ω) ∈ D.Ip q → ∀ a, γ t a a = 0) := by
    intro γ r hr hcont
    have hdual : IsFirstOrderDeformationOfRZero D q γ r := by
      intro g a b
      rw [hr g a b]
      refine TrivSqZeroExt.ext ?_ ?_
      · exact (r0e g a b).symm
      · show γ g a b * (χ b g : E) = (γ g * Matrix.map (Matrix.diagonal (fun i => (D.ps i g : c.O))) (algebraMap c.O E)) a b
        rw [Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal]
        rfl
    rw [spTanP D hD q hq E γ r hdual hcont]
    have hdiv : ∀ (g : D.Gp q) a b, algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) = (χ a g : E) / χ b g := by
      intro g a b
      rw [Units.val_mul, map_mul, map_units_inv, hχ, hχ, div_eq_mul_inv]
    simp only [hdiv]
  have hS' : ∀ s, s ∈ S ↔ (∃ r : D.Gp q →* M4 (DualNumber E),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, s g a b⟩) ∧ EqP D q r) ∧
        (∀ a b, Continuous fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0 := by
    intro s
    rw [hS]
    simp only [r0e]
    rfl
  exact dim_core χ (fun s => (s : G ℚ Ω) ∈ D.Ip q) θ σ hθ hc hci hne hI.1 hI.2 (EqP D q) hP j S hS'
