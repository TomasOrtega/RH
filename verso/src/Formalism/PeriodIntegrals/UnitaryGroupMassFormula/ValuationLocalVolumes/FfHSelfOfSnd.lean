import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section split

variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))

/- English proof (translation)
Simplify using `only [ffH, Prod.fst_sum, Prod.fst_mul]`.
-/
theorem ffH_fst' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by
  simp only [ffH, Prod.fst_sum, Prod.fst_mul]

/- English proof (translation)
Simplify using `only [ffH, Prod.snd_sum, Prod.snd_mul]`.
-/
theorem ffH_snd' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by
  simp only [ffH, Prod.snd_sum, Prod.snd_mul]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[ffH_fst']`. Simplify using `[h]`. Rewrite using `[ffH_snd']`. Simplify using `[h]`.
-/
theorem ffH_self_of_snd (x : Fin M → k × k) (h : ∀ l, (x l).2 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[ffH_fst']`. Simplify using `[h]`. Rewrite using `[ffH_snd']`. Simplify using `[h]`.
-/
theorem ffH_self_of_fst (x : Fin M → k × k) (h : ∀ l, (x l).1 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h push_neg at h`. Take `⟨c, hc, hne⟩` from `h`. Distinguish the cases in `h1 : c.1 = 0`. Use `right`.

Establish `h2 : c.2 ≠ 0` using `fun h2 => hne (Prod.ext h1 h2)`. Introduce `l`. Establish `hl` using `congrArg Prod.snd (congrFun hc l)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl`. Conclude with `(mul_eq_zero.1 hl).resolve_left h2`.

Use `left`. Introduce `l`. Establish `hl` using `congrArg Prod.fst (congrFun hc l)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl`. Conclude with `(mul_eq_zero.1 hl).resolve_left h1`.

Introduce and unpack `(h | h) hfree`. Establish `h1` using `hfree (1, 0) (by`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp [h l])`. Simplify using `at h1`.

Establish `h1` using `hfree (0, 1) (by`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp [h l])`. Simplify using `at h1`.
-/
theorem notFree_iff (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hne⟩ := h
    by_cases h1 : c.1 = 0
    · right
      have h2 : c.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      intro l
      have hl := congrArg Prod.snd (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h2
    · left
      intro l
      have hl := congrArg Prod.fst (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h1
  · rintro (h | h) hfree
    · have h1 := hfree (1, 0) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
    · have h1 := hfree (0, 1) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1

/- English proof (translation)
Use `set c := T0⁻¹.mulVec w with hc`. Use `⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩` and prove the remaining obligations. Establish `h1 : ffH (RingEquiv.prodComm (R` using `k) (S := k)).toRingHom J (Y j) (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by`. Rewrite using `[← hY]`. Simplify using `only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]`.

Use `conv_lhs => arg 2`. Use extensionality with `i`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `m _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Establish `h2 : T0.mulVec c = w`. Rewrite using `[hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Establish `h3` using `congrFun h2 j`.

Simplify `h3` using `[Matrix.mulVec, dotProduct]`.
-/
theorem perp_surj {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by
  classical
  set c := T0⁻¹.mulVec w with hc
  refine ⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩

  have h1 : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j)
      (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by
    rw [← hY]
    simp only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1]
  have h2 : T0.mulVec c = w := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3

/- English proof (translation)
Establish `_` using `Fintype.ofFinite k`. Establish `hs : LinearMap.range (Matrix.mulVecLin B) = ⊤`. Use `LinearMap.range_eq_top.2 fun v => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hB v`. Conclude with `⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩`.

Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)`. Rewrite `hrn` using `[hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Establish `e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B)` using `Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]`. Rewrite using `[Nat.card_congr e]`. Simplify using `only [Nat.card_eq_fintype_card]`.

Rewrite using `[Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem natCard_ker_mul_card_pow_eq_of_surjective [Finite k] {a' : ℕ} (B : Matrix (Fin a') (Fin M) k)
    (hB : Function.Surjective B.mulVec) :
    Nat.card {u : Fin M → k // B.mulVec u = 0} * Nat.card k ^ a' = Nat.card k ^ M := by
  classical
  have _ := Fintype.ofFinite k
  have hs : LinearMap.range (Matrix.mulVecLin B) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨u, hu⟩ := hB v
    exact ⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B) :=
    Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]
  congr 1
  omega

/- English proof (translation)
Set `B : Matrix (Fin a') (Fin M) k` to `fun j l => ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).1`. Establish `hB : ∀ (x : Fin M → k × k) j, (ffH (RingEquiv.prodComm (R` using `k) (S := k)).toRingHom J (Y j) x).1 = B.mulVec (fun l => (x l).1) j := by`. Introduce `x j`. Rewrite using `[ffH_fst']`. Simplify using `only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hsurj : Function.Surjective B.mulVec`. Introduce `w'`. Take `⟨x, hx⟩` from `perp_surj J T0 hu Y hY (fun j => (w' j, 0))`. Conclude with `⟨fun l => (x l).1, funext fun j => by rw [← hB x j, hx j]⟩`.

Establish `e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R` using `k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} := { toFun := fun x => ⟨fun l => (x.1 l).1, funext fun j => by`. Rewrite using `[← hB, x.2.1 j]`. Use the proof step `rfl⟩`. Use `invFun := fun u => ⟨fun l => (u.1 l, 0), fun j => by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[hB]`. Conclude with `congrFun u.2 j`. Rewrite using `[ffH_snd'] simp, fun l => rfl⟩`. Use `left_inv := fun x => Subtype.ext (funext fun l => Prod.ext rfl (x.2.2 l).symm)`. Use `right_inv := fun u => rfl }`.

Rewrite using `[Nat.card_congr e]`. Conclude with `natCard_ker_mul_card_pow_eq_of_surjective B hsurj`.
-/
theorem card_half_snd [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).1
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).1 =
        B.mulVec (fun l => (x l).1) j := by
    intro x j
    rw [ffH_fst']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (w' j, 0))
    exact ⟨fun l => (x l).1, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).1, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (u.1 l, 0), fun j => by
        refine Prod.ext ?_ ?_
        · rw [hB]
          exact congrFun u.2 j
        · rw [ffH_snd']
          simp, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext rfl (x.2.2 l).symm)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

/- English proof (translation)
Set `B : Matrix (Fin a') (Fin M) k` to `fun j l => ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2`. Establish `hB : ∀ (x : Fin M → k × k) j, (ffH (RingEquiv.prodComm (R` using `k) (S := k)).toRingHom J (Y j) x).2 = B.mulVec (fun l => (x l).2) j := by`. Introduce `x j`. Rewrite using `[ffH_snd']`. Simplify using `only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hsurj : Function.Surjective B.mulVec`. Introduce `w'`. Take `⟨x, hx⟩` from `perp_surj J T0 hu Y hY (fun j => (0, w' j))`. Conclude with `⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩`.

Establish `e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R` using `k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} := { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by`. Rewrite using `[← hB, x.2.1 j]`. Use the proof step `rfl⟩`. Use `invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[ffH_fst']`. Simplify using the standard rewrite rules. Rewrite using `[hB]`. Conclude with `congrFun u.2 j, fun l => rfl⟩`. Use `left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)`.

Use `right_inv := fun u => rfl }`. Rewrite using `[Nat.card_congr e]`. Conclude with `natCard_ker_mul_card_pow_eq_of_surjective B hsurj`.
-/
theorem card_half_fst [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).2 =
        B.mulVec (fun l => (x l).2) j := by
    intro x j
    rw [ffH_snd']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (0, w' j))
    exact ⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by
        refine Prod.ext ?_ ?_
        · rw [ffH_fst']
          simp
        · rw [hB]
          exact congrFun u.2 j, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

end split

end PI.OmVe
