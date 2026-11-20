import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Expand

/- English proof (translation)
Set `cfg : Finset (Fin e) → Finset (Fin e) → Fin e → X` to `fun T S i => if i ∈ T then (if i ∈ S then A i else M i) else V i`. Establish `key : ∀ T : Finset (Fin e), Φ V = ∑ S ∈ T.powerset, (∏ i ∈ S, b i) * (∏ i ∈ T \ S, a i) * Φ (cfg T S)`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [cfg]`.

Consider the case `insert j T hj ih`. Rewrite using `[Finset.sum_powerset_insert hj, ih, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Establish `hST : S ⊆ T` using `Finset.mem_powerset.mp hS`. Establish `hjS : j ∉ S` using `fun h => hj (hST h)`.

Establish `e1 : cfg T S = Function.update (cfg (insert j T) S) j (V j)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `[cfg, hj]`.

Simplify using `[cfg, hi]`. Establish `e2 : Function.update (cfg (insert j T) S) j (M j) = cfg (insert j T) S`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using `[cfg, hjS]`. Simplify using `[cfg, hi]`. Establish `e3 : Function.update (cfg (insert j T) S) j (A j) = cfg (insert j T) (insert j S)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Simplify using `[cfg]`. Simplify using `[cfg, hi]`. Establish `d1 : insert j T \ S = insert j (T \ S)`. Use extensionality with `i`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `[hjS]`. Simplify using `[hi]`. Establish `d2 : insert j T \ insert j S = T \ S`.

Use extensionality with `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `[hj]`. Simplify using `[hi]`.

Establish `hjTS : j ∉ T \ S` using `fun h => hj (Finset.mem_sdiff.mp h).1`. Rewrite using `[e1, hposition, e2, e3, d1, d2, Finset.prod_insert hjTS, Finset.prod_insert hjS]`. Expand and normalize the polynomial expressions, which then agree. Use `key Finset.univ` as an intermediate fact. Rewrite `this` using `[Finset.powerset_univ]`.

Rewrite using `[this]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.compl_eq_univ_sdiff]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `[cfg]`.
-/
theorem sum_expand_positions {X : Type*} {e : ℕ} (Φ : (Fin e → X) → ℤ) (V M A : Fin e → X) (a b : Fin e → ℤ)
    (hposition : ∀ (L : Fin e → X) (i : Fin e), Φ (Function.update L i (V i)) =
      a i * Φ (Function.update L i (M i)) + b i * Φ (Function.update L i (A i))) :
    Φ V = ∑ S : Finset (Fin e), (∏ i ∈ S, b i) * (∏ i ∈ Sᶜ, a i) *
      Φ (fun i => if i ∈ S then A i else M i) := by
  let cfg : Finset (Fin e) → Finset (Fin e) → Fin e → X := fun T S i =>
    if i ∈ T then (if i ∈ S then A i else M i) else V i
  have key : ∀ T : Finset (Fin e), Φ V =
      ∑ S ∈ T.powerset, (∏ i ∈ S, b i) * (∏ i ∈ T \ S, a i) * Φ (cfg T S) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [cfg]
    | insert j T hj ih =>
      rw [Finset.sum_powerset_insert hj, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hST : S ⊆ T := Finset.mem_powerset.mp hS
      have hjS : j ∉ S := fun h => hj (hST h)
      have e1 : cfg T S = Function.update (cfg (insert j T) S) j (V j) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg, hj]
        · simp [cfg, hi]
      have e2 : Function.update (cfg (insert j T) S) j (M j) = cfg (insert j T) S := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg, hjS]
        · simp [cfg, hi]
      have e3 : Function.update (cfg (insert j T) S) j (A j) = cfg (insert j T) (insert j S) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg]
        · simp [cfg, hi]
      have d1 : insert j T \ S = insert j (T \ S) := by
        ext i; by_cases hi : i = j
        · subst hi; simp [hjS]
        · simp [hi]
      have d2 : insert j T \ insert j S = T \ S := by
        ext i; by_cases hi : i = j
        · subst hi; simp [hj]
        · simp [hi]
      have hjTS : j ∉ T \ S := fun h => hj (Finset.mem_sdiff.mp h).1
      rw [e1, hposition, e2, e3, d1, d2, Finset.prod_insert hjTS, Finset.prod_insert hjS]
      ring
  have := key Finset.univ
  rw [Finset.powerset_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.compl_eq_univ_sdiff]
  congr 2
  funext i
  simp [cfg]

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Use `set C : ℤ := ∑ S ∈ Finset.univ.erase ∅, |c S| with hC`. Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Take `⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = C + 1` from `⟨(C + 1).toNat, Int.toNat_of_nonneg (by omega)⟩`.

Establish `hq1 : 1 ≤ q` using `by omega`. Establish `hsum` using `h q hq1`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]`. Establish `hcard : (∅ : Finset (Fin e))ᶜ.card = e` using `by simp`. Rewrite `hsum` using `[hcard]`.

Establish `hrest : ∑ S ∈ Finset.univ.erase ∅, (q : ℤ) ^ Sᶜ.card * c S ≤ (q : ℤ) ^ (e - 1) * C`. Rewrite using `[hC, Finset.mul_sum]`. Use `Finset.sum_le_sum fun S hS => ?_` and prove the remaining obligations. Establish `hSne : S ≠ ∅` using `Finset.ne_of_mem_erase hS`. Establish `hcardS : Sᶜ.card ≤ e - 1`.

Rewrite using `[Finset.card_compl, Fintype.card_fin]`. Use `(Finset.nonempty_iff_ne_empty.mpr hSne).card_pos` as an intermediate fact. Use `Finset.card_le_univ S` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Substitute `he` using the available equality. Establish `hC' : C = 0` using `Finset.sum_eq_zero fun S hS => absurd (Finset.eq_empty_of_isEmpty S) (Finset.ne_of_mem_erase hS)`. Rewrite `hrest` using `[hC']`.

Simplify using `only [pow_zero, one_mul, mul_zero] at hsum hrest`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : (q : ℤ) ^ e = q * (q : ℤ) ^ (e - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `hpos : 0 < (q : ℤ) ^ (e - 1)` using `by positivity`. Rewrite `hsum` using `[hpow]`. Use `set P : ℤ := (q : ℤ) ^ (e - 1) with hP`. Establish `h1 : (q : ℤ) * P * c ∅ ≤ -((q : ℤ) * P)`.

Establish `: 0 < (q : ℤ) * P` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (q : ℤ) * P = C * P + P` using `by rw [hq]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nonneg_of_poly {e : ℕ} (c : Finset (Fin e) → ℤ)
    (h : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S) : 0 ≤ c ∅ := by
  by_contra hneg
  push Not at hneg
  set C : ℤ := ∑ S ∈ Finset.univ.erase ∅, |c S| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = C + 1 := ⟨(C + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hq1 : 1 ≤ q := by omega
  have hsum := h q hq1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)] at hsum
  have hcard : (∅ : Finset (Fin e))ᶜ.card = e := by simp
  rw [hcard] at hsum
  have hrest : ∑ S ∈ Finset.univ.erase ∅, (q : ℤ) ^ Sᶜ.card * c S ≤ (q : ℤ) ^ (e - 1) * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    have hSne : S ≠ ∅ := Finset.ne_of_mem_erase hS
    have hcardS : Sᶜ.card ≤ e - 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := (Finset.nonempty_iff_ne_empty.mpr hSne).card_pos
      have := Finset.card_le_univ S
      rw [Fintype.card_fin] at this
      omega
    calc (q : ℤ) ^ Sᶜ.card * c S ≤ (q : ℤ) ^ Sᶜ.card * |c S| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ (q : ℤ) ^ (e - 1) * |c S| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hq1) hcardS) (abs_nonneg _)
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    have hC' : C = 0 := Finset.sum_eq_zero fun S hS =>
      absurd (Finset.eq_empty_of_isEmpty S) (Finset.ne_of_mem_erase hS)
    rw [hC'] at hrest
    simp only [pow_zero, one_mul, mul_zero] at hsum hrest
    linarith
  · have hpow : (q : ℤ) ^ e = q * (q : ℤ) ^ (e - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < (q : ℤ) ^ (e - 1) := by positivity
    rw [hpow] at hsum
    set P : ℤ := (q : ℤ) ^ (e - 1) with hP
    have h1 : (q : ℤ) * P * c ∅ ≤ -((q : ℤ) * P) := by
      have : 0 < (q : ℤ) * P := by positivity
      nlinarith
    have h2 : (q : ℤ) * P = C * P + P := by rw [hq]; ring
    linarith

end Expand

section Numbers

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def bundleNum (pp : Ideal (Poly k N)) {n : ℕ} (L : Fin n → LineBundle k x) : ℤ :=
  interNum pp (fun i => (L i).toSubSystem)

/- English proof (translation)
Unfold `bundleNum`. Rewrite using `[funext h]`.
-/
theorem bundleNum_congr (pp : Ideal (Poly k N)) {n : ℕ} {L L' : Fin n → LineBundle k x}
    (h : ∀ i, (L i).toSubSystem = (L' i).toSubSystem) : bundleNum pp L = bundleNum pp L' := by
  unfold bundleNum
  rw [funext h]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.
-/
theorem toSubSystem_update {n : ℕ} (L : Fin n → LineBundle k x) (i : Fin n) (Y : LineBundle k x) :
    (fun j => (Function.update L i Y j).toSubSystem) =
      Function.update (fun j => (L j).toSubSystem) i Y.toSubSystem := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR

/- English proof (translation)
Unfold `bundleNum`. Rewrite using `[toSubSystem_update, toSubSystem_update, toSubSystem_update]`. Conclude with `(hR k Ω N x).2.2.1 n pp L i Y Y' hW`.
-/
theorem bundleNum_tensor {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (Y Y' : LineBundle k x) :
    bundleNum pp (Function.update L i (Y.tensor Y')) =
      bundleNum pp (Function.update L i Y) + bundleNum pp (Function.update L i Y') := by
  unfold bundleNum
  rw [toSubSystem_update, toSubSystem_update, toSubSystem_update]
  exact (hR k Ω N x).2.2.1 n pp L i Y Y' hW

/- English proof (translation)
Establish `h` using `bundleNum_tensor hR hW L i (twistBundle k x 0) (twistBundle k x 0)`. Establish `hc : bundleNum pp (Function.update L i ((twistBundle k x 0).tensor (twistBundle k x 0))) = bundleNum pp (Function.update L i (twistBundle k x 0))`. Use `bundleNum_congr pp fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]`. Conclude with `twistSys_zero_twist _`. Simplify using `[hj]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bundleNum_zero {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) :
    bundleNum pp (Function.update L i (twistBundle k x 0)) = 0 := by
  have h := bundleNum_tensor hR hW L i (twistBundle k x 0) (twistBundle k x 0)
  have hc : bundleNum pp (Function.update L i ((twistBundle k x 0).tensor (twistBundle k x 0))) =
      bundleNum pp (Function.update L i (twistBundle k x 0)) := by
    refine bundleNum_congr pp fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]
      exact twistSys_zero_twist _
    · simp [hj]
  linarith

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => rw [Nat.cast_zero, zero_mul]`. Conclude with `bundleNum_zero hR hW L i`. Consider the case `succ p ih`. Express the relevant statement in the definitionally equal form `bundleNum pp (Function.update L i ((M.tpow p).tensor M)) = _`.

Rewrite using `[bundleNum_tensor hR hW, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bundleNum_tpow {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (M : LineBundle k x) (p : ℕ) :
    bundleNum pp (Function.update L i (M.tpow p)) = p * bundleNum pp (Function.update L i M) := by
  induction p with
  | zero => rw [Nat.cast_zero, zero_mul]; exact bundleNum_zero hR hW L i
  | succ p ih =>
    change bundleNum pp (Function.update L i ((M.tpow p).tensor M)) = _
    rw [bundleNum_tensor hR hW, ih]
    push_cast; ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using bundleNum_zero hR hW L i`. Consider the case `succ m ih`. Establish `hc : bundleNum pp (Function.update L i (twistBundle k x ((m + 1 : ℕ) : ℤ))) = bundleNum pp (Function.update L i ((twistBundle k x m).tensor (twistBundle k x 1)))`. Use `bundleNum_congr pp fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]`. Rewrite using `[twistSys_twist_twistSys]`. Use `push_cast`.

Both sides reduce to the same expression. Simplify using `[hj]`. Rewrite using `[hc, bundleNum_tensor hR hW, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bundleNum_twist {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (m : ℕ) :
    bundleNum pp (Function.update L i (twistBundle k x m)) =
      m * bundleNum pp (Function.update L i (twistBundle k x 1)) := by
  induction m with
  | zero => simpa using bundleNum_zero hR hW L i
  | succ m ih =>
    have hc : bundleNum pp (Function.update L i (twistBundle k x ((m + 1 : ℕ) : ℤ))) =
        bundleNum pp (Function.update L i ((twistBundle k x m).tensor (twistBundle k x 1))) := by
      refine bundleNum_congr pp fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]
        rw [twistSys_twist_twistSys]
        push_cast; rfl
      · simp [hj]
    rw [hc, bundleNum_tensor hR hW, ih]
    push_cast; ring

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `pp L hW _`. Establish `h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω)`.

Use function extensionality and compare the values at `fun i => i.elim0`. Rewrite using `[h0, (hR k Ω N x).2.2.2.2 pp hW]`. Conclude with `Nat.cast_nonneg _`. Consider the case `succ n ih`. Introduce `pp L hW hL`.

Take `⟨s, hs, hsI⟩` from `exists_sec_not_mem (L (Fin.last n)) (hL _) hW`. Establish `hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α` using `fun _ => SubSystem k x Ω) (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem := (Fin.snoc_init_self _).symm`. Rewrite using `[hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]`. Use `finsum_nonneg fun qq => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (ih qq _ h.2 fun i => hL _)`. Conclude with `le_rfl`.
-/
theorem interNum_nonneg_of_veryAmple : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x),
    IsSubvar x pp n → (∀ i, IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by
  intro n
  induction n with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    refine finsum_nonneg fun qq => ?_
    split_ifs with h
    · exact mul_nonneg (Nat.cast_nonneg _) (ih qq _ h.2 fun i => hL _)
    · exact le_rfl

end Numbers

/- English proof (translation)
Introduce `k _ Ω _ _ N x e pp Ms hW hnef`. Take `⟨D, hZ⟩` from `exists_dim_of_isSubvar hW`. Set `A : LineBundle k x` to `twistBundle k x 1`. Set `c : Finset (Fin e) → ℤ` to `fun S => bundleNum pp (fun i => if i ∈ S then A else Ms i)`. Establish `key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S`.

Introduce `q hq`. Establish `hq0 : (0 : ℚ) < q` using `by exact_mod_cast hq`. Establish `hK'` using `fun i => hK k D Ω N x (Ms i) hZ (hnef i) (1 / q) (by positivity)`. Use `choose p m hp hm hva using hK'`. Establish `hpm : ∀ i, (p i : ℤ) = q * m i`.

Introduce `i`. Establish `h` using `hm i`. Rewrite `h` using `[mul_one_div, eq_div_iff hq0.ne']`. Establish `: ((p i : ℤ) : ℚ) = ((q * m i : ℤ) : ℚ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions.

Establish `hm0 : ∀ i, 0 < m i`. Introduce `i`. Establish `: 0 < (q : ℤ) * m i` using `by rw [← hpm]; exact_mod_cast hp i`. Conclude with `pos_of_mul_pos_right this (by positivity)`. Set `V : Fin e → LineBundle k x` to `fun i => ((Ms i).tpow (p i)).tensor (twistBundle k x (m i))`.

Establish `hV : ∀ i, IsVeryAmple (V i).toSubSystem`. Introduce `i`. Establish `: (V i).toSubSystem = twistMul (Ms i).toSubSystem (p i) (m i)`. Express the relevant statement in the definitionally equal form `((Ms i).tpow (p i)).toSubSystem.twist (twistSys k x (m i)) = _`. Rewrite using `[LineBundle.tpow_toSubSystem]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hva i`. Establish `hposition : ∀ (L : Fin e → LineBundle k x) (i : Fin e), bundleNum pp (Function.update L i (V i)) = (q * m i) * bundleNum pp (Function.update L i (Ms i)) + m i * bundleNum pp (Function.update L i A)`. Introduce `L i`.

Express the relevant statement in the definitionally equal form `bundleNum pp (Function.update L i (((Ms i).tpow (p i)).tensor (twistBundle k x (m i)))) = _`. Rewrite using `[bundleNum_tensor hR hW, bundleNum_tpow hR hW, ← hpm]`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (hm0 i).le`. Rewrite using `[hn, bundleNum_twist hR hW]`. Establish `hexp` using `sum_expand_positions (bundleNum pp) V Ms (fun _ => A) (fun i => q * m i) m hposition`.

Establish `hVn : 0 ≤ bundleNum pp V` using `interNum_nonneg_of_veryAmple hR e pp V hW hV`. Establish `hw : ∀ S : Finset (Fin e), (∏ i ∈ S, m i) * (∏ i ∈ Sᶜ, ((q : ℤ) * m i)) = (∏ i, m i) * (q : ℤ) ^ Sᶜ.card`. Introduce `S`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc, Finset.prod_mul_prod_compl, mul_comm]`. Simplify using `only [hw, mul_assoc] at hexp`.

Rewrite `hexp` using `[← Finset.mul_sum]`. Establish `hprod : 0 < ∏ i, m i` using `Finset.prod_pos fun i _ => hm0 i`. Rewrite `hVn` using `[hexp]`. Conclude with `(mul_nonneg_iff_of_pos_left hprod).mp hVn`. Establish `h0` using `nonneg_of_poly c key`.

Simplify `h0` using `[c, bundleNum]`.
-/
theorem NefProductNonneg.proof (hK : VeryAmpleNefPlusAmple.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : NefProductNonneg.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp Ms hW hnef
  obtain ⟨D, hZ⟩ := exists_dim_of_isSubvar hW
  let A : LineBundle k x := twistBundle k x 1
  let c : Finset (Fin e) → ℤ := fun S => bundleNum pp (fun i => if i ∈ S then A else Ms i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq
    have hK' := fun i => hK k D Ω N x (Ms i) hZ (hnef i) (1 / q) (by positivity)
    choose p m hp hm hva using hK'
    have hpm : ∀ i, (p i : ℤ) = q * m i := by
      intro i
      have h := hm i
      rw [mul_one_div, eq_div_iff hq0.ne'] at h
      have : ((p i : ℤ) : ℚ) = ((q * m i : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hm0 : ∀ i, 0 < m i := by
      intro i
      have : 0 < (q : ℤ) * m i := by rw [← hpm]; exact_mod_cast hp i
      exact pos_of_mul_pos_right this (by positivity)
    let V : Fin e → LineBundle k x := fun i => ((Ms i).tpow (p i)).tensor (twistBundle k x (m i))
    have hV : ∀ i, IsVeryAmple (V i).toSubSystem := by
      intro i
      have : (V i).toSubSystem = twistMul (Ms i).toSubSystem (p i) (m i) := by
        change ((Ms i).tpow (p i)).toSubSystem.twist (twistSys k x (m i)) = _
        rw [LineBundle.tpow_toSubSystem]
        rfl
      rw [this]
      exact hva i
    have hposition : ∀ (L : Fin e → LineBundle k x) (i : Fin e),
        bundleNum pp (Function.update L i (V i)) =
          (q * m i) * bundleNum pp (Function.update L i (Ms i)) +
            m i * bundleNum pp (Function.update L i A) := by
      intro L i
      change bundleNum pp (Function.update L i (((Ms i).tpow (p i)).tensor (twistBundle k x (m i)))) = _
      rw [bundleNum_tensor hR hW, bundleNum_tpow hR hW, ← hpm]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hm0 i).le
      rw [hn, bundleNum_twist hR hW]
    have hexp := sum_expand_positions (bundleNum pp) V Ms (fun _ => A) (fun i => q * m i) m hposition
    have hVn : 0 ≤ bundleNum pp V := interNum_nonneg_of_veryAmple hR e pp V hW hV
    have hw : ∀ S : Finset (Fin e), (∏ i ∈ S, m i) * (∏ i ∈ Sᶜ, ((q : ℤ) * m i)) =
        (∏ i, m i) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm0 i
    rw [hexp] at hVn
    exact (mul_nonneg_iff_of_pos_left hprod).mp hVn
  have h0 := nonneg_of_poly c key
  simpa [c, bundleNum] using h0

end

end GroundTheory.Heights₂.Heights.Kleiman
