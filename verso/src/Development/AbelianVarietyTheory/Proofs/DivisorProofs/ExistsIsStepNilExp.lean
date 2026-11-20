import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def prods (κ : DividedPowers I) (m : ℕ) : Set R :=
  {x | ∃ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ κ.dpow p.1 p.2).prod}

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons p l ih`. Introduce `hl hs`.

Establish `hp : p.2 ∈ I` using `hl p (by simp)`. Simplify using `only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢`. Break down `Nat.eq_zero_or_pos p.1 with h | h` into its components or cases. Rewrite `hs` using `[h]`. Conclude with `I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))`.

Conclude with `I.mul_mem_right _ (κ.dpow_mem (by omega) hp)`.
-/
theorem prod_mem (κ : DividedPowers I) : ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) →
    1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod ∈ I := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro hl hs
    have hp : p.2 ∈ I := hl p (by simp)
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h] at hs
      exact I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))
    · exact I.mul_mem_right _ (κ.dpow_mem (by omega) hp)

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _ h`. Simplify using `at h`. Consider the case `cons p l ih`.

Introduce `hl hs n hn`. Establish `hp : p.2 ∈ I` using `hl p (by simp)`. Establish `hl' : ∀ q ∈ l, q.2 ∈ I` using `fun q hq ↦ hl q (by simp [hq])`. Simplify using `only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢`. Break down `Nat.eq_zero_or_pos p.1 with h | h` into its components or cases.

Rewrite using `[h, κ.dpow_zero hp, _root_.one_mul]`. Conclude with `ih hl' (by omega) n hn`. Use `set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod`. Establish `hm : κ.dpow p.1 p.2 ∈ I` using `κ.dpow_mem (by omega) hp`. Establish `hz : P * κ.dpow (n * p.1) p.2 = 0`.

Use `hN ((n * p.1, p.2) :: l) (by` as an intermediate fact. Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases. Conclude with `hp`. Conclude with `hl' q hq) (by`.

Establish `: 2 * p.1 ≤ n * p.1` using `Nat.mul_le_mul_right _ hn`. Simplify using `only [List.map_cons, List.sum_cons]`. Use the proof step `omega)`. Simplify `this` using `[List.map_cons, List.prod_cons, mul_comm]`. Rewrite using `[mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]`.

Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]`.
-/
theorem dpow_prod_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N + 1 ≤ (l.map Prod.fst).sum →
      ∀ n, 2 ≤ n → κ.dpow n (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p l ih =>
    intro hl hs n hn
    have hp : p.2 ∈ I := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ I := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, κ.dpow_zero hp, _root_.one_mul]
      exact ih hl' (by omega) n hn
    · set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod
      have hm : κ.dpow p.1 p.2 ∈ I := κ.dpow_mem (by omega) hp
      have hz : P * κ.dpow (n * p.1) p.2 = 0 := by
        have := hN ((n * p.1, p.2) :: l) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hl' q hq) (by
          have : 2 * p.1 ≤ n * p.1 := Nat.mul_le_mul_right _ hn
          simp only [List.map_cons, List.sum_cons]
          omega)
        simpa [List.map_cons, List.prod_cons, mul_comm] using this
      rw [mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]

end GlobalTheory.SqLift.DPStep

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def idl (κ : DividedPowers I) (m : ℕ) : Ideal R := Ideal.span (prods κ m)

/- English proof (translation)
Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨l, hl, hs, rfl⟩`. Conclude with `prod_mem κ l hl (by omega)`.
-/
theorem idl_le (κ : DividedPowers I) (N : ℕ) : idl κ (N + 1) ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact prod_mem κ l hl (by omega)

/- English proof (translation)
Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, hs, rfl⟩` from `hx`. Use `hN ((1, a) :: l) (by` as an intermediate fact.

Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases. Conclude with `ha`. Conclude with `hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)`. Simplify `this` using `[κ.dpow_one ha]`.

Consider the case `zero => exact mul_zero a`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]`.
-/
theorem mul_idl_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) {a : R} (ha : a ∈ I) :
    ∀ b ∈ idl κ (N + 1), a * b = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    have := hN ((1, a) :: l) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)
    simpa [κ.dpow_one ha] using this
  | zero => exact mul_zero a
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

/- English proof (translation)
Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, pow_two]`. Use `Ideal.mul_le.2 fun a ha b hb ↦ ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Conclude with `mul_idl_eq_zero κ hN (idl_le κ N ha) b hb`.
-/
theorem idl_sq (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) : idl κ (N + 1) ^ 2 = 0 := by
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  rw [Ideal.mem_bot]
  exact mul_idl_eq_zero κ hN (idl_le κ N ha) b hb

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, hs, rfl⟩` from `hx`. Conclude with `dpow_prod_eq_zero κ hN l hl hs`.

Consider the case `zero => intro n hn; exact κ.dpow_eval_zero (by omega)`. Consider the case `add x y hxm hym hx hy`. Introduce `n hn`. Establish `hxI` using `idl_le κ N hxm`. Establish `hyI` using `idl_le κ N hym`.

Rewrite using `[κ.dpow_add hxI hyI]`. Use `Finset.sum_eq_zero fun k hk ↦ ?_` and prove the remaining obligations. Rewrite `hk` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h1 : 2 ≤ k.1`. Rewrite using `[hx _ h1, MulZeroClass.zero_mul]`.

Distinguish the cases in `h2 : 2 ≤ k.2`. Rewrite using `[hy _ h2, mul_zero]`. Take `⟨a, b⟩` from `k`. Simplify using `only at h1 h2 hk`. Take `rfl : a = 1` from `by omega`.

Take `rfl : b = 1` from `by omega`. Rewrite using `[κ.dpow_one hxI, κ.dpow_one hyI]`. Conclude with `mul_idl_eq_zero κ hN hxI y hym`. Consider the case `smul r x hxm hx`. Introduce `n hn`.

Rewrite using `[smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]`.
-/
theorem dpow_idl (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ x ∈ idl κ (N + 1), ∀ n, 2 ≤ n → κ.dpow n x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    exact dpow_prod_eq_zero κ hN l hl hs
  | zero => intro n hn; exact κ.dpow_eval_zero (by omega)
  | add x y hxm hym hx hy =>
    intro n hn
    have hxI := idl_le κ N hxm
    have hyI := idl_le κ N hym
    rw [κ.dpow_add hxI hyI]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : 2 ≤ k.1
    · rw [hx _ h1, MulZeroClass.zero_mul]
    by_cases h2 : 2 ≤ k.2
    · rw [hy _ h2, mul_zero]
    obtain ⟨a, b⟩ := k
    simp only at h1 h2 hk
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [κ.dpow_one hxI, κ.dpow_one hyI]
    exact mul_idl_eq_zero κ hN hxI y hym
  | smul r x hxm hx =>
    intro n hn
    rw [smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]

/- English proof (translation)
The claim follows from `inf_le_right dpow_mem n hn j hj := by rcases Nat.lt_or_ge n 2 with h | h · obtain rfl : n = 1 := by omega rw [κ.dpow_one hj.2]; exact hj · rw [dpow_idl κ hN j hj.1 n h]; exact Submodule.zero_mem _`.
-/
theorem isSubDPIdeal (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    IsSubDPIdeal κ (idl κ (N + 1) ⊓ I) where
  isSubideal := inf_le_right
  dpow_mem n hn j hj := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [κ.dpow_one hj.2]; exact hj
    · rw [dpow_idl κ hN j hj.1 n h]; exact Submodule.zero_mem _

end GlobalTheory.SqLift.DPStep

open GlobalTheory.SqLift.DPStep in

/- English proof (translation)
Introduce `R R₀ _ _ I κ π hπ hker N hN`. Use `set J := idl κ (N + 1)`. Establish `hJI : J ≤ I` using `idl_le κ N`. Establish `hsub` using `isSubDPIdeal κ hN`. Establish `hz : ∀ a ∈ J, π a = 0` using `fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha`.

Set `π₁ : R ⧸ J →+* R₀` to `Ideal.Quotient.lift J π hz`. Establish `hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1)`. Introduce `l hl hs`. Establish `key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) → ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧ (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod = Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpo …`. Introduce `l`.

Proceed by induction on `l with`. Consider the case `nil => intro _; exact ⟨[], by simp, by simp, by simp⟩`. Consider the case `cons p l ih`. Introduce `hl`. Take `⟨l', hl', he, hp⟩` from `ih fun q hq ↦ hl q (by simp [hq])`.

Take `⟨a, ha, hae⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hl p (by simp))`. Use `⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩` and prove the remaining obligations. Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases. Conclude with `ha`.

Conclude with `hl' q hq`. Simplify using `only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]`. Rewrite using `[DividedPowers.Quotient.dpow_apply κ hsub ha]`. Take `⟨l', hl', he, hp⟩` from `key l hl`. Rewrite using `[hp, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩`. Use `⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J), DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩` and prove the remaining obligations. Use `{ nil := ⟨N + 2, hN⟩ nil₁ := ⟨N + 1, hnil1⟩ surj := Ideal.Quotient.mk_surjective surj₁ := ?_ comp := Ideal.Quotient.lift_comp_mk J π hz ker := hker kerJ := Ideal.mk_ker ker₁ := ?_ dp := DividedPowers.Quotient.isDPMorphism κ hsub dpJ := ?_ }` and prove the remaining obligations. Introduce `y`. Take `⟨a, rfl⟩` from `hπ y`.

Conclude with `⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩`. Use extensionality with `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]`. Use `(isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩` and prove the remaining obligations.

Break down `Nat.lt_or_ge n 2 with h | h` into its components or cases. Take `rfl : n = 1` from `by omega`. Rewrite using `[RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]`. Rewrite using `[RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]`.
-/
theorem GlobalTheory.SqLift.exists_isStep_nilExp :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ N : ℕ, NilExp κ (N + 2) →
    ∃ (R₁ : Type) (_ : CommRing R₁) (J : Ideal R) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀),
      IsStep κ π hJ ρ κ₁ π₁ ∧ NilExp κ₁ (N + 1) := by
  intro R R₀ _ _ I κ π hπ hker N hN
  set J := idl κ (N + 1)
  have hJI : J ≤ I := idl_le κ N
  have hsub := isSubDPIdeal κ hN
  have hz : ∀ a ∈ J, π a = 0 := fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha
  let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π hz
  have hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1) := by
    intro l hl hs
    have key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) →
        ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧
          (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod =
            Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpow p.1 p.2).prod := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
      | cons p l ih =>
        intro hl
        obtain ⟨l', hl', he, hp⟩ := ih fun q hq ↦ hl q (by simp [hq])
        obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
          (hl p (by simp))
        refine ⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ha
          · exact hl' q hq
        · simp only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]
          rw [DividedPowers.Quotient.dpow_apply κ hsub ha]
    obtain ⟨l', hl', he, hp⟩ := key l hl
    rw [hp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩
  refine ⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J),
    DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩
  refine
    { nil := ⟨N + 2, hN⟩
      nil₁ := ⟨N + 1, hnil1⟩
      surj := Ideal.Quotient.mk_surjective
      surj₁ := ?_
      comp := Ideal.Quotient.lift_comp_mk J π hz
      ker := hker
      kerJ := Ideal.mk_ker
      ker₁ := ?_
      dp := DividedPowers.Quotient.isDPMorphism κ hsub
      dpJ := ?_ }
  · intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩
  · ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]
  · refine (isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]
    · rw [RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]
