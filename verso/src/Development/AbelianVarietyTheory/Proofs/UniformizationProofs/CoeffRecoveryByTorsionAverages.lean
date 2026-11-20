import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero

namespace GlobalTheory.TorsRecov

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩`. Set `b` to `Module.Free.chooseBasis ℤ X`. Set `f : {t : Multiplicative X →* Fˣ // t ^ N = 1} → (Module.Free.ChooseBasisIndex ℤ X → rootsOfUnity N F)` to `fun t i => ⟨t.1 (Multiplicative.ofAdd (b i)), by`. Rewrite using `[mem_rootsOfUnity, ← MonoidHom.pow_apply, t.2, MonoidHom.one_apply]⟩`.

Establish `hrep : ∀ (t : Multiplicative X →* Fˣ) (x : X), t (Multiplicative.ofAdd x) = ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i)`. Introduce `t x`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[ofAdd_sum, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ofAdd_zsmul, map_zpow]`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `s t h`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Establish `h1` using `hrep s.1 x.toAdd`. Establish `h2` using `hrep t.1 x.toAdd`. Rewrite `h1`, `h2` using `[ofAdd_toAdd]`. Rewrite using `[h1, h2]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congrArg Subtype.val (congrFun h i)` as an intermediate fact. Simplify using `only [f] at this`. Rewrite using `[this]`. Introduce `u`.

Set `t : Multiplicative X →* Fˣ` to `{ toFun := fun x => ∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i) map_one' := by simp map_mul' := by`. Introduce `x y`. Simplify using `[zpow_add, Finset.prod_mul_distrib] }`. Establish `ht : t ^ N = 1`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Express the relevant statement in the definitionally equal form `(∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `hu : (u i : Fˣ) ^ N = 1` using `(mem_rootsOfUnity _ _).1 (u i).2`.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]`. Use `⟨⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `∏ j, (u j : Fˣ) ^ (b.repr (b i) j) = u i`.

Rewrite using `[Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Finsupp.single_apply, hj.symm]`. Simplify using the standard rewrite rules.

Rewrite using `[Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]`.
-/
theorem card_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ N = 1} = N ^ Module.finrank ℤ X := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  let f : {t : Multiplicative X →* Fˣ // t ^ N = 1} →
      (Module.Free.ChooseBasisIndex ℤ X → rootsOfUnity N F) := fun t i =>
    ⟨t.1 (Multiplicative.ofAdd (b i)), by
      rw [mem_rootsOfUnity, ← MonoidHom.pow_apply, t.2, MonoidHom.one_apply]⟩
  have hrep : ∀ (t : Multiplicative X →* Fˣ) (x : X), t (Multiplicative.ofAdd x) =
      ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i) := by
    intro t x
    conv_lhs => rw [← b.sum_repr x]
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      have h1 := hrep s.1 x.toAdd
      have h2 := hrep t.1 x.toAdd
      rw [ofAdd_toAdd] at h1 h2
      rw [h1, h2]
      refine Finset.prod_congr rfl fun i _ => ?_
      have := congrArg Subtype.val (congrFun h i)
      simp only [f] at this
      rw [this]
    · intro u
      let t : Multiplicative X →* Fˣ :=
        { toFun := fun x => ∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)
          map_one' := by simp
          map_mul' := by
            intro x y
            simp [zpow_add, Finset.prod_mul_distrib] }
      have ht : t ^ N = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        change (∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1
        rw [← Finset.prod_pow]
        refine Finset.prod_eq_one fun i _ => ?_
        have hu : (u i : Fˣ) ^ N = 1 := (mem_rootsOfUnity _ _).1 (u i).2
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      apply Subtype.ext
      change ∏ j, (u j : Fˣ) ^ (b.repr (b i) j) = u i
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

open Classical in
/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩`. Use `split_ifs with h`. Take `⟨z, rfl⟩` from `h`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (1 : F))]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_tors F X N hN]`. Simplify using the standard rewrite rules. Introduce `t _`. Rewrite using `[ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, t.2]`. Simplify using the standard rewrite rules.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F N`. Establish `: ∃ t₀ : Multiplicative X →* Fˣ, t₀ ^ N = 1 ∧ t₀ (Multiplicative.ofAdd α) ≠ t₀ (Multiplicative.ofAdd β)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq F X N ζ hN hζ α β hc)`.

Take `⟨t₀, h₀, hne⟩` from `this`. Establish `h₀' : t₀⁻¹ ^ N = 1` using `by rw [inv_pow, h₀, inv_one]`. Set `e : {t : Multiplicative X →* Fˣ // t ^ N = 1} ≃ {t : Multiplicative X →* Fˣ // t ^ N = 1}` to `{ toFun := fun t => ⟨t₀ * t.1, by rw [mul_pow, h₀, t.2, mul_one]⟩ invFun := fun t => ⟨t₀⁻¹ * t.1, by rw [mul_pow, h₀', t.2, mul_one]⟩ left_inv := fun t => Subtype.ext (inv_mul_cancel_left _ _) right_inv := fun t => Subtype.ext (mul_inv_cancel_left _ _) }`. Use `set s := ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1}, ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val with hs`. Establish `h1 : s = (((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val) * s` using `by conv_lhs => rw [hs, ← e.sum_comp]`.

Rewrite using `[hs, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [e, Equiv.coe_fn_mk, MonoidHom.mul_apply, mul_inv, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hs0`.

Apply `hne` to reduce the goal to its premises. Establish `h2 : ((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val = 1` using `mul_right_cancel₀ hs0 (by rw [← h1, one_mul])`. Rewrite `h2` using `[← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]`. Conclude with `h2.symm`.
-/
theorem sum_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N)
    [Fintype {t : Multiplicative X →* Fˣ // t ^ N = 1}] (α β : X) :
    ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val =
      if ∃ z, α = β + N • z then (N : F) ^ Module.finrank ℤ X else 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  split_ifs with h
  · obtain ⟨z, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun _ => (1 : F))]
    · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_tors F X N hN]
      simp
    · intro t _
      rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, t.2]
      simp
  · obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F N
    have : ∃ t₀ : Multiplicative X →* Fˣ, t₀ ^ N = 1 ∧
        t₀ (Multiplicative.ofAdd α) ≠ t₀ (Multiplicative.ofAdd β) := by
      by_contra hc
      push_neg at hc
      exact h (GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq F X N ζ hN hζ α β hc)
    obtain ⟨t₀, h₀, hne⟩ := this
    have h₀' : t₀⁻¹ ^ N = 1 := by rw [inv_pow, h₀, inv_one]
    let e : {t : Multiplicative X →* Fˣ // t ^ N = 1} ≃ {t : Multiplicative X →* Fˣ // t ^ N = 1} :=
      { toFun := fun t => ⟨t₀ * t.1, by rw [mul_pow, h₀, t.2, mul_one]⟩
        invFun := fun t => ⟨t₀⁻¹ * t.1, by rw [mul_pow, h₀', t.2, mul_one]⟩
        left_inv := fun t => Subtype.ext (inv_mul_cancel_left _ _)
        right_inv := fun t => Subtype.ext (mul_inv_cancel_left _ _) }
    set s := ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val with hs
    have h1 : s = (((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val) * s := by
      conv_lhs => rw [hs, ← e.sum_comp]
      rw [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [e, Equiv.coe_fn_mk, MonoidHom.mul_apply, mul_inv, Units.val_mul]
      ring
    by_contra hs0
    apply hne
    have h2 : ((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val = 1 :=
      mul_right_cancel₀ hs0 (by rw [← h1, one_mul])
    rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h2
    exact h2.symm

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[map_zero, Finsupp.zero_apply]`. Take `⟨z, hz⟩` from `h (b.repr x i).natAbs`.

Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr x i).natAbs : ℕ) : ℤ)) ⟨b.repr z i, ?_⟩ ?_` and prove the remaining obligations. Use `conv_lhs => rw [hz]`. Rewrite using `[map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]`. Rewrite using `[Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self (by omega)`.
-/
theorem eq_zero_of_div (X : Type) [AddCommGroup X] [Module.Free ℤ X] (n : ℕ) (hn : 2 ≤ n) (x : X)
    (h : ∀ k, ∃ z, x = n ^ k • z) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr x i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr x i).natAbs : ℕ) : ℤ))
    ⟨b.repr z i, ?_⟩ ?_
  · conv_lhs => rw [hz]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

/- English proof (translation)
Proceed by induction on `k, hjk using Nat.le_induction with`. Consider the case `base => exact h`. Consider the case `succ k _ ih`. Apply `ih` to reduce the goal to its premises. Take `⟨z, hz⟩` from `h`.

Take `⟨w, hw⟩` from `hc k`. Conclude with `⟨w + n • z, by rw [hz, hw, pow_succ, mul_smul, smul_add, add_assoc]⟩`.
-/
theorem class_mono (X : Type) [AddCommGroup X] (n : ℕ) (c : ℕ → X)
    (hc : ∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) (α : X) (j k : ℕ) (hjk : j ≤ k)
    (h : ∃ z, α = c k + n ^ k • z) : ∃ z, α = c j + n ^ j • z := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    apply ih
    obtain ⟨z, hz⟩ := h
    obtain ⟨w, hw⟩ := hc k
    exact ⟨w + n • z, by rw [hz, hw, pow_succ, mul_smul, smul_add, add_assoc]⟩

/- English proof (translation)
Establish `h1 : N • v x = 0` using `by rw [← v.map_pow, h, v.map_one]`. Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_pow hN.ne']`. Conclude with `zero_ne_one h`.

Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)`. Rewrite `h1` using `[← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero]`. Rewrite using `[← hr, h1.resolve_left hN.ne', WithTop.coe_zero]`.
-/
theorem val_eq_zero_of_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (N : ℕ)
    (hN : 0 < N) (h : x ^ N = 1) : v x = 0 := by
  have h1 : N • v x = 0 := by rw [← v.map_pow, h, v.map_one]
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h1
  rw [← hr, h1.resolve_left hN.ne', WithTop.coe_zero]

/- English proof (translation)
Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[v.map_zero]`. Conclude with `WithTop.top_ne_zero h`. Establish `h1 : v (x ^ m) = 0` using `by rw [v.map_pow, h, smul_zero]`.

Establish `h2` using `v.map_mul (x ^ m) (x ^ m)⁻¹`. Rewrite `h2` using `[mul_inv_cancel₀ (pow_ne_zero _ hx), v.map_one, h1, zero_add]`. Conclude with `h2.symm`.
-/
theorem val_inv_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (m : ℕ)
    (h : v x = 0) : v (x ^ m)⁻¹ = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at h
    exact WithTop.top_ne_zero h
  have h1 : v (x ^ m) = 0 := by rw [v.map_pow, h, smul_zero]
  have h2 := v.map_mul (x ^ m) (x ^ m)⁻¹
  rw [mul_inv_cancel₀ (pow_ne_zero _ hx), v.map_one, h1, zero_add] at h2
  exact h2.symm

end GlobalTheory.TorsRecov

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

/- English proof (translation)
Introduce `F _ _ _ v X _ _ _ n hn hv a ha S hS c hc lim hlim q`. Establish `hB : ∀ α : X, ∃ j : ℕ, (¬ ∀ k, ∃ z, α = c k + n ^ k • z) → ¬ ∃ z, α = c j + n ^ j • z`. Introduce `α`. Distinguish the cases in `h : ∀ k, ∃ z, α = c k + n ^ k • z`. Conclude with `⟨0, fun h' => (h' h).elim⟩`.

Take `⟨j, hj⟩` from `not_forall.1 h`. Conclude with `⟨j, fun _ => hj⟩`. Use `choose j hj using hB`. Use `⟨(ha q).toFinset.sup j, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hN : 0 < n ^ k` using `pow_pos (by omega) k`.

Establish `hn0 : (n : F) ≠ 0` using `by exact_mod_cast (by omega : n ≠ 0)`. Establish `key : ∀ α : X, (∃ z, α = c k + n ^ k • z) → (¬ ∀ k, ∃ z, α = c k + n ^ k • z) → (q : WithTop ℚ) ≤ v (a α)`. Introduce `α h1 h2`. Assume the negation of the conclusion as `h3`. Establish `h4 : α ∈ (ha q).toFinset` using `(ha q).mem_toFinset.2 (not_le.1 h3)`.

Conclude with `hj α h2 (GlobalTheory.TorsRecov.class_mono X n c hc α _ k ((Finset.le_sup h4).trans hk) h1)`. Use `haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} := Nat.finite_of_card_ne_zero (by`. Rewrite using `[GlobalTheory.TorsRecov.card_tors F X _ hN]`. Conclude with `pow_ne_zero _ hN.ne')`. Use `letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `hS'` using `fun t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} => hS t.1 ⟨k, t.2⟩ q`. Use `choose S₀ hS₀ using hS'`. Establish `main : ∀ T : Finset X, (∀ t, S₀ t ⊆ T) → (q : WithTop ℚ) ≤ v (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) → (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k …`. Introduce `T hT h`.

Establish `e1 : ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α = (n : F) ^ (k * Module.finrank ℤ X) * ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Simplify using `only [← _root_.mul_assoc]`.

Rewrite using `[← Finset.sum_mul, GlobalTheory.TorsRecov.sum_tors F X _ hN]`. Use `split_ifs`. Rewrite using `[Nat.cast_pow, ← pow_mul]`. Rewrite using `[zero_mul]`. Establish `e2 : lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1 = (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Mult …`.

Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[e1, inv_mul_cancel_left₀ (pow_ne_zero _ hn0)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use `v.map_le_sub h ?_` and prove the remaining obligations.

Rewrite using `[v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hv, zero_add]`. Use `v.map_le_sum fun t _ => ?_` and prove the remaining obligations. Rewrite using `[v.map_mul, GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN, zero_add]`. Conclude with `hS₀ t T (hT t)`. Rewrite using `[← Units.val_pow_eq_pow_val, inv_pow, ← MonoidHom.pow_apply, t.2]`.

Simplify using the standard rewrite rules. Break down `hlim with ⟨χ, hχ, rfl⟩ | ⟨hno, rfl⟩` into its components or cases. Use `main (insert χ (Finset.univ.biUnion S₀)) (fun t => ?_) ?_` and prove the remaining obligations. Conclude with `(Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)).trans (Finset.subset_insert _ _)`. Rewrite using `[← Finset.add_sum_erase _ a (a := χ) (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hχ k⟩), sub_add_cancel_left, v.map_neg]`.

Use `v.map_le_sum fun α hα => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_erase.1 hα`. Use `key α (Finset.mem_filter.1 h2).2 fun h3 => h1 ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `GlobalTheory.TorsRecov.eq_zero_of_div X n hn _ fun m => ?_` and prove the remaining obligations.

Take `⟨z, hz⟩` from `h3 m`. Take `⟨w, hw⟩` from `hχ m`. Conclude with `⟨z - w, by rw [hz, hw, smul_sub, add_sub_add_left_eq_sub]⟩`. Use `main (Finset.univ.biUnion S₀) (fun t => Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)) ?_` and prove the remaining obligations. Rewrite using `[zero_sub, v.map_neg]`.

Use `v.map_le_sum fun α hα => ?_` and prove the remaining obligations. Conclude with `key α (Finset.mem_filter.1 hα).2 fun h3 => hno ⟨α, h3⟩`.
-/
theorem GlobalTheory.coeff_recovery_by_torsion_averages : ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n → v (n : F) = 0 → ∀ a : X → F, NullV v a → ∀ S : (Multiplicative X →* Fˣ) → F, (∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) → SumV v (fun α => (t (Multiplicative.ofAdd α)).val * a α) (S t)) → ∀ c : ℕ → X, (∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) → ∀ (lim : F), ((∃ χ, (∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = a χ) ∨ ((¬ ∃ χ, ∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = 0)) → ∀ q : ℚ, ∃ k₀, ∀ k ≥ k₀, (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ᶠ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
  intro F _ _ _ v X _ _ _ n hn hv a ha S hS c hc lim hlim q
  classical
  have hB : ∀ α : X, ∃ j : ℕ, (¬ ∀ k, ∃ z, α = c k + n ^ k • z) → ¬ ∃ z, α = c j + n ^ j • z := by
    intro α
    by_cases h : ∀ k, ∃ z, α = c k + n ^ k • z
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨j, hj⟩ := not_forall.1 h
      exact ⟨j, fun _ => hj⟩
  choose j hj using hB
  refine ⟨(ha q).toFinset.sup j, fun k hk => ?_⟩
  have hN : 0 < n ^ k := pow_pos (by omega) k
  have hn0 : (n : F) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have key : ∀ α : X, (∃ z, α = c k + n ^ k • z) → (¬ ∀ k, ∃ z, α = c k + n ^ k • z) →
      (q : WithTop ℚ) ≤ v (a α) := by
    intro α h1 h2
    by_contra h3
    have h4 : α ∈ (ha q).toFinset := (ha q).mem_toFinset.2 (not_le.1 h3)
    exact hj α h2 (GlobalTheory.TorsRecov.class_mono X n c hc α _ k ((Finset.le_sup h4).trans hk) h1)
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype]
  have hS' := fun t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} => hS t.1 ⟨k, t.2⟩ q
  choose S₀ hS₀ using hS'
  have main : ∀ T : Finset X, (∀ t, S₀ t ⊆ T) →
      (q : WithTop ℚ) ≤ v (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) →
      (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
    intro T hT h
    have e1 : ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α =
        (n : F) ^ (k * Module.finrank ℤ X) *
          ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [← _root_.mul_assoc]
      rw [← Finset.sum_mul, GlobalTheory.TorsRecov.sum_tors F X _ hN]
      split_ifs
      · rw [Nat.cast_pow, ← pow_mul]
      · rw [zero_mul]
    have e2 : lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1 =
        (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) -
        ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            (S t.1 - ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [e1, inv_mul_cancel_left₀ (pow_ne_zero _ hn0)]
      ring
    rw [e2]
    refine v.map_le_sub h ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hv, zero_add]
    refine v.map_le_sum fun t _ => ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN, zero_add]
    · exact hS₀ t T (hT t)
    · rw [← Units.val_pow_eq_pow_val, inv_pow, ← MonoidHom.pow_apply, t.2]
      simp
  rcases hlim with ⟨χ, hχ, rfl⟩ | ⟨hno, rfl⟩
  · refine main (insert χ (Finset.univ.biUnion S₀)) (fun t => ?_) ?_
    · exact (Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)).trans (Finset.subset_insert _ _)
    · rw [← Finset.add_sum_erase _ a (a := χ)
        (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hχ k⟩), sub_add_cancel_left, v.map_neg]
      refine v.map_le_sum fun α hα => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hα
      refine key α (Finset.mem_filter.1 h2).2 fun h3 => h1 ?_
      rw [← sub_eq_zero]
      refine GlobalTheory.TorsRecov.eq_zero_of_div X n hn _ fun m => ?_
      obtain ⟨z, hz⟩ := h3 m
      obtain ⟨w, hw⟩ := hχ m
      exact ⟨z - w, by rw [hz, hw, smul_sub, add_sub_add_left_eq_sub]⟩
  · refine main (Finset.univ.biUnion S₀)
      (fun t => Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)) ?_
    rw [zero_sub, v.map_neg]
    refine v.map_le_sum fun α hα => ?_
    exact key α (Finset.mem_filter.1 hα).2 fun h3 => hno ⟨α, h3⟩
