import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
import GroundTheory.FunctionField.ValuationAevalSubCoeffZeroLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

abbrev Divisor := Place k K →₀ ℤ

variable {k K}

namespace Divisor

noncomputable def deg : Divisor k K →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

/- English proof (translation)
Simplify using `[deg, Finsupp.liftAddHom_apply]`. Use the proof step `@[simp]`.
-/
theorem deg_apply (D : Divisor k K) : deg D = D.sum fun v n => n * v.deg := by
  simp [deg, Finsupp.liftAddHom_apply]

@[simp]
/- English proof (translation)
Simplify using `[deg]`.
-/
theorem deg_single (v : Place k K) (n : ℤ) : deg (Finsupp.single v n) = n * v.deg := by
  simp [deg]

/- English proof (translation)
Rewrite using `[deg_apply, Finsupp.sum]`.
-/
theorem deg_eq_sum (D : Divisor k K) : deg D = ∑ v ∈ D.support, D v * v.deg := by
  rw [deg_apply, Finsupp.sum]

/- English proof (translation)
Rewrite using `[deg_eq_sum]`. Conclude with `Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using Finsupp.le_def.1 hD v) (Int.natCast_nonneg _)`.
-/
theorem deg_nonneg {D : Divisor k K} (hD : 0 ≤ D) : 0 ≤ deg D := by
  rw [deg_eq_sum]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using Finsupp.le_def.1 hD v)
    (Int.natCast_nonneg _)

variable [IsFunctionField k K]

/- English proof (translation)
Rewrite `h` using `[deg_eq_sum]`. Establish `hnn : ∀ v ∈ D.support, 0 ≤ D v * v.deg` using `fun v _ => mul_nonneg (by simpa using Finsupp.le_def.1 hD v) (Int.natCast_nonneg _)`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 h`. Use extensionality with `v`. Distinguish the cases in `hv : v ∈ D.support`.

Use `h0 v hv` as an intermediate fact. Establish `hdeg : (0 : ℤ) < v.deg` using `by exact_mod_cast v.deg_pos`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Simplify using `using h'`. Use linear arithmetic over natural numbers and integers.

Simplify using `using hv`.
-/
theorem eq_zero_of_deg_eq_zero {D : Divisor k K} (hD : 0 ≤ D) (h : deg D = 0) : D = 0 := by
  rw [deg_eq_sum] at h
  have hnn : ∀ v ∈ D.support, 0 ≤ D v * v.deg := fun v _ =>
    mul_nonneg (by simpa using Finsupp.le_def.1 hD v) (Int.natCast_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext v
  by_cases hv : v ∈ D.support
  · have := h0 v hv
    have hdeg : (0 : ℤ) < v.deg := by exact_mod_cast v.deg_pos
    rcases mul_eq_zero.1 this with h' | h'
    · simpa using h'
    · omega
  · simpa using hv

end Divisor

variable [IsFunctionField k K]

noncomputable def divisor (x : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun v : Place k K => v.ord x) (Place.finite_ord_ne_zero x)

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem divisor_apply (x : K) (v : Place k K) : divisor x v = v.ord x := rfl

@[simp]
/- English proof (translation)
Use extensionality with `v`. Simplify using the standard rewrite rules. Use the proof step `@[simp]`.
-/
theorem divisor_zero : divisor (0 : K) = (0 : Divisor k K) := by
  ext v; simp

@[simp]
/- English proof (translation)
Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem divisor_one : divisor (1 : K) = (0 : Divisor k K) := by
  ext v; simp

/- English proof (translation)
Use extensionality with `v`. Simplify using `[v.ord_mul hx hy]`. Use the proof step `@[simp]`.
-/
theorem divisor_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    divisor (x * y) = (divisor x + divisor y : Divisor k K) := by
  ext v; simp [v.ord_mul hx hy]

@[simp]
/- English proof (translation)
Use extensionality with `v`. Simplify using `[Place.ord_inv]`.
-/
theorem divisor_inv (x : K) : divisor x⁻¹ = -(divisor x : Divisor k K) := by
  ext v; simp [Place.ord_inv]

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, divisor_mul hx (inv_ne_zero hy), divisor_inv, sub_eq_add_neg]`.
-/
theorem divisor_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    divisor (x / y) = (divisor x - divisor y : Divisor k K) := by
  rw [div_eq_mul_inv, divisor_mul hx (inv_ne_zero hy), divisor_inv, sub_eq_add_neg]

/- English proof (translation)
Use extensionality with `v`. Simplify using `[v.ord_eq_zero_of_isAlgebraic hx hx0]`.
-/
theorem divisor_eq_zero_of_isAlgebraic {x : K} (hx : IsAlgebraic k x) (hx0 : x ≠ 0) :
    divisor x = (0 : Divisor k K) := by
  ext v; simp [v.ord_eq_zero_of_isAlgebraic hx hx0]

noncomputable def divisorHom : Additive Kˣ →+ Divisor k K where
  toFun x := divisor ((x.toMul : Kˣ) : K)
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, Units.val_mul]
    exact divisor_mul (Additive.toMul x).ne_zero (Additive.toMul y).ne_zero

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem divisorHom_apply (x : Kˣ) : divisorHom (Additive.ofMul x) = (divisor (x : K) : Divisor k K) :=
  rfl

variable (k K) in

noncomputable def principalDivisors : AddSubgroup (Divisor k K) := (divisorHom (k := k)).range

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, (Additive.toMul x).ne_zero, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨Additive.ofMul (Units.mk0 x hx), rfl⟩`.
-/
theorem mem_principalDivisors {D : Divisor k K} :
    D ∈ principalDivisors k K ↔ ∃ x : K, x ≠ 0 ∧ divisor x = D := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (Additive.toMul x).ne_zero, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 x hx), rfl⟩

noncomputable def zeroDivisor (x : K) : Divisor k K := divisor x ⊔ 0

noncomputable def poleDivisor (x : K) : Divisor k K := divisor x⁻¹ ⊔ 0

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem zeroDivisor_apply (x : K) (v : Place k K) :
    zeroDivisor x v = max (v.ord x) 0 := rfl

@[simp]
/- English proof (translation)
Simplify using `[poleDivisor, Finsupp.sup_apply]`.
-/
theorem poleDivisor_apply (x : K) (v : Place k K) :
    poleDivisor x v = max (-v.ord x) 0 := by
  simp [poleDivisor, Finsupp.sup_apply]

/- English proof (translation)
The claim follows from `Finsupp.le_def.2 fun v => by simp`.
-/
theorem zeroDivisor_nonneg (x : K) : (0 : Divisor k K) ≤ zeroDivisor x :=
  Finsupp.le_def.2 fun v => by simp

/- English proof (translation)
The claim follows from `Finsupp.le_def.2 fun v => by simp @[simp]`.
-/
theorem poleDivisor_nonneg (x : K) : (0 : Divisor k K) ≤ poleDivisor x :=
  Finsupp.le_def.2 fun v => by simp

@[simp]
/- English proof (translation)
Simplify using `[poleDivisor, zeroDivisor]`. Use the proof step `@[simp]`.
-/
theorem poleDivisor_inv (x : K) : poleDivisor x⁻¹ = (zeroDivisor x : Divisor k K) := by
  simp [poleDivisor, zeroDivisor]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zeroDivisor_inv (x : K) : zeroDivisor x⁻¹ = (poleDivisor x : Divisor k K) := rfl

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply, poleDivisor_apply, divisor_apply]`. Break down `le_total 0 (v.ord x) with h | h` into its components or cases. Rewrite using `[max_eq_left h, max_eq_right (by omega)]; ring`. Rewrite using `[max_eq_right h, max_eq_left (by omega)]; ring`.
-/
theorem zeroDivisor_sub_poleDivisor (x : K) :
    zeroDivisor x - poleDivisor x = (divisor x : Divisor k K) := by
  ext v
  simp only [Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply, poleDivisor_apply, divisor_apply]
  rcases le_total 0 (v.ord x) with h | h
  · rw [max_eq_left h, max_eq_right (by omega)]; ring
  · rw [max_eq_right h, max_eq_left (by omega)]; ring

namespace Divisor

def L (D : Divisor k K) : Submodule k K where
  carrier := {z | ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v)}
  add_mem' {a b} ha hb v := Valuation.map_add_le _ (ha v) (hb v)
  zero_mem' v := by rw [map_zero]; exact zero_le
  smul_mem' c z hz v := by
    rw [Algebra.smul_def, map_mul]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero, zero_mul]; exact zero_le
    · rw [v.valuation_algebraMap' hc, one_mul]; exact hz v

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_L {D : Divisor k K} {z : K} :
    z ∈ L D ↔ ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v) := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_L, Finsupp.le_def]`. Use `forall_congr' fun v => ?_` and prove the remaining obligations. Rewrite using `[v.valuation_le_exp_iff hz]`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divisor_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_L_iff_le {D : Divisor k K} {z : K} (hz : z ≠ 0) :
    z ∈ L D ↔ 0 ≤ divisor z + D := by
  rw [mem_L, Finsupp.le_def]
  refine forall_congr' fun v => ?_
  rw [v.valuation_le_exp_iff hz]
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divisor_apply]
  omega

/- English proof (translation)
Introduce `_z hz v` and use `(hz v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 h v))`.
-/
theorem L_mono {D E : Divisor k K} (h : D ≤ E) : L D ≤ L E := fun _z hz v =>
  (hz v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 h v))

/- English proof (translation)
Rewrite using `[Place.isAlgebraic_iff_forall_mem, mem_L]`. Use `forall_congr' fun v => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero, v.valuation_le_one_iff]`.
-/
theorem mem_L_zero {z : K} : z ∈ L (0 : Divisor k K) ↔ IsAlgebraic k z := by
  rw [Place.isAlgebraic_iff_forall_mem, mem_L]
  refine forall_congr' fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero, v.valuation_le_one_iff]

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hz0`. Establish `hall : ∀ w : Place k K, z ∈ w.ring` using `fun w => (w.valuation_le_one_iff z).1 ((hz w).trans (by`.

Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Simplify using `using Finsupp.le_def.1 hD w))`. Establish `h0` using `v.ord_eq_zero_of_isAlgebraic (Place.isAlgebraic_iff_forall_mem.2 hall) hz0`. Use `hz v` as an intermediate fact. Rewrite `this` using `[v.valuation_le_exp_iff hz0, h0]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem L_eq_bot_of_nonpos {D : Divisor k K} (hD : D ≤ 0) {v : Place k K} (hv : D v < 0) :
    L D = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  by_contra hz0
  have hall : ∀ w : Place k K, z ∈ w.ring := fun w =>
    (w.valuation_le_one_iff z).1 ((hz w).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simpa using Finsupp.le_def.1 hD w))
  have h0 := v.ord_eq_zero_of_isAlgebraic (Place.isAlgebraic_iff_forall_mem.2 hall) hz0
  have := hz v
  rw [v.valuation_le_exp_iff hz0, h0] at this
  omega

/- English proof (translation)
Use `set E := D + Finsupp.single v 1 with hE`. Establish `hEv : E v = D v + 1` using `by simp [E]`. Establish `hEw : ∀ w, w ≠ v → E w = D w` using `fun w hw => by`. Simplify using `[E, Ne.symm hw]`. Take `⟨t, ht⟩` from `v.valuation_surjective (WithZero.exp (-(D v + 1)))`.

Establish `hmem : ∀ z : L E, t * (z : K) ∈ v.ring` using `fun z => by`. Rewrite using `[← v.valuation_le_one_iff, map_mul, ht]`. Combine the equalities or inequalities in the displayed calculation. Set `φ : L E →ₗ[k] v.ResidueField` to `{ toFun := fun z => IsLocalRing.residue v.ring ⟨t * z, hmem z⟩ map_add' := fun a b => by`. Rewrite using `[← map_add]`.

Use `congr 1`. Use `ext`. Simplify using `[mul_add]`. Use the proof step `map_smul' := fun c a => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, IsScalarTower.algebraMap_apply k v.ring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]`.

Use `congr 1`. Use `ext`. Express the relevant statement in the definitionally equal form `t * ((c • a : L E) : K) = (algebraMap k v.ring c : K) * (t * a)`. Rewrite using `[Submodule.coe_smul, Algebra.smul_def, Place.coe_algebraMap_apply]`. Use `ring }`.

Establish `hker : ∀ z : L E, φ z = 0 ↔ (z : K) ∈ L D`. Introduce `z`. Express the relevant statement in the definitionally equal form `IsLocalRing.residue v.ring ⟨t * z, hmem z⟩ = 0 ↔ _`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Express the relevant statement in the definitionally equal form `v.ring.valuation (t * z) < 1 ↔ _`.

Rewrite using `[← v.valuation_lt_one_iff, map_mul, ht]`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Distinguish the cases in `hw : w = v`. Rewrite using `[hw]`.

Distinguish the cases in `hz : (z : K) = 0`. Rewrite using `[hz, map_zero]`. Conclude with `zero_le`. Rewrite `h` using `[v.valuation_eq_exp_neg_ord hz, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[v.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← hEw w hw]`. Conclude with `z.2 w`. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.

Set `ψ : LinearMap.ker φ →ₗ[k] L D` to `((L E).subtype.comp (LinearMap.ker φ).subtype).codRestrict (L D) fun z => (hker z.1).1 (LinearMap.mem_ker.1 z.2)`. Establish `hψ : Function.Injective ψ` using `fun a b h => by`. Establish `h'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (Subtype.ext h')`. Establish `: FiniteDimensional k (LinearMap.ker φ)` using `Module.Finite.of_injective ψ hψ`.

Establish `hrank` using `LinearMap.rank_range_add_rank_ker φ`. Establish `hfin : FiniteDimensional k (L E)`. Apply `Module.rank_lt_aleph0_iff.1` to reduce the goal to its premises. Rewrite using `[← hrank]`. Conclude with `Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)`.

Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Establish `h2 : finrank k (LinearMap.range φ) ≤ v.deg` using `Submodule.finrank_le _`. Establish `h3 : finrank k (LinearMap.ker φ) ≤ finrank k (L D)` using `LinearMap.finrank_le_finrank_of_injective hψ`. Use linear arithmetic over natural numbers and integers.
-/
theorem finiteDimensional_L_add_single (D : Divisor k K) (v : Place k K)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L (D + Finsupp.single v 1)) ∧
      finrank k (L (D + Finsupp.single v 1)) ≤ finrank k (L D) + v.deg := by
  classical
  set E := D + Finsupp.single v 1 with hE
  have hEv : E v = D v + 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    simp [E, Ne.symm hw]
  obtain ⟨t, ht⟩ := v.valuation_surjective (WithZero.exp (-(D v + 1)))
  have hmem : ∀ z : L E, t * (z : K) ∈ v.ring := fun z => by
    rw [← v.valuation_le_one_iff, map_mul, ht]
    calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
        ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (E v) := mul_le_mul' le_rfl (z.2 v)
      _ = 1 := by rw [hEv, ← WithZero.exp_add]; simp
  let φ : L E →ₗ[k] v.ResidueField :=
    { toFun := fun z => IsLocalRing.residue v.ring ⟨t * z, hmem z⟩
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext
        simp [mul_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, Algebra.smul_def,
          IsScalarTower.algebraMap_apply k v.ring v.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
        congr 1
        ext
        change t * ((c • a : L E) : K) = (algebraMap k v.ring c : K) * (t * a)
        rw [Submodule.coe_smul, Algebra.smul_def, Place.coe_algebraMap_apply]
        ring }
  have hker : ∀ z : L E, φ z = 0 ↔ (z : K) ∈ L D := by
    intro z
    change IsLocalRing.residue v.ring ⟨t * z, hmem z⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change v.ring.valuation (t * z) < 1 ↔ _
    rw [← v.valuation_lt_one_iff, map_mul, ht]
    constructor
    · intro h w
      by_cases hw : w = v
      · rw [hw]
        by_cases hz : (z : K) = 0
        · rw [hz, map_zero]; exact zero_le
        · rw [v.valuation_eq_exp_neg_ord hz, ← WithZero.exp_add, ← WithZero.exp_zero,
            WithZero.exp_lt_exp] at h
          rw [v.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]
          omega
      · rw [← hEw w hw]; exact z.2 w
    · intro h
      calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
          ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (D v) := mul_le_mul' le_rfl (h v)
        _ < 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  let ψ : LinearMap.ker φ →ₗ[k] L D :=
    ((L E).subtype.comp (LinearMap.ker φ).subtype).codRestrict (L D)
      fun z => (hker z.1).1 (LinearMap.mem_ker.1 z.2)
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have : FiniteDimensional k (LinearMap.ker φ) := Module.Finite.of_injective ψ hψ
  have hrank := LinearMap.rank_range_add_rank_ker φ
  have hfin : FiniteDimensional k (L E) := by
    apply Module.rank_lt_aleph0_iff.1
    rw [← hrank]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank k (LinearMap.range φ) ≤ v.deg := Submodule.finrank_le _
  have h3 : finrank k (LinearMap.ker φ) ≤ finrank k (L D) :=
    LinearMap.finrank_le_finrank_of_injective hψ
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `D E hDE hn _`. Use `deg_nonneg (sub_nonneg.2 hDE)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Consider the case `succ n ih`. Introduce `D E hDE hn hD`. Distinguish the cases in `hED : E = D`. Substitute `hED` using the available equality. Conclude with `⟨hD, by omega⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, D v < E v := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hED (le_antisymm (Finsupp.le_def.2 h) hDE)`. Use `set E' := E - Finsupp.single v 1 with hE'`.

Establish `hDE' : D ≤ E'` using `Finsupp.le_def.2 fun w => by`. Rewrite using `[hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers.

Use `Finsupp.le_def.1 hDE w` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hn' : deg (E' - D) < n`. Establish `h1 : deg (E' - D) = deg (E - D) - v.deg`. Rewrite using `[hE', map_sub, map_sub, map_sub, deg_single]`.

Expand and normalize the polynomial expressions, which then agree. Use `v.deg_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨hfin', hle'⟩` from `ih hDE' hn' hD`. Establish `hE : E = E' + Finsupp.single v 1` using `by rw [hE']; abel`.

Use `hfin'` as an intermediate fact. Take `⟨hfin, hle⟩` from `finiteDimensional_L_add_single E' v`. Rewrite `hfin`, `hle` using `[← hE]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hdeg : deg E = deg E' + v.deg` using `by rw [hE, map_add, deg_single, one_mul]`.

Establish `: (finrank k (L E) : ℤ) ≤ finrank k (L E') + v.deg` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem finiteDimensional_L_of_le_of_deg_lt (n : ℕ) :
    ∀ {D E : Divisor k K}, D ≤ E → deg (E - D) < n → FiniteDimensional k (L D) →
      FiniteDimensional k (L E) ∧
        (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D := by
  classical
  induction n with
  | zero =>
    intro D E hDE hn _
    have := deg_nonneg (sub_nonneg.2 hDE)
    omega
  | succ n ih =>
    intro D E hDE hn hD
    by_cases hED : E = D
    · subst hED
      exact ⟨hD, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, D v < E v := by
      by_contra h
      push Not at h
      exact hED (le_antisymm (Finsupp.le_def.2 h) hDE)
    set E' := E - Finsupp.single v 1 with hE'
    have hDE' : D ≤ E' := Finsupp.le_def.2 fun w => by
      rw [hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · have := Finsupp.le_def.1 hDE w; omega
    have hn' : deg (E' - D) < n := by
      have h1 : deg (E' - D) = deg (E - D) - v.deg := by
        rw [hE', map_sub, map_sub, map_sub, deg_single]; ring
      have := v.deg_pos
      omega
    obtain ⟨hfin', hle'⟩ := ih hDE' hn' hD
    have hE : E = E' + Finsupp.single v 1 := by rw [hE']; abel
    have := hfin'
    obtain ⟨hfin, hle⟩ := finiteDimensional_L_add_single E' v
    rw [← hE] at hfin hle
    refine ⟨hfin, ?_⟩
    have hdeg : deg E = deg E' + v.deg := by rw [hE, map_add, deg_single, one_mul]
    have : (finrank k (L E) : ℤ) ≤ finrank k (L E') + v.deg := by exact_mod_cast hle
    omega

/- English proof (translation)
The claim follows from `finiteDimensional_L_of_le_of_deg_lt ((deg (E - D)).toNat + 1) hDE (by omega) inferInstance`.
-/
theorem finiteDimensional_L_of_le {D E : Divisor k K} (hDE : D ≤ E)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L E) ∧
      (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  finiteDimensional_L_of_le_of_deg_lt ((deg (E - D)).toNat + 1) hDE (by omega) inferInstance

instance (D : Divisor k K) : FiniteDimensional k (L D) := by
  classical
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  have hbot : L (-Finsupp.single v 1 : Divisor k K) = ⊥ :=
    L_eq_bot_of_nonpos (v := v) (Finsupp.le_def.2 fun w => by
      have h := Finsupp.single_apply (a := v) (a' := w) (b := (1 : ℤ))
      simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs at h <;> omega) (by simp)
  have : FiniteDimensional k (L (-Finsupp.single v 1 : Divisor k K)) := by
    rw [hbot]; infer_instance
  have := (finiteDimensional_L_of_le
    (le_sup_right : (-Finsupp.single v 1 : Divisor k K) ≤ D ⊔ -Finsupp.single v 1)).1
  exact Module.Finite.of_injective
    (Submodule.inclusion (L_mono (le_sup_left : D ≤ D ⊔ -Finsupp.single v 1)))
    (Submodule.inclusion_injective _)

/- English proof (translation)
The claim follows from `(finiteDimensional_L_of_le hDE).2`.
-/
theorem finrank_L_le_of_le {D E : Divisor k K} (hDE : D ≤ E) :
    (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  (finiteDimensional_L_of_le hDE).2

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[mem_L_zero]`. Simplify using `[mem_algebraicClosure_iff]`.
-/
theorem L_zero :
    L (0 : Divisor k K) = Subalgebra.toSubmodule (algebraicClosure k K).toSubalgebra := by
  ext z
  rw [mem_L_zero]
  simp [mem_algebraicClosure_iff]

/- English proof (translation)
Rewrite using `[L_zero]`. Both sides reduce to the same expression.
-/
theorem finrank_L_zero : finrank k (L (0 : Divisor k K)) = finrank k (algebraicClosure k K) := by
  rw [L_zero]
  rfl

/- English proof (translation)
Use `finrank_L_le_of_le hD` as an intermediate fact. Rewrite `this` using `[finrank_L_zero, map_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_L_le_deg_add {D : Divisor k K} (hD : 0 ≤ D) :
    (finrank k (L D) : ℤ) ≤ deg D + finrank k (algebraicClosure k K) := by
  have := finrank_L_le_of_le hD
  rw [finrank_L_zero, map_zero] at this
  omega

/- English proof (translation)
Use `finrank_L_le_deg_add hD` as an intermediate fact. Rewrite `this` using `[hk, IntermediateField.finrank_bot]`. Conclude with `this` after adjusting the coercions.
-/
theorem finrank_L_le_deg_add_one (hk : algebraicClosure k K = ⊥) {D : Divisor k K}
    (hD : 0 ≤ D) : (finrank k (L D) : ℤ) ≤ deg D + 1 := by
  have := finrank_L_le_deg_add hD
  rw [hk, IntermediateField.finrank_bot] at this
  exact_mod_cast this

end Divisor

end GroundTheory.FunctionField
