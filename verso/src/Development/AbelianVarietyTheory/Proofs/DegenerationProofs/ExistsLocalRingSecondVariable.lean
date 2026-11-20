import Mathlib

namespace GlobalTheory.TwoVarValRing

/- English proof (translation)
Establish `h` using `MvPowerSeries.weightedOrder_eq_nat (f := f) (Pi.single s 1) (n := 0)`. Rewrite `h` using `[Nat.cast_zero]`. Rewrite using `[h, MvPowerSeries.X_dvd_iff]`. Simplify using `only [Finsupp.weight_single_one_apply, not_forall, Nat.not_lt_zero, false_imp_iff, implies_true, and_true]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, h1, h2⟩`. Conclude with `⟨m, h2, h1⟩`. Introduce and unpack `⟨m, h1, h2⟩`. Conclude with `⟨m, h2, h1⟩`.
-/
theorem not_X_dvd_iff_weightedOrder {σ R : Type} [DecidableEq σ] [Semiring R] (s : σ)
    (f : MvPowerSeries σ R) :
    ¬ MvPowerSeries.X s ∣ f ↔ f.weightedOrder (Pi.single s 1) = 0 := by
  have h := MvPowerSeries.weightedOrder_eq_nat (f := f) (Pi.single s 1) (n := 0)
  rw [Nat.cast_zero] at h
  rw [h, MvPowerSeries.X_dvd_iff]
  simp only [Finsupp.weight_single_one_apply, not_forall, Nat.not_lt_zero, false_imp_iff,
    implies_true, and_true]
  constructor
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩

/- English proof (translation)
Rewrite `*` using `[not_X_dvd_iff_weightedOrder]`. Rewrite using `[MvPowerSeries.weightedOrder_mul, hf, hg, add_zero]`.
-/
theorem not_X_dvd_mul {σ R : Type} [DecidableEq σ] [Semiring R] [NoZeroDivisors R] (s : σ)
    {f g : MvPowerSeries σ R} (hf : ¬ MvPowerSeries.X s ∣ f) (hg : ¬ MvPowerSeries.X s ∣ g) :
    ¬ MvPowerSeries.X s ∣ f * g := by
  rw [not_X_dvd_iff_weightedOrder] at *
  rw [MvPowerSeries.weightedOrder_mul, hf, hg, add_zero]

/- English proof (translation)
Rewrite using `[not_X_dvd_iff_weightedOrder, MvPowerSeries.weightedOrder_one]`.
-/
theorem not_X_dvd_one {σ R : Type} [DecidableEq σ] [Semiring R] [Nontrivial R] (s : σ) :
    ¬ MvPowerSeries.X s ∣ (1 : MvPowerSeries σ R) := by
  rw [not_X_dvd_iff_weightedOrder, MvPowerSeries.weightedOrder_one]

/- English proof (translation)
Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `h`. Use `h (Finsupp.single 0 1) (by simp)` as an intermediate fact. Simplify using `[MvPowerSeries.coeff_index_single_self_X] at this`.
-/
theorem not_X_one_dvd_X_zero (k : Type) [Field k] :
    ¬ MvPowerSeries.X 1 ∣ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro h
  have := h (Finsupp.single 0 1) (by simp)
  simp [MvPowerSeries.coeff_index_single_self_X] at this

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)` using `PowerSeries.HasSubst.X 0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb (PowerSeries.X_prime (R := k)).irreducible`. Rewrite using `[PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]`. Apply `not_X_dvd_mul` to reduce the goal to its premises. Introduce `h`.

Establish `hu : IsUnit ((u : PowerSeries k).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))`. Rewrite using `[← PowerSeries.coe_substAlgHom hs]`. Conclude with `u.isUnit.map _`. Conclude with `not_X_dvd_one (R := k) (1 : Fin 2) (h.trans hu.dvd)`. Proceed by induction on `n with`.

Consider the case `zero => simpa using not_X_dvd_one (R := k) (1 : Fin 2)`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `not_X_dvd_mul _ (ih (by simp)) (not_X_one_dvd_X_zero k)`.
-/
theorem not_X_one_dvd_subst (k : Type) [Field k] (b : PowerSeries k) (hb : b ≠ 0) :
    ¬ MvPowerSeries.X 1 ∣ b.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.X 0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb
    (PowerSeries.X_prime (R := k)).irreducible
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
  apply not_X_dvd_mul
  · intro h
    have hu : IsUnit ((u : PowerSeries k).subst
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) := by
      rw [← PowerSeries.coe_substAlgHom hs]
      exact u.isUnit.map _
    exact not_X_dvd_one (R := k) (1 : Fin 2) (h.trans hu.dvd)
  · induction n with
    | zero => simpa using not_X_dvd_one (R := k) (1 : Fin 2)
    | succ n ih =>
      rw [pow_succ]
      exact not_X_dvd_mul _ (ih (by simp)) (not_X_one_dvd_X_zero k)

noncomputable def locSecondVar (k : Type) [Field k] :
    Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)) where
  carrier := {x | ∃ u v : MvPowerSeries (Fin 2) k, ¬ MvPowerSeries.X 1 ∣ v ∧
    x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u}
  mul_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * u', v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_mul, map_mul, ← h, ← h']; ring
  add_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * v' + u' * v, v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap k _ r, 1, not_X_dvd_one _, ?_⟩
    rw [map_one, mul_one, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Establish `hu0 : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) u ≠ 0`. Rewrite using `[ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]`. Introduce and unpack `rfl`. Conclude with `hu (dvd_zero _)`. Establish `hx : (x : FractionRing (MvPowerSeries (Fin 2) k)) ≠ 0`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `hu0 h.symm`. Use `IsUnit.of_mul_eq_one (⟨(x : FractionRing (MvPowerSeries (Fin 2) k))⁻¹, v, u, hu, ?_⟩ : locSecondVar k) ?_` and prove the remaining obligations. Rewrite using `[← h, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]`.

Conclude with `Subtype.ext (mul_inv_cancel₀ hx)`.
-/
theorem isUnit_locSecondVar (k : Type) [Field k] (x : locSecondVar k) (u v : MvPowerSeries (Fin 2) k)
    (hu : ¬ MvPowerSeries.X 1 ∣ u)
    (h : (x : FractionRing (MvPowerSeries (Fin 2) k)) * algebraMap (MvPowerSeries (Fin 2) k) _ v
      = algebraMap (MvPowerSeries (Fin 2) k) _ u) : IsUnit x := by
  have hu0 : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) u
      ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hu (dvd_zero _)
  have hx : (x : FractionRing (MvPowerSeries (Fin 2) k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact hu0 h.symm
  refine IsUnit.of_mul_eq_one (⟨(x : FractionRing (MvPowerSeries (Fin 2) k))⁻¹, v, u, hu, ?_⟩ : locSecondVar k) ?_
  · rw [← h, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · exact Subtype.ext (mul_inv_cancel₀ hx)

instance isLocalRing_locSecondVar (k : Type) [Field k] : IsLocalRing (locSecondVar k) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨u, v, hv, h⟩ := x.2
  by_cases hu : MvPowerSeries.X 1 ∣ u
  · right
    refine isUnit_locSecondVar k _ (v - u) v (fun h' => hv ?_) ?_
    · simpa using dvd_add h' hu
    · rw [map_sub, ← h]
      push_cast
      ring
  · exact Or.inl (isUnit_locSecondVar k x u v hu h)

/- English proof (translation)
Introduce `k _ σ₀ σ₁ h₀ h₁`. Use `⟨locSecondVar k, inferInstance, fun x u v hv h => ⟨u, v, hv, h⟩, fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := PowerSeries k) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `⟨a.subst (MvPowerSeries.X 0), b.subst (MvPowerSeries.X 0), not_X_one_dvd_subst k b hb0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h₀, ← h₀, ← map_mul, div_mul_cancel₀]`. Rewrite using `[ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]` and apply the resulting hypothesis. Break down `ValuationRing.isInteger_or_isInteger (PowerSeries k) x with h | ⟨c, hc⟩` into its components or cases. Conclude with `h`. Distinguish the cases in `hx0 : x = 0`.

Conclude with `⟨0, by rw [hx0, map_zero]⟩`. Distinguish the cases in `hcu : IsUnit c`. Take `⟨d, hd⟩` from `hcu.exists_right_inv`. Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `: x⁻¹ * algebraMap (PowerSeries k) _ d = 1`.

Rewrite using `[← hc, ← map_mul, hd, map_one]`. Rewrite using `[← mul_one x, ← this, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]`. It suffices to derive a contradiction. Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)` using `PowerSeries.HasSubst.X 1`. Establish `hX : PowerSeries.X ∣ c`.

Rewrite using `[PowerSeries.X_dvd_iff]`. Assume the negation of the conclusion as `h0`. Conclude with `hcu (PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit h0))`. Take `⟨c', rfl⟩` from `hX`. Take `⟨u, v, hv, h⟩` from `hx`.

Apply `hv` to reduce the goal to its premises. Establish `h2 : v = (PowerSeries.X * c').subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) * u`. Apply `IsFractionRing.injective (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))` to reduce the goal to its premises. Rewrite using `[map_mul, ← h₁, hc, ← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx0, map_one, one_mul]`. Rewrite using `[h2, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, mul_assoc]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem exists_local_ring_second_variable : ∀ (k : Type) [Field k] (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k)), (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) → (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) → ∃ L : Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)), IsLocalRing L ∧ (∀ (x : FractionRing (MvPowerSeries (Fin 2) k)) (u v : MvPowerSeries (Fin 2) k), ¬ MvPowerSeries.X 1 ∣ v → x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u → x ∈ L) ∧ (∀ x, σ₀ x ∈ L) ∧ ∀ x, σ₁ x ∈ L → x ∈ Set.range (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := by
  intro k _ σ₀ σ₁ h₀ h₁
  refine ⟨locSecondVar k, inferInstance, fun x u v hv h => ⟨u, v, hv, h⟩, fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries k) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨a.subst (MvPowerSeries.X 0), b.subst (MvPowerSeries.X 0),
      not_X_one_dvd_subst k b hb0, ?_⟩
    rw [← h₀, ← h₀, ← map_mul, div_mul_cancel₀]
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  · rcases ValuationRing.isInteger_or_isInteger (PowerSeries k) x with h | ⟨c, hc⟩
    · exact h
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hcu : IsUnit c
      · obtain ⟨d, hd⟩ := hcu.exists_right_inv
        refine ⟨d, ?_⟩
        have : x⁻¹ * algebraMap (PowerSeries k) _ d = 1 := by
          rw [← hc, ← map_mul, hd, map_one]
        rw [← mul_one x, ← this, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
      · exfalso
        have hs : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
          PowerSeries.HasSubst.X 1
        have hX : PowerSeries.X ∣ c := by
          rw [PowerSeries.X_dvd_iff]
          by_contra h0
          exact hcu (PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit h0))
        obtain ⟨c', rfl⟩ := hX
        obtain ⟨u, v, hv, h⟩ := hx
        apply hv
        have h2 : v = (PowerSeries.X * c').subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) * u := by
          apply IsFractionRing.injective (MvPowerSeries (Fin 2) k)
            (FractionRing (MvPowerSeries (Fin 2) k))
          rw [map_mul, ← h₁, hc, ← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx0, map_one, one_mul]
        rw [h2, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, mul_assoc]
        exact dvd_mul_right _ _

end GlobalTheory.TwoVarValRing
