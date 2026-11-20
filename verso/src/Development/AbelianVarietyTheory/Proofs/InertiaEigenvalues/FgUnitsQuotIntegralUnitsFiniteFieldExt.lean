import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

open GlobalTheory.UnitLemma Polynomial IsDedekindDomain

noncomputable section
namespace GlobalTheory.FieldUnitsQuotFG

/- English proof (translation)
Set `e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ)` to `{ toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v)) invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v) left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl }`. Use `haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv`. Establish `h1 : φ.range.FG`. Rewrite using `[Subgroup.fg_iff_add_fg]`. Rewrite using `[← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]`.

Conclude with `(Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)`. Use `haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1`. Conclude with `Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom) (QuotientGroup.quotientKerEquivRange φ).symm.surjective`.
-/
theorem fg_quot_ker {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by
  let e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ) :=
    { toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v))
      invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv
  have h1 : φ.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]
    exact (Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)
  haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1
  exact Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]

/- English proof (translation)
Use `set C := integralClosure K.O L`. Establish `hinj : Function.Injective (algebraMap K.O C)`. Introduce `a b h`. Establish `h2 : algebraMap K.O L a = algebraMap K.O L b`. Rewrite using `[IsScalarTower.algebraMap_apply K.O C L a, h, ← IsScalarTower.algebraMap_apply]`.

Rewrite `h2` using `[IsScalarTower.algebraMap_apply K.O K.E L, IsScalarTower.algebraMap_apply K.O K.E L]`. Conclude with `IsFractionRing.injective K.O K.E ((algebraMap K.E L).injective h2)`. Use `set I := Ideal.map (algebraMap K.O C) (IsLocalRing.maximalIdeal K.O)`. Establish `hI : I ≠ 0`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`.

Introduce `h0`. Establish `: algebraMap K.O C ϖ ∈ I` using `Ideal.mem_map_of_mem _ (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)`. Rewrite `this` using `[h0, Submodule.zero_eq_bot, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero (hinj (this.trans (map_zero _).symm))`. Establish `hall : ∀ v : HeightOneSpectrum C, v.asIdeal ∣ I`.

Introduce `v`. Rewrite using `[Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]`. Establish `hp : (v.asIdeal.comap (algebraMap K.O C)).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hne : v.asIdeal.comap (algebraMap K.O C) ≠ ⊥`. Introduce `h`.

Conclude with `v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)`. Establish `hmax` using `hp.isMaximal hne`. Rewrite using `[IsLocalRing.eq_maximalIdeal hmax]`. Use `Ideal.finite_factors hI` as an intermediate fact. Establish `huniv : (Set.univ : Set (HeightOneSpectrum C)) = {v | v.asIdeal ∣ I}`.

Use extensionality with `v`. Simplify using `[hall v]`. Conclude with `Set.finite_univ_iff.1 (huniv ▸ this)`.
-/
theorem finite_spec [IsDedekindDomain (integralClosure K.O L)] :
    Finite (HeightOneSpectrum (integralClosure K.O L)) := by
  set C := integralClosure K.O L
  have hinj : Function.Injective (algebraMap K.O C) := by
    intro a b h
    have h2 : algebraMap K.O L a = algebraMap K.O L b := by
      rw [IsScalarTower.algebraMap_apply K.O C L a, h, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply K.O K.E L, IsScalarTower.algebraMap_apply K.O K.E L] at h2
    exact IsFractionRing.injective K.O K.E ((algebraMap K.E L).injective h2)
  set I := Ideal.map (algebraMap K.O C) (IsLocalRing.maximalIdeal K.O)
  have hI : I ≠ 0 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    intro h0
    have : algebraMap K.O C ϖ ∈ I :=
      Ideal.mem_map_of_mem _ (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at this
    exact hϖ.ne_zero (hinj (this.trans (map_zero _).symm))
  have hall : ∀ v : HeightOneSpectrum C, v.asIdeal ∣ I := by
    intro v
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have hp : (v.asIdeal.comap (algebraMap K.O C)).IsPrime := Ideal.comap_isPrime _ _
    have hne : v.asIdeal.comap (algebraMap K.O C) ≠ ⊥ := by
      intro h
      exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    have hmax := hp.isMaximal hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  have := Ideal.finite_factors hI
  have huniv : (Set.univ : Set (HeightOneSpectrum C)) = {v | v.asIdeal ∣ I} := by
    ext v; simp [hall v]
  exact Set.finite_univ_iff.1 (huniv ▸ this)

def valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    Lˣ →* (HeightOneSpectrum (integralClosure K.O L) → Multiplicative ℤ) :=
  Pi.monoidHom fun v => WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) : L →* WithZero (Multiplicative ℤ)))

/- English proof (translation)
Use `show ((WithZero.unitsWithZeroEquiv (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) : L →* WithZero (Multiplicative ℤ)) x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _`. Rewrite using `[WithZero.coe_unitsWithZeroEquiv_eq_units_val]`. Both sides reduce to the same expression.
-/
theorem valHom_apply [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L]
    (x : Lˣ) (v : HeightOneSpectrum (integralClosure K.O L)) :
    ((valHom K L x v : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.valuation L (x : L) := by
  show ((WithZero.unitsWithZeroEquiv (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) :
    L →* WithZero (Multiplicative ℤ)) x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker]`. Establish `key : ∀ y : L, IsIntegral K.O y ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L y ≤ 1`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy v`. Establish `: y = algebraMap (integralClosure K.O L) L ⟨y, hy⟩` using `rfl`. Rewrite using `[this]`. Conclude with `v.valuation_le_one _`. Introduce `h`.

Take `⟨c, hc⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one L y h`. Rewrite using `[← hc]`. Conclude with `c.2`. Establish `h1 : valHom K L x = 1 ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L (x : L) = 1`. Rewrite using `[funext_iff]`.

Use `forall_congr' fun v => ?_` and prove the remaining obligations. Rewrite using `[← valHom_apply, Pi.one_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, WithZero.coe_one]`.

Introduce `h`. Conclude with `WithZero.coe_injective (h.trans WithZero.coe_one.symm)`. Rewrite using `[h1]`. Use `show _ ↔ IsIntegral K.O (x : L) ∧ IsIntegral K.O ((x⁻¹ : Lˣ) : L)`. Rewrite using `[key, key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun v => (h v).le, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]`. Introduce and unpack `⟨ha, hb⟩ v`.

Apply `le_antisymm (ha v)` to reduce the goal to its premises. Establish `hx : v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ker_valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    (valHom K L).ker = intUnits K.O L := by
  ext x
  rw [MonoidHom.mem_ker]
  have key : ∀ y : L, IsIntegral K.O y ↔
      ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L y ≤ 1 := by
    intro y
    constructor
    · intro hy v
      have : y = algebraMap (integralClosure K.O L) L ⟨y, hy⟩ := rfl
      rw [this]
      exact v.valuation_le_one _
    · intro h
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L y h
      rw [← hc]
      exact c.2
  have h1 : valHom K L x = 1 ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L (x : L) = 1 := by
    rw [funext_iff]
    refine forall_congr' fun v => ?_
    rw [← valHom_apply, Pi.one_apply]
    constructor
    · intro h
      rw [h, WithZero.coe_one]
    · intro h
      exact WithZero.coe_injective (h.trans WithZero.coe_one.symm)
  rw [h1]
  show _ ↔ IsIntegral K.O (x : L) ∧ IsIntegral K.O ((x⁻¹ : Lˣ) : L)
  rw [key, key]
  constructor
  · intro h
    refine ⟨fun v => (h v).le, fun v => ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
  · rintro ⟨ha, hb⟩ v
    apply le_antisymm (ha v)
    have hx : v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc 1 = v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) := hx.symm
      _ ≤ v.valuation L (x : L) * 1 := by gcongr; exact hb v
      _ = v.valuation L (x : L) := mul_one _

/- English proof (translation)
Introduce `K L _ _ _ _ _`. Use `haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L`. Use `haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L`. Use `haveI := finite_spec K L`. Rewrite using `[← ker_valHom K L]`.

Conclude with `fg_quot_ker _`.
-/
theorem fg_units_quot : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
    [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  intro K L _ _ _ _ _
  haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L
  haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L
  haveI := finite_spec K L
  rw [← ker_valHom K L]
  exact fg_quot_ker _

end GlobalTheory.FieldUnitsQuotFG
