import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.GaloisValuations.GlobalB

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def Dec (A : ValuationSubring (Ω)) : Subgroup (G F Ω) := A.decompositionSubgroup F

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ σ • A = A := Iff.rfl

/- English proof (translation)
Establish `h` using `mem_Dec.mp hσ`. Establish `key : σ • x ∈ σ • A ↔ x ∈ A` using `ValuationSubring.smul_mem_pointwise_smul_iff`. Rewrite `key` using `[h]`. Conclude with `key`.
-/
theorem apply_mem_iff_of_mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  have h := mem_Dec.mp hσ
  have key : σ • x ∈ σ • A ↔ x ∈ A := ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h] at key
  exact key

/- English proof (translation)
Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]`. Simplify using `only [hy, false_or]`. Conclude with `⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩`.
-/
theorem valuation_lt_one_iff' (A : ValuationSubring (Ω)) (y : Ω) :
    A.valuation y < 1 ↔ y ∈ A ∧ (y = 0 ∨ y⁻¹ ∉ A) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le,
      Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
    simp only [hy, false_or]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ, apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]`.
-/
theorem valuation_apply_lt_one_iff {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (y : Ω) :
    A.valuation (σ y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ,
    apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]

/- English proof (translation)
Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.
-/
theorem mul_inv_apply {σ : G F Ω} (x : Ω) : σ ((σ⁻¹ : G F Ω) x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def Ine (A : ValuationSubring (Ω)) : Subgroup (G F Ω) where
  carrier := Inertia (F := F) A
  one_mem' := ⟨(Dec (F := F) A).one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨(Dec (F := F) A).mul_mem hσ hτ, fun x hx => ?_⟩
    have e : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
      simp [AlgEquiv.mul_apply, map_sub]
    rw [e]
    exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσ _).mpr (hτ' x hx)) (hσ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨(Dec (F := F) A).inv_mem hσ, fun x hx => ?_⟩
    have hy : A.valuation ((σ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hσ, mul_inv_apply]
      exact (A.valuation_le_one_iff x).mp hx
    have e : (σ⁻¹ : G F Ω) x - x = -(σ ((σ⁻¹ : G F Ω) x) - (σ⁻¹ : G F Ω) x) := by
      rw [mul_inv_apply]; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Ine {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Ine (F := F) A ↔ σ ∈ Inertia (F := F) A := Iff.rfl

/- English proof (translation)
Introduce `_ h` and use `(mem_Ine.mp h).1`.
-/
theorem Ine_le_Dec (A : ValuationSubring (Ω)) : Ine (F := F) A ≤ Dec (F := F) A := fun _ h => (mem_Ine.mp h).1

/- English proof (translation)
Use `⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).mul_mem hg hσ.1) ((Dec (F := F) A).inv_mem hg), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hy : A.valuation ((g⁻¹ : G F Ω) x) ≤ 1`. Rewrite using `[A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hg, mul_inv_apply]`. Conclude with `(A.valuation_le_one_iff x).mp hx`. Establish `e : (g * σ * g⁻¹) x - x = g (σ ((g⁻¹ : G F Ω) x) - (g⁻¹ : G F Ω) x)`.

Rewrite using `[map_sub, mul_inv_apply]`. Both sides reduce to the same expression. Rewrite using `[e, valuation_apply_lt_one_iff hg]`. Conclude with `hσ.2 _ hy`.
-/
theorem conj_mem_Ine {A : ValuationSubring (Ω)} {g σ : G F Ω} (hg : g ∈ Dec (F := F) A)
    (hσ : σ ∈ Ine (F := F) A) : g * σ * g⁻¹ ∈ Ine (F := F) A := by
  refine ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).mul_mem hg hσ.1) ((Dec (F := F) A).inv_mem hg), fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G F Ω) x) ≤ 1 := by
    rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hg, mul_inv_apply]
    exact (A.valuation_le_one_iff x).mp hx
  have e : (g * σ * g⁻¹) x - x = g (σ ((g⁻¹ : G F Ω) x) - (g⁻¹ : G F Ω) x) := by
    rw [map_sub, mul_inv_apply]; rfl
  rw [e, valuation_apply_lt_one_iff hg]
  exact hσ.2 _ hy

instance normal_Ine_subgroupOf (A : ValuationSubring (Ω)) :
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_Ine g.2 hn

variable (F Ω) in

def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))

variable (F Ω) in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cyc_eq_map_cycZ (l : ℕ) [Fact l.Prime] (σ : G F Ω) :
    cyc F Ω l σ = Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      (cycZ F Ω l σ) := rfl

variable (F Ω) in

/- English proof (translation)
The claim follows from `cyclotomicCharacter.continuous l F Ω`.
-/
theorem continuous_cycZ (l : ℕ) [Fact l.Prime] : Continuous (cycZ F Ω l) :=
  cyclotomicCharacter.continuous l F Ω

variable (F Ω) in

def cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) : G F Ω →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp (cycZ F Ω l)

def IsCC (c : G F Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

variable (Ω) in

def placeOf (v : HeightOneSpectrum (𝓞 F)) : ValuationSubring (Ω) :=
  @Classical.epsilon _ ⟨⊤⟩ (fun A => IsPlaceOver A v)

variable (Ω) in

def frobOf (v : HeightOneSpectrum (𝓞 F)) : G F Ω :=
  @Classical.epsilon _ ⟨1⟩ (fun σ : G F Ω => IsFrob (placeOf Ω v) (normV v) σ)

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable (Ω) in

def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

variable (Ω) in
/- English proof (translation)
The claim follows from `Subgroup.isClosed_topologicalClosure _`.
-/
theorem isClosed_NS : IsClosed (NS Ω S : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _

variable (Ω) in

abbrev GS := G F Ω ⧸ NS Ω S

variable (Ω) in

def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
/- English proof (translation)
Unfold `toGS`. Conclude with `continuous_quot_mk`.
-/
theorem continuous_toGS : Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

def locHom (A : ValuationSubring (Ω)) : Dec (F := F) A →* GS Ω S :=
  (toGS Ω S).comp (Dec (F := F) A).subtype

/- English proof (translation)
The claim follows from `(continuous_toGS Ω S).comp continuous_subtype_val`.
-/
theorem continuous_locHom (A : ValuationSubring (Ω)) :
    Continuous (locHom S A) := (continuous_toGS Ω S).comp continuous_subtype_val

def UnramOutside {H : Type*} [Group H] (ρ : G F Ω →* H) : Prop := ∀ σ ∈ NS Ω S, ρ σ = 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv A hA σ hσ`. Apply `h` to reduce the goal to its premises. Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]`. Conclude with `⟨v, hv, A, hA, hσ⟩`. Introduce `h σ hσ`. Establish `hker : NS Ω S ≤ ρ.ker`. Apply `Subgroup.topologicalClosure_minimal` to reduce the goal to its premises.

Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `τ hτ`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hτ`. Take `⟨v, hv, A, hA, hτ⟩` from `hτ`. Conclude with `MonoidHom.mem_ker.mpr (h v hv A hA τ hτ)`.

Rewrite using `[MonoidHom.coe_ker]`. Conclude with `isClosed_singleton.preimage hρ`. Conclude with `MonoidHom.mem_ker.mp (hker hσ)`.
-/
theorem unramOutside_iff {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    (ρ : G F Ω →* H) (hρ : Continuous ρ) :
    UnramOutside S ρ ↔ ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia (F := F) A, ρ σ = 1 := by
  constructor
  · intro h v hv A hA σ hσ
    apply h
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]
    exact ⟨v, hv, A, hA, hσ⟩
  · intro h σ hσ
    have hker : NS Ω S ≤ ρ.ker := by
      apply Subgroup.topologicalClosure_minimal
      · apply Subgroup.normalClosure_le_normal
        intro τ hτ
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hτ
        obtain ⟨v, hv, A, hA, hτ⟩ := hτ
        exact MonoidHom.mem_ker.mpr (h v hv A hA τ hτ)
      · rw [MonoidHom.coe_ker]
        exact isClosed_singleton.preimage hρ
    exact MonoidHom.mem_ker.mp (hker hσ)

end unram

section Basic₃

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (natCast_mem A n)`.
-/
theorem valuation_natCast_le_one (A : ValuationSubring (Ω)) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)

/- English proof (translation)
Unfold `Formalism.ConjugateSelfDual.IsPlaceOver at h`. Introduce `hlt`. Establish `hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω)`. Simplify using the standard rewrite rules. Rewrite `hlt` using `[← hc, h]`.

Conclude with `hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))`.
-/
theorem not_valuation_lt_one_of_isPlaceOver {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h
  intro hlt
  have hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω) := by
    simp
  rw [← hc, h] at hlt
  exact hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`. Establish `hN0 : l ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.

Establish `hspec` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one`. Use `set m := (((cyclotomicCharacter (Ω) l) (MulSemiringAction.toRingAut (G F Ω) (Ω) σ)) : ℤ_[l]).toZModPow n |>.val with hm`. Establish `hσζ : σ ζ = ζ ^ m` using `hspec`. Establish `hζA : A.valuation ζ ≤ 1` using `(valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le`. Establish `hlt` using `hσ ζ hζA`.

Rewrite `hlt` using `[hσζ]`. Establish `heq : ζ ^ m = ζ ^ q`. Use `eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl h n) ?_ ?_ hlt` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`.

Establish `heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ q` using `Units.ext (by simpa using heq)`. Establish `hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n)` using `IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)`. Rewrite `heq'` using `[pow_eq_pow_iff_modEq, ← hu.eq_orderOf]`. Rewrite using `[map_natCast]`. Use `show ((cyclotomicCharacter (Ω) l) (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n = _`.

Rewrite using `[← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l) (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n), ← hm]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'`.
-/
theorem cycZ_toZModPow_eq [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) (n : ℕ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n (q : ℤ_[l]) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  set m := (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ)) : ℤ_[l]).toZModPow n |>.val with hm
  have hσζ : σ ζ = ζ ^ m := hspec
  have hζA : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
  have hlt := hσ ζ hζA
  rw [hσζ] at hlt
  have heq : ζ ^ m = ζ ^ q := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl h n) ?_ ?_ hlt
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ q := Units.ext (by simpa using heq)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [map_natCast]
  show ((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n = _
  rw [← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n), ← hm]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'

/- English proof (translation)
Unfold `Formalism.ConjugateSelfDual.IsPlaceOver at h h'`. Establish `e : v.asIdeal = v'.asIdeal`. Use extensionality with `x`. Rewrite using `[← h x, ← h' x]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.ext e`.
-/
theorem eq_of_isPlaceOver {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h h'
  have e : v.asIdeal = v'.asIdeal := by
    ext x
    rw [← h x, ← h' x]
  exact IsDedekindDomain.HeightOneSpectrum.ext e

/- English proof (translation)
Take `⟨hσD, hσF⟩` from `hσ`. Take `⟨hτD, hτF⟩` from `hτ`. Establish `hσD' : σ ∈ Dec (F` using `F) A := mem_Dec.mpr hσD`. Establish `hτD' : τ ∈ Dec (F` using `F) A := mem_Dec.mpr hτD`. Use `mem_Ine.mpr ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hσD') hτD', fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[← valuation_apply_lt_one_iff hσD']`. Establish `e : σ ((σ⁻¹ * τ) x - x) = (τ x - x ^ q) - (σ x - x ^ q)`. Rewrite using `[map_sub, AlgEquiv.mul_apply, mul_inv_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hτF x hx) (hσF x hx))`.
-/
theorem inv_mul_mem_Ine_of_isFrob {A : ValuationSubring (Ω)} {q : ℕ} {σ τ : G F Ω}
    (hσ : IsFrob A q σ) (hτ : IsFrob A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hτD, hτF⟩ := hτ
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  have hτD' : τ ∈ Dec (F := F) A := mem_Dec.mpr hτD
  refine mem_Ine.mpr ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hσD') hτD', fun x hx => ?_⟩
  rw [← valuation_apply_lt_one_iff hσD']
  have e : σ ((σ⁻¹ * τ) x - x) = (τ x - x ^ q) - (σ x - x ^ q) := by
    rw [map_sub, AlgEquiv.mul_apply, mul_inv_apply]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hτF x hx) (hσF x hx))

/- English proof (translation)
Take `⟨hσD, hσF⟩` from `hσ`. Take `⟨hιD, hιI⟩` from `mem_Ine.mp hι`. Establish `hσD' : σ ∈ Dec (F` using `F) A := mem_Dec.mpr hσD`. Use `⟨mem_Dec.mp ((Dec (F := F) A).mul_mem hσD' hιD), fun x hx => ?_⟩` and prove the remaining obligations. Establish `e : (σ * ι) x - x ^ q = σ (ι x - x) + (σ x - x ^ q)`.

Rewrite using `[AlgEquiv.mul_apply, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσD' _).mpr (hιI x hx)) (hσF x hx)`.
-/
theorem isFrob_mul_of_mem_Ine {A : ValuationSubring (Ω)} {q : ℕ} {σ ι : G F Ω}
    (hσ : IsFrob A q σ) (hι : ι ∈ Ine (F := F) A) : IsFrob A q (σ * ι) := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hιD, hιI⟩ := mem_Ine.mp hι
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  refine ⟨mem_Dec.mp ((Dec (F := F) A).mul_mem hσD' hιD), fun x hx => ?_⟩
  have e : (σ * ι) x - x ^ q = σ (ι x - x) + (σ x - x ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [e]
  exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσD' _).mpr (hιI x hx)) (hσF x hx)

variable (Ω) in

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap F Ω)` using `(algebraMap F Ω).injective`. Use `haveI hV : IsLocalRing (v.valuation F).valuationSubring.toSubring := inferInstanceAs (IsLocalRing (v.valuation F).valuationSubring)`. Use `haveI hS : IsLocalRing ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) := IsLocalRing.of_surjective' ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).toRingHom ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective …`. Take `⟨B, hB⟩` from `LocalSubring.exists_le_valuationSubring (LocalSubring.mk ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) : LocalSubring Ω)`. Take `⟨hsub, hloc⟩` from `hB`.

Establish `hfx : ∀ z : F, v.valuation F z ≤ 1 → algebraMap F Ω z ∈ B` using `fun z hz => hsub (Subring.mem_map.mpr ⟨z, hz, rfl⟩)`. Establish `hle : ∀ r : 𝓞 F, v.valuation F (r : F) ≤ 1` using `fun r => v.valuation_le_one r`. Establish `hlt : ∀ r : 𝓞 F, v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal` using `fun r => v.valuation_lt_one_iff_mem r`. Use `⟨B, ?_⟩` and prove the remaining obligations. Unfold `Formalism.ConjugateSelfDual.IsPlaceOver`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hx`. Establish `hx1 : v.valuation F (x : F) = 1` using `le_antisymm (hle x) (not_lt.mp (mt (hlt x).mp hx))`.

Establish `hx0 : (x : F) ≠ 0`. Introduce `h0`. Rewrite `hx1` using `[h0, map_zero]`. Conclude with `zero_ne_one hx1`. Establish `hne : algebraMap F Ω (x : F) ≠ 0` using `(map_ne_zero _).mpr hx0`.

Establish `hinv : v.valuation F ((x : F)⁻¹) ≤ 1` using `by rw [map_inv₀, hx1, inv_one]`. Establish `hmem : algebraMap F Ω ((x : F)⁻¹) ∈ B` using `hfx _ hinv`. Rewrite `hmem` using `[map_inv₀]`. Establish `h1 : B.valuation (algebraMap F Ω (x : F))⁻¹ ≤ 1` using `(B.valuation_le_one_iff _).mpr hmem`. Establish `h2` using `(Valuation.one_lt_val_iff B.valuation (inv_ne_zero hne)).mpr (by rwa [inv_inv])`.

Conclude with `absurd h1 (not_le.mpr h2)`. Introduce `hx`. Assume the negation of the conclusion as `hnot`. Establish `hxlt` using `(hlt x).mpr hx`. Distinguish the cases in `hx0 : (x : F) = 0`.

Apply `hnot` to reduce the goal to its premises. Rewrite using `[hx0, map_zero, map_zero]`. Conclude with `zero_lt_one`. Establish `hne : algebraMap F Ω (x : F) ≠ 0` using `(map_ne_zero _).mpr hx0`. Establish `hyB : algebraMap F Ω (x : F) ∈ B` using `hfx _ (hle x)`.

Establish `hyv : B.valuation (algebraMap F Ω (x : F)) = 1` using `le_antisymm ((B.valuation_le_one_iff _).mpr hyB) (not_lt.mp hnot)`. Establish `hyinvB : (algebraMap F Ω (x : F))⁻¹ ∈ B`. Rewrite using `[← B.valuation_le_one_iff, map_inv₀, hyv, inv_one]`. Establish `hyS : algebraMap F Ω (x : F) ∈ (v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)` using `Subring.mem_map.mpr ⟨_, hle x, rfl⟩`. Establish `hunit : IsUnit (Subring.inclusion hsub ⟨_, hyS⟩)` using `isUnit_iff_exists_inv.mpr ⟨⟨_, hyinvB⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩`.

Take `⟨u, hu⟩` from `hloc.map_nonunit _ hunit`. Establish `ht` using `((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).2`. Establish `hmul : algebraMap F Ω (x : F) * ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).1 = 1`. Establish `h3` using `congrArg Subtype.val u.mul_inv`. Rewrite `h3` using `[hu]`.

Conclude with `h3`. Take `⟨z, hz, hzt⟩` from `Subring.mem_map.mp ht`. Establish `hzx : z = (x : F)⁻¹`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hzt, map_inv₀]`.

Conclude with `eq_inv_of_mul_eq_one_right hmul`. Establish `hzle : v.valuation F z ≤ 1` using `hz`. Rewrite `hzle` using `[hzx]`. Establish `h4` using `(Valuation.one_lt_val_iff (v.valuation F) (inv_ne_zero hx0)).mpr (by rwa [inv_inv])`. Conclude with `absurd hzle (not_le.mpr h4)`.
-/
theorem exists_isPlaceOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring (Ω), IsPlaceOver A v := by
  classical
  have hinj : Function.Injective (algebraMap F Ω) := (algebraMap F Ω).injective
  haveI hV : IsLocalRing (v.valuation F).valuationSubring.toSubring :=
    inferInstanceAs (IsLocalRing (v.valuation F).valuationSubring)
  haveI hS : IsLocalRing ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) :=
    IsLocalRing.of_surjective'
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).toRingHom
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).surjective
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring
    (LocalSubring.mk ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) : LocalSubring Ω)
  obtain ⟨hsub, hloc⟩ := hB
  have hfx : ∀ z : F, v.valuation F z ≤ 1 → algebraMap F Ω z ∈ B := fun z hz =>
    hsub (Subring.mem_map.mpr ⟨z, hz, rfl⟩)
  have hle : ∀ r : 𝓞 F, v.valuation F (r : F) ≤ 1 := fun r => v.valuation_le_one r
  have hlt : ∀ r : 𝓞 F, v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal := fun r =>
    v.valuation_lt_one_iff_mem r
  refine ⟨B, ?_⟩
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  intro x
  constructor
  · intro h
    by_contra hx
    have hx1 : v.valuation F (x : F) = 1 := le_antisymm (hle x) (not_lt.mp (mt (hlt x).mp hx))
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx1
      exact zero_ne_one hx1
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hinv : v.valuation F ((x : F)⁻¹) ≤ 1 := by rw [map_inv₀, hx1, inv_one]
    have hmem : algebraMap F Ω ((x : F)⁻¹) ∈ B := hfx _ hinv
    rw [map_inv₀] at hmem
    have h1 : B.valuation (algebraMap F Ω (x : F))⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hmem
    have h2 := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    exact absurd h1 (not_le.mpr h2)
  · intro hx
    by_contra hnot
    have hxlt := (hlt x).mpr hx
    by_cases hx0 : (x : F) = 0
    · apply hnot
      rw [hx0, map_zero, map_zero]
      exact zero_lt_one
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hyB : algebraMap F Ω (x : F) ∈ B := hfx _ (hle x)
    have hyv : B.valuation (algebraMap F Ω (x : F)) = 1 :=
      le_antisymm ((B.valuation_le_one_iff _).mpr hyB) (not_lt.mp hnot)
    have hyinvB : (algebraMap F Ω (x : F))⁻¹ ∈ B := by
      rw [← B.valuation_le_one_iff, map_inv₀, hyv, inv_one]
    have hyS : algebraMap F Ω (x : F) ∈ (v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω) :=
      Subring.mem_map.mpr ⟨_, hle x, rfl⟩
    have hunit : IsUnit (Subring.inclusion hsub ⟨_, hyS⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hyinvB⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
    have ht := ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
      ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).2
    have hmul : algebraMap F Ω (x : F) *
        ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
          ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).1 = 1 := by
      have h3 := congrArg Subtype.val u.mul_inv
      rw [hu] at h3
      exact h3
    obtain ⟨z, hz, hzt⟩ := Subring.mem_map.mp ht
    have hzx : z = (x : F)⁻¹ := by
      apply hinj
      rw [hzt, map_inv₀]
      exact eq_inv_of_mul_eq_one_right hmul
    have hzle : v.valuation F z ≤ 1 := hz
    rw [hzx] at hzle
    have h4 := (Valuation.one_lt_val_iff (v.valuation F) (inv_ne_zero hx0)).mpr (by rwa [inv_inv])
    exact absurd hzle (not_le.mpr h4)

variable (Ω) in
/- English proof (translation)
The claim follows from `Classical.epsilon_spec (exists_isPlaceOver Ω v)`.
-/
theorem isPlaceOver_placeOf (v : HeightOneSpectrum (𝓞 F)) : IsPlaceOver (placeOf Ω v) v := Classical.epsilon_spec (exists_isPlaceOver Ω v)

/- English proof (translation)
Conclude with `exists_smul_eq_of_over h h'`.
-/
theorem exists_smul_eq_of_isPlaceOver [IsAlgClosure F Ω] {A A' : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (h' : IsPlaceOver A' v) :
    ∃ σ : G F Ω, σ • A = A' := by
  exact exists_smul_eq_of_over h h'

/- English proof (translation)
Conclude with `exists_frob_over h`.
-/
theorem exists_isFrob [IsAlgClosure F Ω] {A : ValuationSubring (Ω)} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : ∃ σ : G F Ω, IsFrob A (normV v) σ := by
  exact exists_frob_over h

variable (Ω) in
/- English proof (translation)
The claim follows from `Classical.epsilon_spec (exists_isFrob (isPlaceOver_placeOf Ω v))`.
-/
theorem isFrob_frobOf [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    IsFrob (placeOf Ω v) (normV v) (frobOf Ω v) := Classical.epsilon_spec (exists_isFrob (isPlaceOver_placeOf Ω v))

/- English proof (translation)
Take `⟨-, hI⟩` from `mem_Ine.mp hσ`. Establish `key : ∀ n, PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n ((1 : ℕ) : ℤ_[l])` using `cycZ_toZModPow_eq hl h (fun x hx => by simpa using hI x hx)`. Establish `hz : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Simplify using `using PadicInt.ext_of_toZModPow.mp key`. Rewrite using `[cyc_eq_map_cycZ, show cycZ F Ω l σ = 1 from Units.ext hz, map_one]`.
-/
theorem cyc_eq_one_of_mem_Ine [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cyc F Ω l σ = 1 := by
  obtain ⟨-, hI⟩ := mem_Ine.mp hσ
  have key : ∀ n, PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) =
      PadicInt.toZModPow n ((1 : ℕ) : ℤ_[l]) :=
    cycZ_toZModPow_eq hl h (fun x hx => by simpa using hI x hx)
  have hz : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa using PadicInt.ext_of_toZModPow.mp key
  rw [cyc_eq_map_cycZ, show cycZ F Ω l σ = 1 from Units.ext hz, map_one]

/- English proof (translation)
Take `⟨-, hF⟩` from `hσ`. Conclude with `PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hF)`.
-/
theorem cycZ_of_isFrob [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : IsFrob A (normV v) σ) : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV v : ℤ_[l]) := by
  obtain ⟨-, hF⟩ := hσ
  exact PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hF)

/- English proof (translation)
Establish `hal : Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Establish `hfd : FiniteDimensional F (IntermediateField.adjoin F {x})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `σ hσ`.

Use `⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)), ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩` and prove the remaining obligations. Introduce `τ hτ hPτ`. Establish `h1 : (σ⁻¹ * τ) x = x` using `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)`. Establish `h2 : τ x = σ x`. Establish `h3` using `congrArg σ h1`.

Rewrite `h3` using `[AlgEquiv.mul_apply, mul_inv_apply]`. Then use the resulting hypothesis. Conclude with `hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)`. Use `show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`.
-/
private theorem isClosed_setOf_apply_lemma [IsAlgClosure F Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {τ : G F Ω | P (τ x)} := by
  have hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)),
    ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro τ hτ hPτ
    have h1 : (σ⁻¹ * τ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, mul_inv_apply] at h3
    exact hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)
  · show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

/- English proof (translation)
Establish `e : (Dec (F` using `F) A : Set (G F Ω)) = ⋂ x : Ω, {τ : G F Ω | τ x ∈ A ↔ x ∈ A} := by`. Use extensionality with `τ`. Simplify using `only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]`. Use `⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Establish `k : τ • ((τ⁻¹ : G F Ω) y) ∈ τ • A ↔ (τ⁻¹ : G F Ω) y ∈ A` using `ValuationSubring.smul_mem_pointwise_smul_iff`. Rewrite `k` using `[AlgEquiv.smul_def, mul_inv_apply]`. Rewrite using `[k, ← h ((τ⁻¹ : G F Ω) y), mul_inv_apply]`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => y ∈ A ↔ x ∈ A)`.
-/
theorem isClosed_Dec [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Dec (F := F) A : Set (G F Ω)) := by
  have e : (Dec (F := F) A : Set (G F Ω)) = ⋂ x : Ω, {τ : G F Ω | τ x ∈ A ↔ x ∈ A} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
    ext y
    have k : τ • ((τ⁻¹ : G F Ω) y) ∈ τ • A ↔ (τ⁻¹ : G F Ω) y ∈ A :=
      ValuationSubring.smul_mem_pointwise_smul_iff
    rw [AlgEquiv.smul_def, mul_inv_apply] at k
    rw [k, ← h ((τ⁻¹ : G F Ω) y), mul_inv_apply]
  rw [e]
  exact isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => y ∈ A ↔ x ∈ A)

/- English proof (translation)
Establish `e : (Ine (F` using `F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩ ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by`. Use extensionality with `τ`. Simplify using `only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `Iff.rfl`. Rewrite using `[e]`.

Conclude with `(isClosed_Dec A).inter (isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))`.
-/
theorem isClosed_Ine [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by
  have e : (Ine (F := F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩
      ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Dec A).inter (isClosed_iInter fun x =>
    isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

end Basic₃

end ReciprocityTheory.Gal
