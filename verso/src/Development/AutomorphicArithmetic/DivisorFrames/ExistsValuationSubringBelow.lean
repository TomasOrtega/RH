import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsValuationSubringExtensionP
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]`. Introduce `hu`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `h1 : y * (u : L) = 1` using `congrArg Subtype.val hu`. Apply `hy'` to reduce the goal to its premises.

Rewrite using `[← eq_inv_of_mul_eq_one_right h1]`. Conclude with `u.2`.
-/
private theorem UpperTheory.residue_eq_zero_of_inv_not_mem {L : Type} [Field L] (R : ValuationSubring L) (y : L)
    (hy : y ∈ R) (hy' : y⁻¹ ∉ R) : IsLocalRing.residue R ⟨y, hy⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : y * (u : L) = 1 := congrArg Subtype.val hu
  apply hy'
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact u.2

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← map_mul, ← map_one (IsLocalRing.residue R)]`. Use `congr 1`. Conclude with `Subtype.ext (mul_inv_cancel₀ h0)`.
-/
private theorem UpperTheory.residue_inv {L : Type} [Field L] (R : ValuationSubring L) (y : L)
    (hy : y ∈ R) (hy' : y⁻¹ ∈ R) (h0 : y ≠ 0) :
    IsLocalRing.residue R ⟨y⁻¹, hy'⟩ = (IsLocalRing.residue R ⟨y, hy⟩)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul, ← map_one (IsLocalRing.residue R)]
  congr 1
  exact Subtype.ext (mul_inv_cancel₀ h0)

/- English proof (translation)
Establish `key : ∀ x : L, x ∈ (A₀.toSubring.comap (IsLocalRing.residue R)).map R.subtype ↔ ∃ h : x ∈ R, IsLocalRing.residue R ⟨x, h⟩ ∈ A₀`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`.

Introduce and unpack `⟨h, hx⟩`. Conclude with `⟨⟨x, h⟩, hx, rfl⟩`. Use `⟨ValuationSubring.ofSubring ((A₀.toSubring.comap (IsLocalRing.residue R)).map R.subtype) ?_, key⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[key, key]`.

Distinguish the cases in `hx : x ∈ R`. Distinguish the cases in `hx' : x⁻¹ ∈ R`. Distinguish the cases in `h0 : x = 0`. Use `left`. Use `⟨hx, ?_⟩` and prove the remaining obligations.

Establish `: (⟨x, hx⟩ : R) = 0` using `Subtype.ext h0`. Rewrite using `[this, map_zero]`. Conclude with `A₀.zero_mem`. Break down `A₀.mem_or_inv_mem (IsLocalRing.residue R ⟨x, hx⟩) with h | h` into its components or cases. Conclude with `Or.inl ⟨hx, h⟩`.

Use `right`. Use `⟨hx', ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.residue_inv R x hx hx' h0]`. Conclude with `h`. Use `left`.

Use `⟨hx, ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.residue_eq_zero_of_inv_not_mem R x hx hx']`. Conclude with `A₀.zero_mem`. Use `right`. Establish `hx' : x⁻¹ ∈ R` using `(R.mem_or_inv_mem x).resolve_left hx`.

Use `⟨hx', ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.residue_eq_zero_of_inv_not_mem R x⁻¹ hx' (by rwa [inv_inv])]`. Conclude with `A₀.zero_mem`.
-/
private theorem UpperTheory.exists_composite_valuationSubring {L : Type} [Field L] (R : ValuationSubring L)
    (A₀ : ValuationSubring (IsLocalRing.ResidueField R)) :
    ∃ A : ValuationSubring L, ∀ x : L,
      x ∈ A ↔ ∃ h : x ∈ R, IsLocalRing.residue R ⟨x, h⟩ ∈ A₀ := by
  have key : ∀ x : L, x ∈ (A₀.toSubring.comap (IsLocalRing.residue R)).map R.subtype ↔
      ∃ h : x ∈ R, IsLocalRing.residue R ⟨x, h⟩ ∈ A₀ := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨ValuationSubring.ofSubring
    ((A₀.toSubring.comap (IsLocalRing.residue R)).map R.subtype) ?_, key⟩
  intro x
  rw [key, key]
  by_cases hx : x ∈ R
  · by_cases hx' : x⁻¹ ∈ R
    · by_cases h0 : x = 0
      · left
        refine ⟨hx, ?_⟩
        have : (⟨x, hx⟩ : R) = 0 := Subtype.ext h0
        rw [this, map_zero]
        exact A₀.zero_mem
      · rcases A₀.mem_or_inv_mem (IsLocalRing.residue R ⟨x, hx⟩) with h | h
        · exact Or.inl ⟨hx, h⟩
        · right
          refine ⟨hx', ?_⟩
          rw [UpperTheory.residue_inv R x hx hx' h0]
          exact h
    · left
      refine ⟨hx, ?_⟩
      rw [UpperTheory.residue_eq_zero_of_inv_not_mem R x hx hx']
      exact A₀.zero_mem
  · right
    have hx' : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hx
    refine ⟨hx', ?_⟩
    rw [UpperTheory.residue_eq_zero_of_inv_not_mem R x⁻¹ hx' (by rwa [inv_inv])]
    exact A₀.zero_mem

/- English proof (translation)
Introduce `p K L _ _ _ _ R φ V hp hV`. Use `haveI : Countable R := Subtype.countable`. Use `haveI : Countable (IsLocalRing.ResidueField R) := (IsLocalRing.residue_surjective (R := R)).countable`. Take `⟨A₀, h1, h2, h3⟩` from `UpperTheory.exists_valuationSubring_extension_p p K (IsLocalRing.ResidueField R) ((IsLocalRing.residue R).comp φ) V hp hV`. Take `⟨A, hA⟩` from `UpperTheory.exists_composite_valuationSubring R A₀`.

Establish `hpR : (p : L) ∈ R` using `natCast_mem R p`. Establish `hpe : (⟨(p : L), hpR⟩ : R) = (p : R)` using `Subtype.ext (by simp)`. Use `⟨A, fun x hx => ((hA x).1 hx).1, fun v hv => (hA _).2 ⟨(φ v).2, h1 v hv⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h2`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`. Distinguish the cases in `h0 : (p : L) = 0`.

Conclude with `Or.inl h0`. Use `right`. Introduce `hi`. Take `⟨hR, hi⟩` from `(hA _).1 hi`. Rewrite `hi` using `[UpperTheory.residue_inv R p hpR hR h0, hpe, map_natCast]`.

Break down `h2 with h2 | h2` into its components or cases. Establish `hK : (p : K) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Apply `hK` to reduce the goal to its premises. Apply `((IsLocalRing.residue R).comp φ).injective` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero, h2]`.

Conclude with `h2 hi`. Introduce `x hx`. Take `⟨m, hm⟩` from `h3 (IsLocalRing.residue R ⟨x, hx⟩)`. Use `⟨m, (hA _).2 ⟨mul_mem (pow_mem hpR m) hx, ?_⟩⟩` and prove the remaining obligations. Establish `: (⟨(p : L) ^ m * x, mul_mem (pow_mem hpR m) hx⟩ : R) = (p : R) ^ m * ⟨x, hx⟩` using `Subtype.ext (by simp)`.

Rewrite using `[this, map_mul, map_pow, map_natCast]`. Conclude with `hm`.
-/
theorem UpperTheory.exists_valuationSubring_below :
    ∀ (p : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [Countable L] (R : ValuationSubring L) (φ : K →+* R) (V : ValuationSubring K), p.Prime → (p : K) ∈ V.nonunits → ∃ A : ValuationSubring L, A ≤ R ∧ (∀ v ∈ V, (φ v : L) ∈ A) ∧ (p : L) ∈ A.nonunits ∧ ∀ x ∈ R, ∃ m : ℕ, (p : L) ^ m * x ∈ A := by
  intro p K L _ _ _ _ R φ V hp hV
  haveI : Countable R := Subtype.countable
  haveI : Countable (IsLocalRing.ResidueField R) :=
    (IsLocalRing.residue_surjective (R := R)).countable
  obtain ⟨A₀, h1, h2, h3⟩ := UpperTheory.exists_valuationSubring_extension_p p K (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp φ) V hp hV
  obtain ⟨A, hA⟩ := UpperTheory.exists_composite_valuationSubring R A₀
  have hpR : (p : L) ∈ R := natCast_mem R p
  have hpe : (⟨(p : L), hpR⟩ : R) = (p : R) := Subtype.ext (by simp)
  refine ⟨A, fun x hx => ((hA x).1 hx).1, fun v hv => (hA _).2 ⟨(φ v).2, h1 v hv⟩, ?_, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff_or] at h2 ⊢
    by_cases h0 : (p : L) = 0
    · exact Or.inl h0
    right
    intro hi
    obtain ⟨hR, hi⟩ := (hA _).1 hi
    rw [UpperTheory.residue_inv R p hpR hR h0, hpe, map_natCast] at hi
    rcases h2 with h2 | h2
    · have hK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
      apply hK
      apply ((IsLocalRing.residue R).comp φ).injective
      rw [map_natCast, map_zero, h2]
    · exact h2 hi
  · intro x hx
    obtain ⟨m, hm⟩ := h3 (IsLocalRing.residue R ⟨x, hx⟩)
    refine ⟨m, (hA _).2 ⟨mul_mem (pow_mem hpR m) hx, ?_⟩⟩
    have : (⟨(p : L) ^ m * x, mul_mem (pow_mem hpR m) hx⟩ : R) = (p : R) ^ m * ⟨x, hx⟩ :=
      Subtype.ext (by simp)
    rw [this, map_mul, map_pow, map_natCast]
    exact hm
