import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittDiag
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.FinNormSurj
import Formalism.SatakeDualWeyl.StatementF

noncomputable section

open Matrix

namespace Formalism.IndefR.LocBrg

def IntWittLoc : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L),
      (∀ i j, H i j ∈ Formalism.UG.intL L) → Valued.v H.det = 1 → Formalism.UG.cT σ H = H →
      ∃ R ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L),
        Formalism.UG.cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
          Formalism.UG.antiJ L n

section Glue

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev VA (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

/- English proof (translation)
The claim follows from `Valuation.mem_valuationSubring_iff _ _`.
-/
theorem mem_VA {x : L} : x ∈ VA L ↔ Valued.v x ≤ 1 := Valuation.mem_valuationSubring_iff _ _

/- English proof (translation)
The claim follows from `Valuation.mem_integer_iff _ _`.
-/
theorem mem_intL {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Valuation.mem_integer_iff _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Establish `hmul : ((u : VA L) : L) * (((u⁻¹ : (VA L)ˣ) : VA L) : L) = 1`. Conclude with `congrArg (fun x : VA L => (x : L)) u.mul_inv`. Establish `hu : Valued.v ((u : VA L) : L) ≤ 1` using `mem_VA.1 (u : VA L).2`.

Establish `hu' : Valued.v (((u⁻¹ : (VA L)ˣ) : VA L) : L) ≤ 1` using `mem_VA.1 (u⁻¹ : (VA L)ˣ).1.2`. Establish `hprod` using `congrArg Valued.v hmul`. Rewrite `hprod` using `[map_mul, map_one]`. Use `le_antisymm hu ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `h`. Establish `ha0 : (a : L) ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, map_zero]`. Conclude with `zero_ne_one h`.

Establish `hinv : (a : L)⁻¹ ∈ VA L`. Rewrite using `[mem_VA, map_inv₀, h, inv_one]`. Use `IsUnit.of_mul_eq_one (⟨(a : L)⁻¹, hinv⟩ : VA L) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `mul_inv_cancel₀ ha0`.
-/
theorem isUnit_VA_iff (a : VA L) : IsUnit a ↔ Valued.v (a : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : ((u : VA L) : L) * (((u⁻¹ : (VA L)ˣ) : VA L) : L) = 1 := by
      exact congrArg (fun x : VA L => (x : L)) u.mul_inv
    have hu : Valued.v ((u : VA L) : L) ≤ 1 := mem_VA.1 (u : VA L).2
    have hu' : Valued.v (((u⁻¹ : (VA L)ˣ) : VA L) : L) ≤ 1 := mem_VA.1 (u⁻¹ : (VA L)ˣ).1.2
    have hprod := congrArg Valued.v hmul
    rw [map_mul, map_one] at hprod
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((u : VA L) : L) *
          Valued.v (((u⁻¹ : (VA L)ˣ) : VA L) : L) := hprod.symm
      _ ≤ Valued.v ((u : VA L) : L) := mul_le_of_le_one_right' hu'
  · intro h
    have ha0 : (a : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    have hinv : (a : L)⁻¹ ∈ VA L := by
      rw [mem_VA, map_inv₀, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(a : L)⁻¹, hinv⟩ : VA L) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_VA_iff]`. Conclude with `⟨fun h => lt_of_le_of_ne (mem_VA.1 a.2) h, fun h => ne_of_lt h⟩`.
-/
theorem mem_max_VA_iff (a : VA L) : a ∈ IsLocalRing.maximalIdeal (VA L) ↔ Valued.v (a : L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_VA_iff]
  exact ⟨fun h => lt_of_le_of_ne (mem_VA.1 a.2) h, fun h => ne_of_lt h⟩

variable (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x)

def sigA : VA L →+* VA L :=
  (σ.comp (VA L).subtype).codRestrict (VA L) (fun x => by
    show σ (x : L) ∈ VA L
    rw [mem_VA, hv]; exact mem_VA.1 x.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigA_coe (x : VA L) : ((sigA σ hv x : VA L) : L) = σ x := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hσ x`.
-/
theorem sigA_inv (hσ : ∀ x, σ (σ x) = x) (x : VA L) : sigA σ hv (sigA σ hv x) = x := by
  apply Subtype.ext
  exact hσ x

instance sigA_local : IsLocalHom (sigA σ hv) where
  map_nonunit a ha := by
    rw [isUnit_VA_iff, sigA_coe, hv] at ha
    exact (isUnit_VA_iff a).2 ha

end Glue

section Norm

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Take `⟨-, -, -, -, -, hq2, hcard⟩` from `hU`. Establish `hle : Valued.v (2 : L) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `h2`. Establish `hlt` using `lt_of_le_of_ne hle h2`.

Establish `hmem : (2 : VA L) ∈ IsLocalRing.maximalIdeal (VA L)`. Rewrite using `[mem_max_VA_iff]`. Use `first`. Consider the case `simpa using hlt`. Consider the case `exact_mod_cast hlt`.

Use `haveI : Finite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Use `letI := Fintype.ofFinite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)`. Establish `h2Q : (2 : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = 0`. Establish `h` using `Ideal.Quotient.eq_zero_iff_mem.2 hmem`. Rewrite `h` using `[map_ofNat]`.

Conclude with `h`. Establish `hc0` using `Nat.cast_card_eq_zero ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)`. Rewrite `hc0` using `[← Nat.card_eq_fintype_card, hcard]`. Take `⟨m, hm⟩ : Odd (q ^ 2)` from `hq.pow`. Rewrite `hc0` using `[hm]`.

Move the coercions through the operations in `at hc0`. Rewrite `hc0` using `[h2Q, zero_mul, zero_add]`. Establish `hsub` using `subsingleton_of_zero_eq_one hc0.symm`. Use `haveI : Unique ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩`. Establish `hc1` using `Nat.card_unique (α := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)`.

Rewrite `hc1` using `[hcard]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem valuation_two_eq_one_of_unramInv_odd {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, hq2, hcard⟩ := hU
  have hle : Valued.v (2 : L) ≤ 1 := by
    calc Valued.v (2 : L) = Valued.v ((1 : L) + 1) := by norm_num
      _ ≤ max (Valued.v (1 : L)) (Valued.v (1 : L)) := Valuation.map_add _ _ _
      _ = 1 := by simp
  by_contra h2
  have hlt := lt_of_le_of_ne hle h2
  have hmem : (2 : VA L) ∈ IsLocalRing.maximalIdeal (VA L) := by
    rw [mem_max_VA_iff]
    first
      | simpa using hlt
      | exact_mod_cast hlt
  haveI : Finite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  have h2Q : (2 : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_ofNat] at h
    exact h
  have hc0 := Nat.cast_card_eq_zero ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  rw [← Nat.card_eq_fintype_card, hcard] at hc0
  obtain ⟨m, hm⟩ : Odd (q ^ 2) := hq.pow
  rw [hm] at hc0
  push_cast at hc0
  rw [h2Q, zero_mul, zero_add] at hc0
  have hsub := subsingleton_of_zero_eq_one hc0.symm
  haveI : Unique ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have hc1 := Nat.card_unique (α := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  rw [hcard] at hc1
  nlinarith

/- English proof (translation)
Rewrite using `[isUnit_VA_iff]`. Use `first`. Consider the case `simpa using valuation_two_eq_one_of_unramInv_odd hU hq`. Consider the case `exact_mod_cast valuation_two_eq_one_of_unramInv_odd hU hq`.
-/
theorem two_unit_VA {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    IsUnit (2 : VA L) := by
  rw [isUnit_VA_iff]
  first
    | simpa using valuation_two_eq_one_of_unramInv_odd hU hq
    | exact_mod_cast valuation_two_eq_one_of_unramInv_odd hU hq

/- English proof (translation)
Conclude with `valuation_two_eq_one_of_unramInv_odd hU hq`.
-/
theorem two_val {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    Valued.v (2 : L) = 1 := by
  exact valuation_two_eq_one_of_unramInv_odd hU hq

/- English proof (translation)
Take `⟨hσσ, hv, -, -, ⟨x₀, hx₀, hx₀v⟩, hq2, hcard⟩` from `id hU`. Use `haveI : Finite (IsLocalRing.ResidueField (VA L)) := Nat.finite_of_card_ne_zero (by rw [show Nat.card (IsLocalRing.ResidueField (VA L)) = q ^ 2 from hcard]; positivity)`. Use `letI : Fintype (IsLocalRing.ResidueField (VA L)) := Fintype.ofFinite _`. Establish `hτres : ∀ a : VA L, IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) a) = IsLocalRing.residue (VA L) (sigA σ hU.2.1 a)` using `fun a => IsLocalRing.ResidueField.map_residue _ a`. Establish `hττ : ∀ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.ResidueField.map (sigA σ hU.2.1) y) = y`.

Introduce `y`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective y`. Rewrite using `[hτres, hτres, sigA_inv σ _ hσσ]`. Establish `hne : ∃ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1) y ≠ y`. Use `⟨IsLocalRing.residue (VA L) ⟨x₀, mem_VA.2 (mem_intL.1 hx₀)⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hτres]`. Introduce `h`. Rewrite `h` using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_VA_iff]`. Establish `h' : Valued.v (σ x₀ - x₀) < 1` using `h`. Rewrite `h'` using `[hx₀v]`.

Conclude with `lt_irrefl _ h'`. Establish `hcfix : IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) c) = IsLocalRing.residue (VA L) c`. Rewrite using `[hτres, hcσ]`. Establish `hc0 : IsLocalRing.residue (VA L) c ≠ 0`. Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff]`.

Conclude with `fun h => (IsLocalRing.mem_maximalIdeal _).1 h hc`. Take `⟨ybar, hy⟩` from `hF _ _ hττ hne _ hcfix hc0`. Take `⟨y, rfl⟩` from `IsLocalRing.residue_surjective ybar`. Rewrite `hy` using `[hτres, ← map_mul]`. Establish `hdiff : sigA σ hU.2.1 y * y - c ∈ IsLocalRing.maximalIdeal (VA L)`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, hy, sub_self]`. Rewrite `hdiff` using `[mem_max_VA_iff]`. Establish `hcv : Valued.v (c : L) = 1` using `(isUnit_VA_iff c).1 hc`. Establish `hdiff' : Valued.v (σ (y : L) * (y : L) - c) < 1` using `hdiff`. Establish `hav : Valued.v (σ (y : L) * (y : L)) = 1`.

Establish `h1 : Valued.v ((c : L) + (σ (y : L) * (y : L) - c)) = Valued.v (c : L)` using `Valuation.map_add_eq_of_lt_left _ (by rw [hcv]; exact hdiff')`. Rewrite `h1` using `[add_sub_cancel, hcv]`. Then use the resulting hypothesis. Establish `ha0 : σ (y : L) * (y : L) ≠ 0` using `fun h => by`. Rewrite `hav` using `[h, map_zero]`. Conclude with `zero_ne_one hav`.

Establish `hu1 : Valued.v ((c : L) * (σ (y : L) * (y : L))⁻¹ - 1) < 1`. Establish `h1 : (c : L) * (σ (y : L) * (y : L))⁻¹ - 1 = -(σ (y : L) * (y : L) - c) * (σ (y : L) * (y : L))⁻¹`. Rewrite using `[neg_sub, sub_mul, mul_inv_cancel₀ ha0]`. Rewrite using `[h1, map_mul, map_inv₀, hav, inv_one, mul_one, Valuation.map_neg]`. Conclude with `hdiff'`.

Establish `h2v : Valued.v (2 : L) = 1` using `two_val hU hq`. Take `⟨s, hss, hs1⟩` from `hS L h2v _ hu1`. Establish `hσc : σ (c : L) = c` using `congrArg Subtype.val hcσ`. Establish `hσu : σ ((c : L) * (σ (y : L) * (y : L))⁻¹) = (c : L) * (σ (y : L) * (y : L))⁻¹`. Rewrite using `[map_mul, map_inv₀, map_mul, hσσ, hσc, mul_comm (y : L)]`.

Establish `hvs : Valued.v s = 1`. Establish `h1 : Valued.v ((1 : L) + (s - 1)) = Valued.v (1 : L)` using `Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hs1)`. Rewrite `h1` using `[add_sub_cancel, map_one]`. Then use the resulting hypothesis. Establish `hσs : σ s = s`. Establish `hsq : (σ s - s) * (σ s + s) = 0`.

Establish `h1 : σ s * σ s = s * s` using `by rw [← map_mul, hss, hσu]`. Take the linear combination `h1`. Establish `hσs1 : Valued.v (σ s - 1) < 1`. Rewrite using `[← map_one σ, ← map_sub, hv]`. Conclude with `hs1`.

Establish `hsmall : Valued.v ((σ s - 1) + (s - 1)) < 1` using `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hσs1 hs1)`. Establish `hsum : Valued.v (σ s + s) = 1`. Establish `h1 : Valued.v ((2 : L) + ((σ s - 1) + (s - 1))) = Valued.v (2 : L)` using `Valuation.map_add_eq_of_lt_left _ (by rw [h2v]; exact hsmall)`. Rewrite `h1` using `[h2v]`. Rewrite using `[← h1]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hne0 : σ s + s ≠ 0` using `fun h => by`. Rewrite `hsum` using `[h, map_zero]`. Conclude with `zero_ne_one hsum`.

Break down `mul_eq_zero.1 hsq with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hne0`. Use `⟨⟨(y : L) * s, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_VA, map_mul, hvs, mul_one]`.

Conclude with `mem_VA.1 y.2`. Apply `Subtype.ext show σ ((y : L) * s) * ((y : L) * s) = (c : L)` to reduce the goal to its premises. Rewrite using `[map_mul, hσs]`. Establish `hcu : (c : L) = (c : L) * (σ (y : L) * (y : L))⁻¹ * (σ (y : L) * (y : L))`. Rewrite using `[mul_assoc, inv_mul_cancel₀ ha0, mul_one]`.

Rewrite using `[hcu, ← hss]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSurj [CompleteSpace L] (hF : FinNormSurj) (hS : HenselSqrt) {ϖ : L} {σ : L →+* L} {q : ℕ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (c : VA L) (hcσ : sigA σ hU.2.1 c = c) (hc : IsUnit c) :
    ∃ t : VA L, sigA σ hU.2.1 t * t = c := by
  obtain ⟨hσσ, hv, -, -, ⟨x₀, hx₀, hx₀v⟩, hq2, hcard⟩ := id hU
  haveI : Finite (IsLocalRing.ResidueField (VA L)) :=
    Nat.finite_of_card_ne_zero (by rw [show Nat.card (IsLocalRing.ResidueField (VA L)) = q ^ 2 from hcard]; positivity)
  letI : Fintype (IsLocalRing.ResidueField (VA L)) := Fintype.ofFinite _
  have hτres : ∀ a : VA L, IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) a) =
      IsLocalRing.residue (VA L) (sigA σ hU.2.1 a) := fun a => IsLocalRing.ResidueField.map_residue _ a
  have hττ : ∀ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1)
      (IsLocalRing.ResidueField.map (sigA σ hU.2.1) y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [hτres, hτres, sigA_inv σ _ hσσ]
  have hne : ∃ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1) y ≠ y := by
    refine ⟨IsLocalRing.residue (VA L) ⟨x₀, mem_VA.2 (mem_intL.1 hx₀)⟩, ?_⟩
    rw [hτres]
    intro h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_VA_iff] at h
    have h' : Valued.v (σ x₀ - x₀) < 1 := h
    rw [hx₀v] at h'
    exact lt_irrefl _ h'
  have hcfix : IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) c) =
      IsLocalRing.residue (VA L) c := by
    rw [hτres, hcσ]
  have hc0 : IsLocalRing.residue (VA L) c ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hc
  obtain ⟨ybar, hy⟩ := hF _ _ hττ hne _ hcfix hc0
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ybar
  rw [hτres, ← map_mul] at hy
  have hdiff : sigA σ hU.2.1 y * y - c ∈ IsLocalRing.maximalIdeal (VA L) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hy, sub_self]
  rw [mem_max_VA_iff] at hdiff
  have hcv : Valued.v (c : L) = 1 := (isUnit_VA_iff c).1 hc
  have hdiff' : Valued.v (σ (y : L) * (y : L) - c) < 1 := hdiff
  have hav : Valued.v (σ (y : L) * (y : L)) = 1 := by
    have h1 : Valued.v ((c : L) + (σ (y : L) * (y : L) - c)) = Valued.v (c : L) :=
      Valuation.map_add_eq_of_lt_left _ (by rw [hcv]; exact hdiff')
    rwa [add_sub_cancel, hcv] at h1
  have ha0 : σ (y : L) * (y : L) ≠ 0 := fun h => by
    rw [h, map_zero] at hav
    exact zero_ne_one hav
  have hu1 : Valued.v ((c : L) * (σ (y : L) * (y : L))⁻¹ - 1) < 1 := by
    have h1 : (c : L) * (σ (y : L) * (y : L))⁻¹ - 1 =
        -(σ (y : L) * (y : L) - c) * (σ (y : L) * (y : L))⁻¹ := by
      rw [neg_sub, sub_mul, mul_inv_cancel₀ ha0]
    rw [h1, map_mul, map_inv₀, hav, inv_one, mul_one, Valuation.map_neg]
    exact hdiff'
  have h2v : Valued.v (2 : L) = 1 := two_val hU hq
  obtain ⟨s, hss, hs1⟩ := hS L h2v _ hu1
  have hσc : σ (c : L) = c := congrArg Subtype.val hcσ
  have hσu : σ ((c : L) * (σ (y : L) * (y : L))⁻¹) = (c : L) * (σ (y : L) * (y : L))⁻¹ := by
    rw [map_mul, map_inv₀, map_mul, hσσ, hσc, mul_comm (y : L)]
  have hvs : Valued.v s = 1 := by
    have h1 : Valued.v ((1 : L) + (s - 1)) = Valued.v (1 : L) :=
      Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hs1)
    rwa [add_sub_cancel, map_one] at h1
  have hσs : σ s = s := by
    have hsq : (σ s - s) * (σ s + s) = 0 := by
      have h1 : σ s * σ s = s * s := by rw [← map_mul, hss, hσu]
      linear_combination h1
    have hσs1 : Valued.v (σ s - 1) < 1 := by
      rw [← map_one σ, ← map_sub, hv]
      exact hs1
    have hsmall : Valued.v ((σ s - 1) + (s - 1)) < 1 :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hσs1 hs1)
    have hsum : Valued.v (σ s + s) = 1 := by
      have h1 : Valued.v ((2 : L) + ((σ s - 1) + (s - 1))) = Valued.v (2 : L) :=
        Valuation.map_add_eq_of_lt_left _ (by rw [h2v]; exact hsmall)
      rw [h2v] at h1
      rw [← h1]
      congr 1
      ring
    have hne0 : σ s + s ≠ 0 := fun h => by
      rw [h, map_zero] at hsum
      exact zero_ne_one hsum
    rcases mul_eq_zero.1 hsq with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne0
  refine ⟨⟨(y : L) * s, ?_⟩, ?_⟩
  · rw [mem_VA, map_mul, hvs, mul_one]
    exact mem_VA.1 y.2
  · apply Subtype.ext
    show σ ((y : L) * s) * ((y : L) * s) = (c : L)
    rw [map_mul, hσs]
    have hcu : (c : L) = (c : L) * (σ (y : L) * (y : L))⁻¹ * (σ (y : L) * (y : L)) := by
      rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [hcu, ← hss]
    ring

end Norm

section Final

end Final

end Formalism.IndefR.LocBrg
