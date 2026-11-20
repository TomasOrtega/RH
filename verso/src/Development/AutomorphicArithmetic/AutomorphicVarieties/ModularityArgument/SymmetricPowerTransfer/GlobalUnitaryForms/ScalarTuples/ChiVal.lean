import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.CharacterValues

/- English proof (translation)
Unfold `hs`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, h⟩`.

Use `⟨a / s, b / s, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Introduce and unpack `⟨a, b, h⟩`. Conclude with `⟨a * s, b * s, by rw [← h]; ring⟩`.
-/
private theorem hs_mul_sq {K : Type} [Field K] (D x s : K) (h0 : s ≠ 0) : hs D (x * s ^ 2) = hs D x := by
  unfold hs
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a / s, b / s, ?_⟩
    field_simp
    linear_combination h
  · rintro ⟨a, b, h⟩
    exact ⟨a * s, b * s, by rw [← h]; ring⟩

/- English proof (translation)
Unfold `hs`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem hs_sq {K : Type} [Field K] (D x : K) : hs D x ^ 2 = 1 := by
  unfold hs
  split_ifs <;> norm_num

/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Establish `hr : r ≠ 0` using `fun e => h0 (by rw [e, mul_zero])`. Use `if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hs_of_sq {K : Type} [Field K] [CharZero K] (D x : K) (h0 : D ≠ 0) (h : IsSquare D) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

/- English proof (translation)
Establish `e : Ideal.span {(u : O) * p ^ n} = IsLocalRing.maximalIdeal O ^ n`. Rewrite using `[Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, hp.maximalIdeal_eq]`. Rewrite using `[e]`. Conclude with `cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal O) (IsDiscreteValuationRing.not_a_field O)`.
-/
private theorem card_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : O} (hp : Irreducible p)
    (u : Oˣ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {(u : O) * p ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have e : Ideal.span {(u : O) * p ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, hp.maximalIdeal_eq]
  rw [e]
  exact cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal O) (IsDiscreteValuationRing.not_a_field O)

/- English proof (translation)
Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `h0 : x₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `x.ne_zero (by rw [← hx, map_zero])`. Establish `hp0 : algebraMap O K p ≠ 0` using `fun e => hp.ne_zero (inj (e.trans (map_zero _).symm))`.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hp`. Rewrite using `[card_pow hp]`. Establish `hup : Irreducible ((u : O) * p)` using `(irreducible_units_mul u).2 hp`. Use `set U : Kˣ := Units.map (algebraMap O K : O →* K) u with hU`. Use `set P : Kˣ := Units.mk0 _ hp0 with hP`.

Establish `hxe : x = U * P ^ n`. Use `ext`. Rewrite using `[← hx]`. Simplify using `[hU, hP]`. Establish `c1 : (χ P : ℂ) = hs Δ (P : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ)` using `hχ.2 p P hp rfl`.

Establish `c2 : (χ (U * P) : ℂ) = hs Δ ((U * P : Kˣ) : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ)` using `hχ.2 (u * p) (U * P) hup (by simp [hU, hP])`. Establish `c3 : χ U = 1` using `hχ.1 u`. Establish `c4 : hs Δ (U : K) = 1` using `hu u`. Establish `c5 : ∀ k : ℕ, (χ (P ^ (2 * k)) : ℂ) = 1 / (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * k)` using `fun k => by`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, c1, div_pow, pow_mul (hs _ _), hs_sq, one_pow]`.

Take `⟨k, rfl | rfl⟩` from `Nat.even_or_odd' n`. Establish `e : ((U * P ^ (2 * k) : Kˣ) : K) = U * ((P : K) ^ k) ^ 2`. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), c4, map_mul, c3, one_mul, c5, Nat.cast_pow]`.

Establish `e : ((U * P ^ (2 * k + 1) : Kˣ) : K) = ((U * P : Kˣ) : K) * ((P : K) ^ k) ^ 2`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree. Establish `e' : U * P ^ (2 * k + 1) = U * P * P ^ (2 * k)` using `by rw [pow_succ', mul_assoc]`. Rewrite using `[hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), e', map_mul, Units.val_mul, c2, c5, Nat.cast_pow, div_mul_div_comm, mul_one, pow_succ']`.
-/
private theorem main {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (inj : Function.Injective (algebraMap O K)) (Δ : K) (χ : Kˣ →* ℂˣ) (hχ : IsChi O Δ χ)
    (hu : ∀ u : Oˣ, hs Δ (algebraMap O K u) = 1) (x : Kˣ) (x₀ : O) (hx : algebraMap O K x₀ = x) :
    (χ x : ℂ) = hs Δ (x : K) / (Nat.card (O ⧸ Ideal.span {x₀}) : ℂ) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hx, map_zero])
  have hp0 : algebraMap O K p ≠ 0 := fun e => hp.ne_zero (inj (e.trans (map_zero _).symm))
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hp
  rw [card_pow hp]
  have hup : Irreducible ((u : O) * p) := (irreducible_units_mul u).2 hp
  set U : Kˣ := Units.map (algebraMap O K : O →* K) u with hU
  set P : Kˣ := Units.mk0 _ hp0 with hP
  have hxe : x = U * P ^ n := by
    ext
    rw [← hx]
    simp [hU, hP]
  have c1 : (χ P : ℂ) = hs Δ (P : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ) := hχ.2 p P hp rfl
  have c2 : (χ (U * P) : ℂ) = hs Δ ((U * P : Kˣ) : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ) :=
    hχ.2 (u * p) (U * P) hup (by simp [hU, hP])
  have c3 : χ U = 1 := hχ.1 u
  have c4 : hs Δ (U : K) = 1 := hu u
  have c5 : ∀ k : ℕ, (χ (P ^ (2 * k)) : ℂ) = 1 / (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * k) := fun k => by
    rw [map_pow, Units.val_pow_eq_pow_val, c1, div_pow, pow_mul (hs _ _), hs_sq, one_pow]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : ((U * P ^ (2 * k) : Kˣ) : K) = U * ((P : K) ^ k) ^ 2 := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val]; ring
    rw [hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), c4, map_mul, c3, one_mul, c5, Nat.cast_pow]
  · have e : ((U * P ^ (2 * k + 1) : Kˣ) : K) = ((U * P : Kˣ) : K) * ((P : K) ^ k) ^ 2 := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]; ring
    have e' : U * P ^ (2 * k + 1) = U * P * P ^ (2 * k) := by rw [pow_succ', mul_assoc]
    rw [hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), e', map_mul, Units.val_mul, c2, c5, Nat.cast_pow,
      div_mul_div_comm, mul_one, pow_succ']

end UpperTheory.V.Z.Sym.Glob.CharacterValues

open UpperTheory.V.Z.Sym.Glob.CharacterValues in
/- English proof (translation)
Introduce `F _ _ Δ D hD v x x₀ hx`. Use `main (fun a b h => Subtype.ext h) _ _ (hD.chi v) (fun u => ?_) x x₀ hx` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ D.Sg`. Use `haveI := hD.real haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective`. Establish `hΔ : Δ ≠ 0`.

Take `⟨w⟩ : Nonempty (NumberField.InfinitePlace F)` from `inferInstance`. Use `hD.neg (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w))` as an intermediate fact. Introduce and unpack `rfl`. Simplify using `at this`. Conclude with `hs_of_sq _ _ ((map_ne_zero _).2 hΔ) (hD.split v hv)`.

Establish `h` using `hD.off v hv`. Conclude with `(hsLaw _ _ _ h).2.1 _ _ h.even ⟨u, 1, one_ne_zero, by simp⟩`.
-/
theorem UpperTheory.V.Z.Sym.Glob.chiVal :
    UpperTheory.V.Z.Sym.Glob.ChiVal := by
  intro F _ _ Δ D hD v x x₀ hx
  refine main (fun a b h => Subtype.ext h) _ _ (hD.chi v) (fun u => ?_) x x₀ hx
  by_cases hv : v ∈ D.Sg
  · haveI := hD.real
    haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
    have hΔ : Δ ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      have := hD.neg (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w))
      rintro rfl
      simp at this
    exact hs_of_sq _ _ ((map_ne_zero _).2 hΔ) (hD.split v hv)
  · have h := hD.off v hv
    exact (hsLaw _ _ _ h).2.1 _ _ h.even ⟨u, 1, one_ne_zero, by simp⟩
