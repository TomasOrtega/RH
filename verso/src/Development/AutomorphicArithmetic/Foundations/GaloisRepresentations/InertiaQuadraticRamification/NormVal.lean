import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `Ω _ _ _ U hU q hq`. Use `set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK`. Establish `hfix : K.fixingSubgroup = U` using `InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩`. Establish `hfin : FiniteDimensional ℚ K`. Rewrite using `[← InfiniteGalois.isOpen_iff_finite, hfix]`.

Conclude with `hU`. Establish `hq0 : q ≠ 0` using `by omega`. Establish `hpp : q.minFac.Prime` using `Nat.minFac_prime (by omega)`. Use `haveI : Fact q.minFac.Prime := ⟨hpp⟩`. Establish `ha : 0 < padicValNat q.minFac q` using `one_le_padicValNat_of_dvd hq0 (Nat.minFac_dvd q)`.

Use `⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩` and prove the remaining obligations. Introduce `z n c hz hzq`. Break down `n with _ | k` into its components or cases. Establish `h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω)` using `by simpa using hzq`. Establish `h2 : q ^ c = 1` using `Nat.cast_injective h1`.

Break down `(Nat.pow_eq_one.1 h2) with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Simplify using `[h]`. Establish `hzK : z ∈ K` using `(IntermediateField.mem_fixedField_iff U z).2 hz`. Use `set w : K := ⟨z, hzK⟩ with hwdef`.

Establish `hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hzq` using `[hwdef]`. Establish `hN` using `congrArg (Algebra.norm ℚ) hw`. Rewrite `hN` using `[map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one]`.

Establish `hNw : Algebra.norm ℚ w ≠ 0`. Introduce `h0`. Rewrite `hN` using `[h0, zero_pow (Nat.succ_ne_zero k), zero_mul]`. Conclude with `zero_ne_one hN`. Establish `hqQ : (q : ℚ) ≠ 0` using `by exact_mod_cast hq0`.

Establish `hv` using `congrArg (padicValRat q.minFac) hN`. Rewrite `hv` using `[padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)), padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one, padicValRat.of_nat]`. Establish `hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ)`. Use `⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, Nat.cast_mul]`.

Take the linear combination `hv`. Conclude with `Int.natCast_dvd_natCast.1 hd`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q :=
    one_le_padicValNat_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
