import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.TangentDegree
open LateralTheory.DivDb

variable {C : Type} [Field C]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma aeval_self_eq_ev {N : ℕ} (x : Mat C N) (f : MP C N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = ev x f := rfl

noncomputable def U {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) i j

noncomputable def Z {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => (((k + 1).factorial : C)⁻¹ • Y ^ (k + 1)) i j

/- English proof (translation)
Use extensionality with `i j k`. Break down `k with _ | k` into its components or cases. Apply the tactic sequence `simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, PowerSeries.coeff_zero_X_mul, add_zero, Matrix.one_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one] split_ifs <;> simp`. Apply the tactic sequence `simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, PowerSeries.coeff_succ_X_mul, Matrix.one_apply] split_ifs <;> simp`.
-/
lemma U_eq {N : ℕ} (Y : Mat C N) : U Y = 1 + (PowerSeries.X : PowerSeries C) • Z Y := by
  ext i j k
  rcases k with _ | k
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      PowerSeries.coeff_zero_X_mul, add_zero, Matrix.one_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
    split_ifs <;> simp
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      PowerSeries.coeff_succ_X_mul, Matrix.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[Z, PowerSeries.coeff_mk]`.
-/
lemma constantCoeff_Z {N : ℕ} (Y : Mat C N) (i j : Fin N) : PowerSeries.constantCoeff (Z Y i j) = Y i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Z, PowerSeries.coeff_mk]

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hk]`.
-/
lemma map_aeval_ring {R S σ : Type} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S] (k : R →+* S)
    (hk : k.comp (algebraMap C R) = algebraMap C S) (x : σ → R) (f : MvPolynomial σ C) :
    k (MvPolynomial.aeval x f) = MvPolynomial.aeval (k ∘ x) f := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hk]

/- English proof (translation)
Take `⟨𝓕, h𝓕⟩` from `hD C N n`. Use `⟨𝓕, h𝓕, fun f hf x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_self_eq_ev]`. Conclude with `(h𝓕 C x).1 (hS x hx) f hf`.
-/
lemma van_of (hD : DegPoly) {N n : ℕ} (S : Submonoid (Mat C N)) (hS : ∀ x ∈ S, Deg n x) :
    ∃ 𝓕 : Set (MP C N), (∀ (F : Type) [Field F] [Algebra C F] (x : Mat F N),
      Deg n x ↔ ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = 0) ∧
      ∀ f ∈ 𝓕, f ∈ Van (S : Set (Mat C N)) := by
  obtain ⟨𝓕, h𝓕⟩ := hD C N n
  refine ⟨𝓕, h𝓕, fun f hf x hx => ?_⟩
  rw [← aeval_self_eq_ev]
  exact (h𝓕 C x).1 (hS x hx) f hf

/- English proof (translation)
Take `⟨𝓕, h𝓕, hvan⟩` from `van_of hD S hS`. Set `F` to `FractionRing (PowerSeries C)`. Set `ι : PowerSeries C →+* F` to `algebraMap (PowerSeries C) F`. Set `alg : Algebra C F` to `(ι.comp (algebraMap C (PowerSeries C))).toAlgebra`. Establish `hιinj : Function.Injective ι` using `IsFractionRing.injective (PowerSeries C) F`.

Establish `hmap : ∀ (M : Matrix (Fin N) (Fin N) (PowerSeries C)) (f : MP C N), @MvPolynomial.aeval C F _ _ _ alg (fun p : Fin N × Fin N => (M.map ι) p.1 p.2) f = ι (MvPolynomial.aeval (fun p : Fin N × Fin N => M p.1 p.2) f)`. Introduce `M f`. Rewrite using `[map_aeval_ring (S := F) ι rfl]`. Both sides reduce to the same expression. Establish `hUF : Deg n ((U Y).map ι)`.

Use `(@h𝓕 F _ alg ((U Y).map ι)).2 fun f hf => ?_` and prove the remaining obligations. Rewrite using `[hmap]`. Use `hE C N S Y hY f (hvan f hf)` as an intermediate fact. Simplify using `only [U] at this ⊢`. Rewrite using `[this, map_zero]`.

Use `set s : F := ι PowerSeries.X with hsdef`. Establish `hs : s ≠ 0` using `(map_ne_zero_iff ι hιinj).2 PowerSeries.X_ne_zero`. Establish `hUZ : (U Y).map ι = 1 + s • (Z Y).map ι`. Rewrite using `[U_eq]`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply, hsdef]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hZF : Deg n ((Z Y).map ι)`. Take `⟨q, hq0, hqd, hqx⟩` from `hUF`. Use `⟨q.comp (Polynomial.C s * Polynomial.X + Polynomial.C 1), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Break down `Polynomial.comp_eq_zero_iff.1 h with h | ⟨_, h⟩` into its components or cases. Conclude with `hq0 h`. Use `congrArg Polynomial.natDegree h` as an intermediate fact. Rewrite `this` using `[Polynomial.natDegree_linear hs, Polynomial.natDegree_C]`.

Conclude with `one_ne_zero this`. Rewrite using `[Polynomial.natDegree_comp, Polynomial.natDegree_linear hs, mul_one]`. Conclude with `hqd`. Rewrite using `[Polynomial.aeval_comp]`. Use `hqx using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[hUZ]`. Simplify using `[Algebra.algebraMap_eq_smul_one, add_comm]`. Establish `hZ0 : ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => Z Y p.1 p.2) f = 0`. Introduce `f hf`. Use `(@h𝓕 F _ alg ((Z Y).map ι)).1 hZF f hf` as an intermediate fact.

Rewrite `this` using `[hmap]`. Conclude with `(map_eq_zero_iff ι hιinj).1 this`. Use `(h𝓕 C Y).2 fun f hf => ?_` and prove the remaining obligations. Establish `hk : (PowerSeries.constantCoeff (R` using `C)).comp (algebraMap C (PowerSeries C)) = algebraMap C C := by`. Use extensionality with `c`.

Simplify using the standard rewrite rules. Use `congrArg PowerSeries.constantCoeff (hZ0 f hf)` as an intermediate fact. Rewrite `this` using `[map_aeval_ring _ hk, map_zero]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use `congr 1`.

Use function extensionality and compare the values at `p`. Simplify using `[constantCoeff_Z]`.
-/
lemma tan_deg (hE : ExpVan) (hD : DegPoly) [CharZero C] {N n : ℕ} (S : Submonoid (Mat C N))
    (hS : ∀ x ∈ S, Deg n x) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) : Deg n Y := by
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  let F := FractionRing (PowerSeries C)
  let ι : PowerSeries C →+* F := algebraMap (PowerSeries C) F
  let alg : Algebra C F := (ι.comp (algebraMap C (PowerSeries C))).toAlgebra
  have hιinj : Function.Injective ι := IsFractionRing.injective (PowerSeries C) F
  have hmap : ∀ (M : Matrix (Fin N) (Fin N) (PowerSeries C)) (f : MP C N),
      @MvPolynomial.aeval C F _ _ _ alg (fun p : Fin N × Fin N => (M.map ι) p.1 p.2) f
        = ι (MvPolynomial.aeval (fun p : Fin N × Fin N => M p.1 p.2) f) := by
    intro M f
    rw [map_aeval_ring (S := F) ι rfl]
    rfl
  have hUF : Deg n ((U Y).map ι) := by
    refine (@h𝓕 F _ alg ((U Y).map ι)).2 fun f hf => ?_
    rw [hmap]
    have := hE C N S Y hY f (hvan f hf)
    simp only [U] at this ⊢
    rw [this, map_zero]
  set s : F := ι PowerSeries.X with hsdef
  have hs : s ≠ 0 := (map_ne_zero_iff ι hιinj).2 PowerSeries.X_ne_zero
  have hUZ : (U Y).map ι = 1 + s • (Z Y).map ι := by
    rw [U_eq]; ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      Matrix.one_apply, hsdef]
    split_ifs <;> simp
  have hZF : Deg n ((Z Y).map ι) := by
    obtain ⟨q, hq0, hqd, hqx⟩ := hUF
    refine ⟨q.comp (Polynomial.C s * Polynomial.X + Polynomial.C 1), ?_, ?_, ?_⟩
    · intro h
      rcases Polynomial.comp_eq_zero_iff.1 h with h | ⟨_, h⟩
      · exact hq0 h
      · have := congrArg Polynomial.natDegree h
        rw [Polynomial.natDegree_linear hs, Polynomial.natDegree_C] at this
        exact one_ne_zero this
    · rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hs, mul_one]; exact hqd
    · rw [Polynomial.aeval_comp]
      convert hqx using 2
      rw [hUZ]
      simp [Algebra.algebraMap_eq_smul_one, add_comm]
  have hZ0 : ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => Z Y p.1 p.2) f = 0 := by
    intro f hf
    have := (@h𝓕 F _ alg ((Z Y).map ι)).1 hZF f hf
    rw [hmap] at this
    exact (map_eq_zero_iff ι hιinj).1 this
  refine (h𝓕 C Y).2 fun f hf => ?_
  have hk : (PowerSeries.constantCoeff (R := C)).comp (algebraMap C (PowerSeries C)) = algebraMap C C := by
    ext c; simp
  have := congrArg PowerSeries.constantCoeff (hZ0 f hf)
  rw [map_aeval_ring _ hk, map_zero] at this
  convert this using 2
  congr 1
  funext p
  simp [constantCoeff_Z]

/- English proof (translation)
Introduce `C _ _ N n S hS`. Use `⟨fun x hx => ?_, fun Y hY => tan_deg hE hD S hS Y hY⟩` and prove the remaining obligations. Take `⟨𝓕, h𝓕, hvan⟩` from `van_of hD S hS`. Use `(h𝓕 C x).2 fun f hf => ?_` and prove the remaining obligations. Rewrite using `[aeval_self_eq_ev]`.

Conclude with `hx f (hvan f hf)`.
-/
theorem TanDeg_of (hE : ExpVan) (hD : DegPoly) : TanDeg := by
  intro C _ _ N n S hS
  refine ⟨fun x hx => ?_, fun Y hY => tan_deg hE hD S hS Y hY⟩
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  refine (h𝓕 C x).2 fun f hf => ?_
  rw [aeval_self_eq_ev]
  exact hx f (hvan f hf)

end LateralTheory.DivDb.TangentDegree
