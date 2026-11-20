import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatLargeCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin.CondTest

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem barF_tmul (a : Af D.host.F) (x : D.host.E) : barF D (a ⊗ₜ x) = a ⊗ₜ star x := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [barF_tmul, barF_tmul, star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem barF_barF (x : AfE D) : barF D (barF D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [barF_tmul, barF_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Simplify using `[NormOne]`.
-/
theorem normOne_one : NormOne (1 : (AfE D)ˣ) := by simp [NormOne]

/- English proof (translation)
Simplify using `[NormOne]`.
-/
theorem normOne_neg_one : NormOne (-1 : (AfE D)ˣ) := by simp [NormOne]

/- English proof (translation)
Unfold `NormOne at *`. Rewrite using `[Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, one_mul]`.
-/
theorem NormOne.mul' {x y : (AfE D)ˣ} (hx : NormOne x) (hy : NormOne y) : NormOne (x * y) := by
  unfold NormOne at *
  rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, one_mul]

/- English proof (translation)
The claim follows from `Units.inv_eq_of_mul_eq_one_right hx`.
-/
theorem NormOne.inv_eq {x : (AfE D)ˣ} (hx : NormOne x) : ((x⁻¹ : (AfE D)ˣ) : AfE D) = barF D x :=
  Units.inv_eq_of_mul_eq_one_right hx

/- English proof (translation)
Establish `h` using `NormOne.inv_eq hx`. Unfold `NormOne at *`. Rewrite using `[h, barF_barF, mul_comm, hx]`.
-/
theorem NormOne.inv' {x : (AfE D)ˣ} (hx : NormOne x) : NormOne x⁻¹ := by
  have h := NormOne.inv_eq hx
  unfold NormOne at *
  rw [h, barF_barF, mul_comm, hx]

/- English proof (translation)
Unfold `NormOne`. Establish `h : ((Units.map (barF D : AfE D →* AfE D) y)⁻¹ : (AfE D)ˣ) = Units.map (barF D : AfE D →* AfE D) y⁻¹` using `(map_inv _ y).symm`. Rewrite using `[h, Units.val_mul, map_mul]`. Express the relevant statement in the definitionally equal form `(y : AfE D) * barF D (y⁻¹ : (AfE D)ˣ) * (barF D y * barF D (barF D (y⁻¹ : (AfE D)ˣ))) = 1`. Rewrite using `[barF_barF, mul_comm (barF D (y : AfE D)), mul_mul_mul_comm, ← map_mul]`.

Simplify using the standard rewrite rules.
-/
theorem normOne_div (y : (AfE D)ˣ) : NormOne (y * (Units.map (barF D : AfE D →* AfE D) y)⁻¹) := by
  unfold NormOne
  have h : ((Units.map (barF D : AfE D →* AfE D) y)⁻¹ : (AfE D)ˣ) = Units.map (barF D : AfE D →* AfE D) y⁻¹ :=
    (map_inv _ y).symm
  rw [h, Units.val_mul, map_mul]
  change (y : AfE D) * barF D (y⁻¹ : (AfE D)ˣ) * (barF D y * barF D (barF D (y⁻¹ : (AfE D)ˣ))) = 1
  rw [barF_barF, mul_comm (barF D (y : AfE D)), mul_mul_mul_comm, ← map_mul]
  simp

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Take `⟨w, hw, e⟩` from `hx`. Conclude with `⟨k • w, (intAE D).nsmul_mem hw k, by rw [e, mul_smul]⟩`.
-/
theorem congOne_of_dvd {M N : ℕ} (h : M ∣ N) {x : (AfE D)ˣ} (hx : CongOne N x) : CongOne M x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨w, hw, e⟩ := hx
  exact ⟨k • w, (intAE D).nsmul_mem hw k, by rw [e, mul_smul]⟩

/- English proof (translation)
Introduce `h` and use `by obtain ⟨x, -, -, hx⟩ := h.ram exact hx rfl`.
-/
theorem not_xiOK_one (p : ℕ) : ¬ XiOK D p 1 := fun h => by
  obtain ⟨x, -, -, hx⟩ := h.ram
  exact hx rfl

/- English proof (translation)
Introduce `h` and use `by obtain ⟨x, h1, h2, hx⟩ := h.ram exact hx (h.tame x h1 (by rwa [mul_one]))`.
-/
theorem not_xiOK_level_one (xi : (AfE D)ˣ →* ℂˣ) : ¬ XiOK D 1 xi := fun h => by
  obtain ⟨x, h1, h2, hx⟩ := h.ram
  exact hx (h.tame x h1 (by rwa [mul_one]))

/- English proof (translation)
Simplify using `[h.rat x a e hx] tame x h1 h2 := by simp [h.tame x h1 h2] ram := by`. Take `⟨x, h1, h2, hx⟩` from `h.ram`. Conclude with `⟨x, h1, h2, by simpa using hx⟩`. Use `fin := by`. Take `⟨m, hm, e⟩` from `h.fin`.

Conclude with `⟨m, hm, fun x hx => by simp [e x hx]⟩`. Use `val x hx := by simpa using (FO D).inv_mem (h.val x hx)`.
-/
theorem xiOK_inv {p : ℕ} {xi : (AfE D)ˣ →* ℂˣ} (h : XiOK D p xi) : XiOK D p xi⁻¹ where
  rat x a e hx := by simp [h.rat x a e hx]
  tame x h1 h2 := by simp [h.tame x h1 h2]
  ram := by
    obtain ⟨x, h1, h2, hx⟩ := h.ram
    exact ⟨x, h1, h2, by simpa using hx⟩
  fin := by
    obtain ⟨m, hm, e⟩ := h.fin
    exact ⟨m, hm, fun x hx => by simp [e x hx]⟩
  val x hx := by simpa using (FO D).inv_mem (h.val x hx)

/- English proof (translation)
The claim follows from `h.rat (-1) (-1) (by rw [TensorProduct.tmul_neg]; rfl) normOne_neg_one`.
-/
theorem xi_neg_one {p : ℕ} {xi : (AfE D)ˣ →* ℂˣ} (h : XiOK D p xi) : xi (-1) = 1 :=
  h.rat (-1) (-1) (by rw [TensorProduct.tmul_neg]; rfl) normOne_neg_one

/- English proof (translation)
Use `(primeClass_eq_splitK_iff H).2 ⟨fun h => ?_, H.q_prime.ne_zero.symm, H.d_prime.ne_zero.symm, jacobiSym.zero_right _⟩` and prove the remaining obligations. Conclude with `Nat.not_prime_zero (Nat.prime_of_mem_primeFactors h)`.
-/
theorem primeClass_zero {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : primeClass H 0 = PrimeClass.splitK := by
  refine (primeClass_eq_splitK_iff H).2 ⟨fun h => ?_, H.q_prime.ne_zero.symm, H.d_prime.ne_zero.symm, jacobiSym.zero_right _⟩
  exact Nat.not_prime_zero (Nat.prime_of_mem_primeFactors h)

/- English proof (translation)
Break down `h.own with rfl | rfl` into its components or cases. Conclude with `⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩`. Conclude with `⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩`.
-/
theorem prime_of_fieldOK {p : ℕ} (h : FieldOK D p) : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
  rcases h.own with rfl | rfl
  · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
  · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩

/- English proof (translation)
The claim follows from `((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top`.
-/
theorem zeta_isIntegral {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top

/- English proof (translation)
Take `⟨F₁, _, h₁⟩` from `GlobalTheory.CurveField.exists_curveOver H hn`. Use `IntermediateField.adjoin.finiteDimensional (zeta_isIntegral hp)` as an intermediate fact. Use `⟨F₁ ⊔ IntermediateField.adjoin ℚ {zeta p}, inferInstance, fun F hF => ⟨?_, fun τ hτ => h₁ τ fun x hx => ?_⟩⟩` and prove the remaining obligations. Conclude with `hF (le_sup_right (a := F₁) (IntermediateField.mem_adjoin_simple_self ℚ _))`. Conclude with `hτ x (hF (le_sup_left (a := F₁) hx))`.
-/
theorem exists_field {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {n p : ℕ}
    (hn : 0 < n) (hp : 0 < p) : ∃ F₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ F₀ ∧
      ∀ F, F₀ ≤ F → zeta p ∈ F ∧ GlobalTheory.CompRat.CurveOver H F n := by
  obtain ⟨F₁, _, h₁⟩ := GlobalTheory.CurveField.exists_curveOver H hn
  have := IntermediateField.adjoin.finiteDimensional (zeta_isIntegral hp)
  refine ⟨F₁ ⊔ IntermediateField.adjoin ℚ {zeta p}, inferInstance, fun F hF => ⟨?_, fun τ hτ => h₁ τ fun x hx => ?_⟩⟩
  · exact hF (le_sup_right (a := F₁) (IntermediateField.mem_adjoin_simple_self ℚ _))
  · exact hτ x (hF (le_sup_left (a := F₁) hx))

/- English proof (translation)
Establish `h : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, y, rfl⟩`. Conclude with `GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)`. Conclude with `(FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 x).1 (h hx))`.
-/
theorem integral_of_mem_intAE {x : D.host.E} (hx : (1 : Af D.host.F) ⊗ₜ[D.host.F] x ∈ intAE D) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) = x := by
  have h : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 x).1 (h hx))

/- English proof (translation)
Introduce and unpack `⟨w, hw, e⟩`. Establish `hN0 : (N : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hw' : w = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((-2 : D.host.E) / N)`. Set `i : D.host.E →ₐ[D.host.F] AfE D` to `Algebra.TensorProduct.includeRight`. Express the relevant statement in the definitionally equal form `w = i _`.

Establish `e' : i (-2) = i N * w`. Rewrite using `[map_natCast, ← nsmul_eq_mul, ← e, map_neg, map_ofNat, Units.val_neg, Units.val_one]`. Evaluate the numerical expressions. Establish `: i (-2 / N) = i (N : D.host.E)⁻¹ * i (-2)` using `by rw [← map_mul]; congr 1; ring`. Rewrite using `[this, e', ← mul_assoc, ← map_mul, inv_mul_cancel₀ hN0, map_one, one_mul]`.

Take `⟨y, hy⟩` from `integral_of_mem_intAE (hw' ▸ hw)`. Establish `hi : IsIntegral ℤ ((-2 : D.host.E) / N)` using `hy ▸ RingOfIntegers.isIntegral_coe y`. Establish `hq : IsIntegral ℤ ((-2 : ℚ) / N)`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]`. Simplify using `using hi`.

Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hq`. Establish `hNq : (N : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h2 : k * (N : ℤ) = -2`. Establish `: (k : ℚ) * N = -2`. Rewrite using `[show (k : ℚ) = -2 / N from hk, div_mul_cancel₀ _ hNq]`.

Conclude with `this` after adjusting the coercions. Establish `hd : (N : ℤ) ∣ 2` using `⟨-k, by linarith⟩`. Use `Int.le_of_dvd (by norm_num) hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_congOne_neg_one {N : ℕ} (hN : 3 ≤ N) : ¬ CongOne N (-1 : (AfE D)ˣ) := by
  rintro ⟨w, hw, e⟩
  have hN0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hw' : w = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((-2 : D.host.E) / N) := by
    let i : D.host.E →ₐ[D.host.F] AfE D := Algebra.TensorProduct.includeRight
    change w = i _
    have e' : i (-2) = i N * w := by
      rw [map_natCast, ← nsmul_eq_mul, ← e, map_neg, map_ofNat, Units.val_neg, Units.val_one]
      norm_num
    have : i (-2 / N) = i (N : D.host.E)⁻¹ * i (-2) := by rw [← map_mul]; congr 1; ring
    rw [this, e', ← mul_assoc, ← map_mul, inv_mul_cancel₀ hN0, map_one, one_mul]
  obtain ⟨y, hy⟩ := integral_of_mem_intAE (hw' ▸ hw)
  have hi : IsIntegral ℤ ((-2 : D.host.E) / N) := hy ▸ RingOfIntegers.isIntegral_coe y
  have hq : IsIntegral ℤ ((-2 : ℚ) / N) := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]
    simpa using hi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : k * (N : ℤ) = -2 := by
    have : (k : ℚ) * N = -2 := by
      rw [show (k : ℚ) = -2 / N from hk, div_mul_cancel₀ _ hNq]
    exact_mod_cast this
  have hd : (N : ℤ) ∣ 2 := ⟨-k, by linarith⟩
  have := Int.le_of_dvd (by norm_num) hd
  omega

/- English proof (translation)
Take `⟨I, c', hle, h⟩` from `GlobalTheory.SplitPrimeData.exists_deltaDat_large_coeff E H Dw l Xo c h1 hA p hp h5 hc hj`. Use `⟨I, c', hle, fun c'' h'' n => ?_⟩` and prove the remaining obligations. Take `⟨d, a1, a2, a3, a4, a5, a6, a7, a8⟩` from `h c'' h'' n`. Conclude with `⟨d, ⟨a1, a2, a3, a4, a5⟩, ⟨a6, a7⟩, a8⟩`.
-/
theorem exists_deltaOK {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h1 : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (p : ℕ)
    (hp : p.Prime) (h5 : 5 ≤ p) (hc : p.Coprime l.M) (hj : jacobiSym (-(H.d : ℤ)) p = 1) :
    ∃ (I : Ideal (𝓞 E)) (c' : Coeff l), c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → ∀ n : ℕ,
      ∃ d : DeltaDat Xo c'' n, DeltaOK d p I := by
  obtain ⟨I, c', hle, h⟩ := GlobalTheory.SplitPrimeData.exists_deltaDat_large_coeff E H Dw l Xo c h1 hA p hp h5 hc hj
  refine ⟨I, c', hle, fun c'' h'' n => ?_⟩
  obtain ⟨d, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h c'' h'' n
  exact ⟨d, ⟨a1, a2, a3, a4, a5⟩, ⟨a6, a7⟩, a8⟩

/- English proof (translation)
The claim follows from `hp full := GlobalTheory.Mem.hermitianCodeWordStages_ringOfIntegers_full X zetaM := GlobalTheory.Mem.hermitianCodeWordStages_has_rootOfUnity X zetaP := hz curve := hc kpsi := hk vol := hv bad := h0 split := by rcases hp with rfl | rfl · exact X.B.level_split _ X.B.host.pde_level.1 …`.
-/
theorem fieldOK_of_stages (X : GlobalTheory.Mem.Stages) {p : ℕ} (hp : p = X.toD7.host.pde ∨ p = X.toD7.host.pde')
    (hz : zeta p ∈ FO X.toD7)
    (hc : GlobalTheory.CompRat.CurveOver (hostOfRecord X.toD7) (FO X.toD7) (X.toD7.host.g 0 * X.toD7.host.g 1 * p))
    (hk : OKPsi X.toD7) (hv : VolTieG X.toD7) (h0 : 0 ∉ X.toD7.host.levelPrimes) : FieldOK X.toD7 p where
  own := hp
  full := GlobalTheory.Mem.hermitianCodeWordStages_ringOfIntegers_full X
  zetaM := GlobalTheory.Mem.hermitianCodeWordStages_has_rootOfUnity X
  zetaP := hz
  curve := hc
  kpsi := hk
  vol := hv
  bad := h0
  split := by
    rcases hp with rfl | rfl
    · exact X.B.level_split _ X.B.host.pde_level.1
    · exact X.B.level_split _ X.B.host.pde_level.2

end GlobalTheory.FinalJoin.CondTest
