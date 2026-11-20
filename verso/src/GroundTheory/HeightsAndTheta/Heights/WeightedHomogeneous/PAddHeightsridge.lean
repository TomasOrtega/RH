import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace AddBlockBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false

abbrev ConeField (ι Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial ι Ω)

def constMap (ι : Type) : Ω →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp C

/- English proof (translation)
The claim follows from `(IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω)).comp (C_injective _ _)`.
-/
theorem constMap_injective : Function.Injective (constMap (Ω := Ω) ι) :=
  (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω)).comp (C_injective _ _)

def varT (k : ι) : ConeField ι Ω := algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (X k)

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))).mpr (X_ne_zero k)`.
-/
theorem varT_ne_zero (k : ι) : varT (Ω := Ω) k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))).mpr (X_ne_zero k)

def coneHom (y : Coord n → Ω) : MvPolynomial (Coord n) ℤ →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp (Geo.mConeMap (ι := blockIdx n) y).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coneHom_apply (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    coneHom y f = algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (Geo.mConeMap (ι := blockIdx n) y f) := rfl

/- English proof (translation)
Rewrite using `[coneHom_apply]`. Simplify using `[Geo.mConeMap, constMap, varT]`.
-/
theorem coneHom_X (y : Coord n → Ω) (v : Coord n) : coneHom y (X v) = constMap ι (y v) * varT v.1 := by
  rw [coneHom_apply]
  simp [Geo.mConeMap, constMap, varT]

/- English proof (translation)
Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker, coneHom_apply, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))]`.
-/
theorem mem_mCoordIdeal_iff (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ coneHom y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, coneHom_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))]

/- English proof (translation)
Establish `h1 : Geo.mConeMap (ι` using `blockIdx n) y f = eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ X v.1 * C (y v)) f := by`. Simplify using `only [Geo.mConeMap, aeval_def]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `mul_comm _ _`.

Establish `h2 : (C (aeval y f) : MvPolynomial ι Ω) = eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ C (y v)) f`. Rewrite using `[aeval_def, algebraMap_int_eq, eval₂_comp_left]`. Use `congr 1`. Rewrite using `[coneHom_apply, h1, eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X k : MvPolynomial ι Ω)) _ hf, ← h2, mul_comm, map_mul, map_prod]`. Simplify using `only [map_pow]`.

Both sides reduce to the same expression.
-/
theorem coneHom_of_homog (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    coneHom y f = constMap ι (aeval y f) * ∏ k, varT k ^ δ k := by
  have h1 : Geo.mConeMap (ι := blockIdx n) y f =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ X v.1 * C (y v)) f := by
    simp only [Geo.mConeMap, aeval_def]
    congr 1
    funext v
    exact mul_comm _ _
  have h2 : (C (aeval y f) : MvPolynomial ι Ω) =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ C (y v)) f := by
    rw [aeval_def, algebraMap_int_eq, eval₂_comp_left]
    congr 1
  rw [coneHom_apply, h1, eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X k : MvPolynomial ι Ω)) _ hf, ← h2,
    mul_comm, map_mul, map_prod]
  simp only [map_pow]
  rfl

variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

def coordHom : P.CoordRing →+* ConeField ι Ω :=
  Ideal.Quotient.lift P.ideal (coneHom y) fun f hf ↦ by
    rw [hP] at hf
    exact (mem_mCoordIdeal_iff y f).mp hf

/- English proof (translation)
The claim follows from `RingHom.lift_injective_of_ker_le_ideal _ _ fun f hf ↦ by rw [hP] exact (mem_mCoordIdeal_iff y f).mpr (RingHom.mem_ker.mp hf)`.
-/
theorem coordHom_injective : Function.Injective (coordHom P y hP) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun f hf ↦ by
    rw [hP]
    exact (mem_mCoordIdeal_iff y f).mpr (RingHom.mem_ker.mp hf)

def funHom : P.FunField →+* ConeField ι Ω := IsFractionRing.lift (coordHom_injective P y hP)

/- English proof (translation)
Simplify using `only [funHom, ArithVariety.mkF, RingHom.comp_apply, IsFractionRing.lift_algebraMap, coordHom, Ideal.Quotient.lift_mk]`.
-/
theorem funHom_mkF (f : MvPolynomial (Coord n) ℤ) : funHom P y hP (P.mkF f) = coneHom y f := by
  simp only [funHom, ArithVariety.mkF, RingHom.comp_apply, IsFractionRing.lift_algebraMap, coordHom,
    Ideal.Quotient.lift_mk]

include hP in

/- English proof (translation)
Introduce `hy`. Apply `hc k` to reduce the goal to its premises. Rewrite using `[hP, mem_mCoordIdeal_iff, coneHom_X, hy, map_zero, zero_mul]`.
-/
theorem ne_zero_of_isLive {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) : y ⟨k, c k⟩ ≠ 0 := by
  intro hy
  apply hc k
  rw [hP, mem_mCoordIdeal_iff, coneHom_X, hy, map_zero, zero_mul]

/- English proof (translation)
Rewrite using `[ArithVariety.chartCoord, map_div₀, funHom_mkF, funHom_mkF, coneHom_X, coneHom_X, map_div₀, mul_div_mul_right _ _ (varT_ne_zero v.1)]`.
-/
theorem funHom_chartCoord (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funHom P y hP (P.chartCoord c v) = constMap ι (y v / y ⟨v.1, c v.1⟩) := by
  rw [ArithVariety.chartCoord, map_div₀, funHom_mkF, funHom_mkF, coneHom_X, coneHom_X, map_div₀,
    mul_div_mul_right _ _ (varT_ne_zero v.1)]

/- English proof (translation)
Rewrite using `[ArithVariety.chartPow, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, funHom_mkF, coneHom_X, mul_zpow]`.
-/
theorem funHom_chartPow (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funHom P y hP (P.chartPow c a) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k) * ∏ k, varT k ^ a k := by
  rw [ArithVariety.chartPow, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, funHom_mkF, coneHom_X, mul_zpow]

/- English proof (translation)
Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `⟨P.chartCoord c p, Subring.subset_closure ⟨p, rfl⟩, funHom_chartCoord P y hP c p⟩`. Consider the case `algebraMap z`.

Conclude with `⟨(z : P.FunField), intCast_mem _ z, by simp⟩`. Consider the case `add x x' _ _ hx hx'`. Take `⟨η, hη, he⟩` from `hx`. Take `⟨η', hη', he'⟩` from `hx'`. Conclude with `⟨η + η', add_mem hη hη', by rw [map_add, map_add, he, he']⟩`.

Consider the case `mul x x' _ _ hx hx'`. Take `⟨η, hη, he⟩` from `hx`. Take `⟨η', hη', he'⟩` from `hx'`. Conclude with `⟨η * η', mul_mem hη hη', by rw [map_mul, map_mul, he, he']⟩`.
-/
theorem exists_chartRing (c : (k : ι) → Fin (n k + 1)) {r : Ω}
    (hr : r ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ η ∈ P.chartRing c, funHom P y hP η = constMap ι r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨P.chartCoord c p, Subring.subset_closure ⟨p, rfl⟩, funHom_chartCoord P y hP c p⟩
  | algebraMap z =>
    exact ⟨(z : P.FunField), intCast_mem _ z, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η + η', add_mem hη hη', by rw [map_add, map_add, he, he']⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η * η', mul_mem hη hη', by rw [map_mul, map_mul, he, he']⟩

/- English proof (translation)
Establish `hden : P.mkF t.den ≠ 0` using `fun h ↦ t.den_not_mem ((P.mkF_eq_zero_iff _).mp h)`. Establish `hnum : P.mkF t.num = t.toFun * P.mkF t.den`. Rewrite using `[IntegralSection.toFun, div_mul_cancel₀ _ hden]`. Establish `hval : aeval y t.num = s * aeval y t.den` using `(ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous (fun k ↦ by have := t.deg_eq k; omega)).mpr hnum`. Establish `hden' : funHom P y hP (P.mkF t.den) ≠ 0` using `(map_ne_zero_iff _ (funHom P y hP).injective).mpr hden`.

Rewrite `hden'` using `[funHom_mkF, coneHom_of_homog y t.den_isHomogeneous]`. Establish `hc : constMap ι (aeval y t.den) ≠ 0` using `left_ne_zero_of_mul hden'`. Establish `hp : ∏ k, varT (Ω` using `Ω) k ^ t.denDeg k ≠ 0 := right_ne_zero_of_mul hden'`. Establish `hPa : ∏ k, varT (Ω` using `Ω) k ^ a k = (∏ k, varT k ^ t.numDeg k) / ∏ k, varT k ^ t.denDeg k := by`. Rewrite using `[← Finset.prod_div_distrib]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← t.deg_eq k, zpow_sub₀ (varT_ne_zero k), zpow_natCast, zpow_natCast]`. Rewrite using `[IntegralSection.toFun, map_div₀, funHom_mkF, funHom_mkF, coneHom_of_homog y t.num_isHomogeneous, coneHom_of_homog y t.den_isHomogeneous, hval, map_mul, hPa]`. Clear the denominators using the available nonvanishing facts.
-/
theorem funHom_of_reads {a : ι → ℤ} (t : IntegralSection P a) {s : Ω} (ht : P.Reads y a s t.toFun) :
    funHom P y hP t.toFun = constMap ι s * ∏ k, varT k ^ a k := by
  have hden : P.mkF t.den ≠ 0 := fun h ↦ t.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
  have hnum : P.mkF t.num = t.toFun * P.mkF t.den := by
    rw [IntegralSection.toFun, div_mul_cancel₀ _ hden]
  have hval : aeval y t.num = s * aeval y t.den :=
    (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
      (fun k ↦ by have := t.deg_eq k; omega)).mpr hnum
  have hden' : funHom P y hP (P.mkF t.den) ≠ 0 := (map_ne_zero_iff _ (funHom P y hP).injective).mpr hden
  rw [funHom_mkF, coneHom_of_homog y t.den_isHomogeneous] at hden'
  have hc : constMap ι (aeval y t.den) ≠ 0 := left_ne_zero_of_mul hden'
  have hp : ∏ k, varT (Ω := Ω) k ^ t.denDeg k ≠ 0 := right_ne_zero_of_mul hden'
  have hPa : ∏ k, varT (Ω := Ω) k ^ a k = (∏ k, varT k ^ t.numDeg k) / ∏ k, varT k ^ t.denDeg k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← t.deg_eq k, zpow_sub₀ (varT_ne_zero k), zpow_natCast, zpow_natCast]
  rw [IntegralSection.toFun, map_div₀, funHom_mkF, funHom_mkF, coneHom_of_homog y t.num_isHomogeneous,
    coneHom_of_homog y t.den_isHomogeneous, hval, map_mul, hPa]
  field_simp

end AddBlockBridge

/- English proof (translation)
Establish `h : ((aeval fun o ↦ C (w o)⁻¹ * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L).comp (aeval fun o ↦ C (w o) * X o)) = AlgHom.id L _`. Use `algHom_ext fun o ↦ ?_` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ (hw o), C_1, one_mul]`. Conclude with `Function.LeftInverse.injective (g := aeval fun o ↦ C (w o)⁻¹ * X o) fun p ↦ by`.

Simplify using `using congrArg (fun φ ↦ φ p) h`.
-/
theorem AddBlockBridge.scale_injective {σ L : Type} [Field L] (w : σ → L) (hw : ∀ o, w o ≠ 0) :
    Function.Injective (aeval fun o ↦ C (w o) * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L) := by
  have h : ((aeval fun o ↦ C (w o)⁻¹ * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L).comp
      (aeval fun o ↦ C (w o) * X o)) = AlgHom.id L _ := by
    refine algHom_ext fun o ↦ ?_
    simp only [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hw o), C_1, one_mul]
  exact Function.LeftInverse.injective (g := aeval fun o ↦ C (w o)⁻¹ * X o) fun p ↦ by
    simpa using congrArg (fun φ ↦ φ p) h

open AddBlockBridge in

/- English proof (translation)
Introduce `ι _ _ n Ω _ y P a m x' hP hx' hgen`. Establish `hsec : ∀ j, ∃ t : IntegralSection P a, P.Reads y a (x' j) t.toFun` using `fun j ↦ by`. Take `⟨t, ht⟩` from `(hCLS ι n Ω y P a 1 (x' j) hP).mp (hx' j)`. Use `⟨t.cast (one_smul ℕ a), ?_⟩` and prove the remaining obligations. Rewrite using `[show P.Reads y a = P.Reads y ((1 : ℕ) • a) by rw [one_smul]]`.

Conclude with `ht`. Use `choose t ht using hsec`. Establish `hval : ∀ j, funHom P y hP (t j).toFun = constMap ι (x' j) * ∏ k, varT k ^ a k` using `fun j ↦ funHom_of_reads P y hP (t j) (ht j)`. Establish `hquot : ∀ c, P.IsLive c → ∀ j, funHom P y hP ((t j).toFun / P.chartPow c a) = constMap ι (x' j * ∏ k, y ⟨k, c k⟩ ^ (-a k))`. Introduce `c hc j`.

Establish `hy : ∀ k, constMap ι (y ⟨k, c k⟩) ≠ 0` using `fun k ↦ (map_ne_zero_iff _ constMap_injective).mpr (ne_zero_of_isLive P y hP hc k)`. Establish `hT : ∏ k, varT (Ω` using `Ω) k ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)`. Establish `hY : ∏ k, constMap ι (y ⟨k, c k⟩) ^ a k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)`. Establish `e : ∏ k, constMap ι (y ⟨k, c k⟩ ^ (-a k)) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k)⁻¹`. Rewrite using `[← Finset.prod_inv_distrib]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, zpow_neg]`. Rewrite using `[map_div₀, hval, funHom_chartPow, map_mul, map_prod, e]`. Clear the denominators using the available nonvanishing facts. Establish `hmem : ∀ c, P.IsLive c → ∀ j, (t j).toFun / P.chartPow c a ∈ P.chartRing c`.

Introduce `c hc j`. Establish `hm` using `hx' j c (ne_zero_of_isLive P y hP hc)`. Simplify using `only [Nat.cast_one, one_mul] at hm`. Take `⟨η, hη, he⟩` from `exists_chartRing P y hP c hm`. Rewrite using `[(funHom P y hP).injective ((hquot c hc j).trans he.symm)]` and apply the resulting hypothesis.

Establish `hgen' : ∀ c, P.IsLive c → ∃ u : Fin (m + 1) → P.FunField, (∀ j, u j ∈ P.chartRing c) ∧ ∑ j, u j * ((t j).toFun / P.chartPow c a) = 1`. Introduce `c hc`. Take `⟨u, hu, hsum⟩` from `hgen c (ne_zero_of_isLive P y hP hc)`. Use `choose v hv hve using fun j ↦ exists_chartRing P y hP c (hu j)`. Use `⟨v, hv, (funHom P y hP).injective ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum, map_one, ← map_one (constMap (Ω := Ω) ι), ← hsum, map_sum]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hve j, hquot c hc j]`. Set `D : AddBlockData P` to `{ deg := a size := m elt := fun j ↦ (t j).toFun elt_deg := fun j ↦ ⟨(t j).num, (t j).den, (t j).numDeg, (t j).denDeg, (t j).num_isHomogeneous, (t j).den_isHomogeneous, (t j).deg_eq, (t j).den_not_mem, rfl⟩ chart_mem := hmem generating := hgen' }`. Set `w : Option ι → ConeField ι Ω` to `fun o ↦ o.elim (∏ k, varT k ^ a k) varT`.

Establish `hw : ∀ o, w o ≠ 0`. Introduce and unpack `(_ | k)`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)`. Conclude with `varT_ne_zero k`. Set `σ : MvPolynomial (Option ι) (ConeField ι Ω) →ₐ[ConeField ι Ω] MvPolynomial (Option ι) (ConeField ι Ω)` to `aeval fun o ↦ C (w o) * X o`.

Establish `hcomp : (map (funHom P y hP)).comp D.extMap = σ.toRingHom.comp ((map (constMap ι)).comp (Geo.mConeMap (ι` using `blockIdx D.extSizes) (D.plusCoord y x')).toRingHom) := by`. Use `MvPolynomial.ringHom_ext (fun r ↦ by simp) fun v ↦ ?_` and prove the remaining obligations. Break down `v with ⟨_ | k, i⟩` into its components or cases. Simplify using `[D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord]`. Rewrite using `[show (funHom P y hP) (t i).toFun = _ from hval i, map_mul, map_prod]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord, funHom_mkF, coneHom_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `hread : D.BlockReading y x'` using `{ ideal_eq := hP ext_eq := by`. Use extensionality with `f`.

Rewrite using `[AddBlockData.extIdeal, Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker]`. Establish `hf` using `congrArg (fun ψ ↦ ψ f) hcomp`. Simplify using `only [RingHom.comp_apply] at hf`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `hf` using `[h, map_zero]`. Establish `h2` using `scale_injective w hw (hf.symm.trans (map_zero σ).symm)`. Conclude with `map_injective _ constMap_injective (h2.trans (map_zero _).symm)`. Introduce `h`. Use `map_injective _ (funHom P y hP).injective ?_` and prove the remaining obligations.

Rewrite using `[hf, map_zero]`. Simplify using `[h]`. Use `reads := ht }`. Conclude with `⟨D, rfl, rfl, hread⟩`.
-/
theorem AddBlockBridge.proof (hCLS : ChartLatSection.Statement) : AddBlockBridge.Statement := by
  intro ι _ _ n Ω _ y P a m x' hP hx' hgen
  have hsec : ∀ j, ∃ t : IntegralSection P a, P.Reads y a (x' j) t.toFun := fun j ↦ by
    obtain ⟨t, ht⟩ := (hCLS ι n Ω y P a 1 (x' j) hP).mp (hx' j)
    refine ⟨t.cast (one_smul ℕ a), ?_⟩
    rw [show P.Reads y a = P.Reads y ((1 : ℕ) • a) by rw [one_smul]]
    exact ht
  choose t ht using hsec
  have hval : ∀ j, funHom P y hP (t j).toFun = constMap ι (x' j) * ∏ k, varT k ^ a k :=
    fun j ↦ funHom_of_reads P y hP (t j) (ht j)

  have hquot : ∀ c, P.IsLive c → ∀ j, funHom P y hP ((t j).toFun / P.chartPow c a) =
      constMap ι (x' j * ∏ k, y ⟨k, c k⟩ ^ (-a k)) := by
    intro c hc j
    have hy : ∀ k, constMap ι (y ⟨k, c k⟩) ≠ 0 := fun k ↦
      (map_ne_zero_iff _ constMap_injective).mpr (ne_zero_of_isLive P y hP hc k)
    have hT : ∏ k, varT (Ω := Ω) k ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    have hY : ∏ k, constMap ι (y ⟨k, c k⟩) ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have e : ∏ k, constMap ι (y ⟨k, c k⟩ ^ (-a k)) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [map_zpow₀, zpow_neg]
    rw [map_div₀, hval, funHom_chartPow, map_mul, map_prod, e]
    field_simp
  have hmem : ∀ c, P.IsLive c → ∀ j, (t j).toFun / P.chartPow c a ∈ P.chartRing c := by
    intro c hc j
    have hm := hx' j c (ne_zero_of_isLive P y hP hc)
    simp only [Nat.cast_one, one_mul] at hm
    obtain ⟨η, hη, he⟩ := exists_chartRing P y hP c hm
    rwa [(funHom P y hP).injective ((hquot c hc j).trans he.symm)]
  have hgen' : ∀ c, P.IsLive c → ∃ u : Fin (m + 1) → P.FunField, (∀ j, u j ∈ P.chartRing c) ∧
      ∑ j, u j * ((t j).toFun / P.chartPow c a) = 1 := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c (ne_zero_of_isLive P y hP hc)
    choose v hv hve using fun j ↦ exists_chartRing P y hP c (hu j)
    refine ⟨v, hv, (funHom P y hP).injective ?_⟩
    rw [map_sum, map_one, ← map_one (constMap (Ω := Ω) ι), ← hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_mul, hve j, hquot c hc j]
  let D : AddBlockData P :=
    { deg := a
      size := m
      elt := fun j ↦ (t j).toFun
      elt_deg := fun j ↦ ⟨(t j).num, (t j).den, (t j).numDeg, (t j).denDeg, (t j).num_isHomogeneous,
        (t j).den_isHomogeneous, (t j).deg_eq, (t j).den_not_mem, rfl⟩
      chart_mem := hmem
      generating := hgen' }

  let w : Option ι → ConeField ι Ω := fun o ↦ o.elim (∏ k, varT k ^ a k) varT
  have hw : ∀ o, w o ≠ 0 := by
    rintro (_ | k)
    · exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    · exact varT_ne_zero k
  let σ : MvPolynomial (Option ι) (ConeField ι Ω) →ₐ[ConeField ι Ω] MvPolynomial (Option ι) (ConeField ι Ω) :=
    aeval fun o ↦ C (w o) * X o
  have hcomp : (map (funHom P y hP)).comp D.extMap = σ.toRingHom.comp
      ((map (constMap ι)).comp (Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun v ↦ ?_
    rcases v with ⟨_ | k, i⟩
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord]
      rw [show (funHom P y hP) (t i).toFun = _ from hval i, map_mul, map_prod]
      ring
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord,
        funHom_mkF, coneHom_X]
      ring
  have hread : D.BlockReading y x' :=
    { ideal_eq := hP
      ext_eq := by
        ext f
        rw [AddBlockData.extIdeal, Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker]
        have hf := congrArg (fun ψ ↦ ψ f) hcomp
        simp only [RingHom.comp_apply] at hf
        constructor
        · intro h
          rw [h, map_zero] at hf
          have h2 := scale_injective w hw (hf.symm.trans (map_zero σ).symm)
          exact map_injective _ constMap_injective (h2.trans (map_zero _).symm)
        · intro h
          refine map_injective _ (funHom P y hP).injective ?_
          rw [hf, map_zero]
          simp [h]
      reads := ht }
  exact ⟨D, rfl, rfl, hread⟩

end

end GroundTheory.Heights₂.Heights
