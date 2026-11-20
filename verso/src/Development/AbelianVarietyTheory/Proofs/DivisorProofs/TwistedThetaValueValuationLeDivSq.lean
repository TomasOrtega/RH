import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.TwistValBound

section Additive

variable {K L : Type} [Field K] [Field L]

/- English proof (translation)
Set `φ : Kˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun a => Multiplicative.ofAdd (v a)) fun a b => by`. Rewrite using `[Units.val_mul, hv _ _ a.ne_zero b.ne_zero, ofAdd_add]`. Establish `h` using `congrArg Multiplicative.toAdd (map_zpow φ (Units.mk0 x hx) n)`. Simplify `h` using `[φ]`.
-/
theorem add_zpow (v : K → ℤ) (hv : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y) {x : K} (hx : x ≠ 0) (n : ℤ) :
    v (x ^ n) = n * v x := by
  let φ : Kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun a => Multiplicative.ofAdd (v a)) fun a b => by
    rw [Units.val_mul, hv _ _ a.ne_zero b.ne_zero, ofAdd_add]
  have h := congrArg Multiplicative.toAdd (map_zpow φ (Units.mk0 x hx) n)
  simpa [φ] using h

/- English proof (translation)
Establish `key : ∀ a b : ℤ, a * v x + b * v y = 0 → 0 ≤ a * v' (f x) + b * v' (f y)`. Introduce `a b hab`. Establish `h1` using `h (x ^ a * y ^ b) (mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy)) (by`. Rewrite using `[hv _ _ (zpow_ne_zero _ hx) (zpow_ne_zero _ hy), add_zpow v hv hx, add_zpow v hv hy, hab])`. Establish `hfx : f x ≠ 0` using `(map_ne_zero f).2 hx`.

Establish `hfy : f y ≠ 0` using `(map_ne_zero f).2 hy`. Rewrite `h1` using `[map_mul, map_zpow₀, map_zpow₀, hv' _ _ (zpow_ne_zero _ hfx) (zpow_ne_zero _ hfy), add_zpow v' hv' hfx, add_zpow v' hv' hfy]`. Then use the resulting hypothesis. Establish `h1` using `key (v y) (-v x) (by ring)`. Establish `h2` using `key (-v y) (v x) (by ring)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proportional (f : K →+* L) (v : K → ℤ) (v' : L → ℤ)
    (hv : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hv' : ∀ x y, x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (h : ∀ x, x ≠ 0 → 0 ≤ v x → 0 ≤ v' (f x)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v' (f x) * v y = v x * v' (f y) := by
  have key : ∀ a b : ℤ, a * v x + b * v y = 0 → 0 ≤ a * v' (f x) + b * v' (f y) := by
    intro a b hab
    have h1 := h (x ^ a * y ^ b) (mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy)) (by
      rw [hv _ _ (zpow_ne_zero _ hx) (zpow_ne_zero _ hy), add_zpow v hv hx, add_zpow v hv hy, hab])
    have hfx : f x ≠ 0 := (map_ne_zero f).2 hx
    have hfy : f y ≠ 0 := (map_ne_zero f).2 hy
    rwa [map_mul, map_zpow₀, map_zpow₀, hv' _ _ (zpow_ne_zero _ hfx) (zpow_ne_zero _ hfy),
      add_zpow v' hv' hfx, add_zpow v' hv' hfy] at h1
  have h1 := key (v y) (-v x) (by ring)
  have h2 := key (-v y) (v x) (by ring)
  linarith

end Additive

section Ord

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def ordR (a : R) : ℕ := (IsDiscreteValuationRing.addVal R a).toNat

def ordK (x : FractionRing R) : ℤ :=
  (ordR R (IsLocalization.surj (nonZeroDivisors R) x).choose.1 : ℤ) -
    (ordR R ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) : ℤ)

variable {R}

/- English proof (translation)
Unfold `ordR`. Rewrite using `[AddValuation.map_mul, ENat.toNat_add (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]`.
-/
theorem ordR_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : ordR R (a * b) = ordR R a + ordR R b := by
  unfold ordR
  rw [AddValuation.map_mul, ENat.toNat_add (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]

/- English proof (translation)
Unfold `ordR`. Rewrite using `[ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff]`. Simplify using `[ha, IsDiscreteValuationRing.addVal_eq_top_iff]`.
-/
theorem ordR_eq_zero_iff {a : R} (ha : a ≠ 0) : ordR R a = 0 ↔ IsUnit a := by
  unfold ordR
  rw [ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff]
  simp [ha, IsDiscreteValuationRing.addVal_eq_top_iff]

/- English proof (translation)
Unfold `ordR at h`. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd]`. Rewrite using `[← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R a) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha), ← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R b) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]`. Conclude with `h` after adjusting the coercions.
-/
theorem dvd_of_ordR_le {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordR R b ≤ ordR R a) : b ∣ a := by
  unfold ordR at h
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
  rw [← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R a) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha),
    ← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R b) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]
  exact_mod_cast h

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective R (FractionRing R)`. Establish `hp` using `(IsLocalization.surj (nonZeroDivisors R) x).choose_spec`. Unfold `ordK`. Use `set p := (IsLocalization.surj (nonZeroDivisors R) x).choose`. Establish `hp2 : (p.2 : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero _`.

Establish `hne : ∀ {c d : R}, d ≠ 0 → x * algebraMap R _ d = algebraMap R _ c → c ≠ 0`. Introduce and unpack `c d hd hcd rfl`. Rewrite `hcd` using `[map_zero]`. Conclude with `mul_ne_zero hx ((map_ne_zero_iff _ hinj).2 hd) hcd`. Establish `he : p.1 * b = a * p.2` using `hinj (by rw [map_mul, map_mul, ← hp, ← h]; ring)`.

Establish `h2` using `congrArg (ordR R) he`. Rewrite `h2` using `[ordR_mul (hne hp2 hp) hb, ordR_mul (hne hb h) hp2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordK_eq {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R _ b = algebraMap R _ a) : ordK R x = (ordR R a : ℤ) - ordR R b := by
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hp := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  unfold ordK
  set p := (IsLocalization.surj (nonZeroDivisors R) x).choose
  have hp2 : (p.2 : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have hne : ∀ {c d : R}, d ≠ 0 → x * algebraMap R _ d = algebraMap R _ c → c ≠ 0 := by
    rintro c d hd hcd rfl
    rw [map_zero] at hcd
    exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).2 hd) hcd
  have he : p.1 * b = a * p.2 := hinj (by rw [map_mul, map_mul, ← hp, ← h]; ring)
  have h2 := congrArg (ordR R) he
  rw [ordR_mul (hne hp2 hp) hb, ordR_mul (hne hb h) hp2] at h2
  omega

/- English proof (translation)
Rewrite using `[ordK_eq ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha) (a := a) one_ne_zero (by simp), (ordR_eq_zero_iff one_ne_zero).2 isUnit_one]`. Simplify using the standard rewrite rules.
-/
theorem ordK_algebraMap {a : R} (ha : a ≠ 0) : ordK R (algebraMap R (FractionRing R) a) = ordR R a := by
  rw [ordK_eq ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha) (a := a) one_ne_zero
    (by simp), (ordR_eq_zero_iff one_ne_zero).2 isUnit_one]
  simp

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `IsLocalization.surj (nonZeroDivisors R) x`. Establish `hb : (b : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero _`. Use `⟨a, b, ?_, hb, h⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `only [map_zero] at h`.

Conclude with `mul_ne_zero hx ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h`.
-/
theorem exists_frac {x : FractionRing R} (hx : x ≠ 0) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ x * algebraMap R _ b = algebraMap R _ a := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  refine ⟨a, b, ?_, hb, h⟩
  rintro rfl
  simp only [map_zero] at h
  exact mul_ne_zero hx ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h

/- English proof (translation)
Take `⟨a, b, ha, hb, h⟩` from `exists_frac hx`. Take `⟨c, d, hc, hd, h'⟩` from `exists_frac hy`. Rewrite using `[ordK_eq hx hb h, ordK_eq hy hd h', ordK_eq (mul_ne_zero hx hy) (a := a * c) (mul_ne_zero hb hd) (by rw [map_mul, map_mul, ← h, ← h']; ring), ordR_mul ha hc, ordR_mul hb hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordK_mul (x y : FractionRing R) (hx : x ≠ 0) (hy : y ≠ 0) : ordK R (x * y) = ordK R x + ordK R y := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_frac hx
  obtain ⟨c, d, hc, hd, h'⟩ := exists_frac hy
  rw [ordK_eq hx hb h, ordK_eq hy hd h', ordK_eq (mul_ne_zero hx hy) (a := a * c) (mul_ne_zero hb hd)
    (by rw [map_mul, map_mul, ← h, ← h']; ring), ordR_mul ha hc, ordR_mul hb hd]
  push_cast
  ring

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Rewrite using `[ordK_algebraMap (by rintro rfl; simp at hx)]`. Check the signs of the components of the expression.
-/
theorem ordK_nonneg_of_mem {x : FractionRing R} (hx : x ≠ 0)
    (h : x ∈ (algebraMap R (FractionRing R)).range) : 0 ≤ ordK R x := by
  obtain ⟨a, rfl⟩ := h
  rw [ordK_algebraMap (by rintro rfl; simp at hx)]
  positivity

/- English proof (translation)
Take `⟨a, b, ha, hb, h⟩` from `exists_frac hx`. Rewrite `h0` using `[ordK_eq hx hb h]`. Take `⟨c, rfl⟩` from `dvd_of_ordR_le ha hb (by omega)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[map_mul, mul_comm]`.

Conclude with `(mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h).symm`.
-/
theorem mem_of_ordK_nonneg {x : FractionRing R} (hx : x ≠ 0) (h0 : 0 ≤ ordK R x) :
    x ∈ (algebraMap R (FractionRing R)).range := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_frac hx
  rw [ordK_eq hx hb h] at h0
  obtain ⟨c, rfl⟩ := dvd_of_ordR_le ha hb (by omega)
  refine ⟨c, ?_⟩
  rw [map_mul, mul_comm] at h
  exact (mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h).symm

/- English proof (translation)
Unfold `BlochKatoReduction.Gen.vK BlochKatoReduction.Gen.nval ordK ordR`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_eq (l : ℕ) (x : FractionRing R) :
    BlochKatoReduction.Gen.vK R l x = (ordK R x : ℝ) / (ordR R (l : R) : ℝ) := by
  unfold BlochKatoReduction.Gen.vK BlochKatoReduction.Gen.nval ordK ordR
  push_cast
  ring

/- English proof (translation)
Conclude with `Nat.pos_of_ne_zero fun h => hu ((ordR_eq_zero_iff ha).1 h)` after adjusting the coercions.
-/
theorem ordR_pos {a : R} (ha : a ≠ 0) (hu : ¬ IsUnit a) : (0 : ℝ) < ordR R a := by
  exact_mod_cast Nat.pos_of_ne_zero fun h => hu ((ordR_eq_zero_iff ha).1 h)

/- English proof (translation)
Establish `h` using `proportional f (ordK R) (ordK S) ordK_mul ordK_mul (fun y hy h0 => by`. Take `⟨a, rfl⟩` from `mem_of_ordK_nonneg hy h0`. Conclude with `ordK_nonneg_of_mem ((map_ne_zero f).2 hy) ⟨g a, (hfg a).symm⟩) hx`. Use the proof step `((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hR0)`. Rewrite `h` using `[hfg, map_natCast g, ordK_algebraMap hR0, ordK_algebraMap hS0]`.

Rewrite using `[vK_eq, vK_eq, div_eq_div_iff (ordR_pos hS0 hS).ne' (ordR_pos hR0 hR).ne']`. Conclude with `h` after adjusting the coercions.
-/
theorem vK_map {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : FractionRing R →+* FractionRing S) (g : R →+* S)
    (hfg : ∀ a, f (algebraMap R _ a) = algebraMap S _ (g a)) (l : ℕ)
    (hR0 : (l : R) ≠ 0) (hR : ¬ IsUnit (l : R)) (hS0 : (l : S) ≠ 0) (hS : ¬ IsUnit (l : S))
    {x : FractionRing R} (hx : x ≠ 0) : BlochKatoReduction.Gen.vK S l (f x) = BlochKatoReduction.Gen.vK R l x := by
  have h := proportional f (ordK R) (ordK S) ordK_mul ordK_mul (fun y hy h0 => by
      obtain ⟨a, rfl⟩ := mem_of_ordK_nonneg hy h0
      exact ordK_nonneg_of_mem ((map_ne_zero f).2 hy) ⟨g a, (hfg a).symm⟩) hx
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hR0)
  rw [hfg, map_natCast g, ordK_algebraMap hR0, ordK_algebraMap hS0] at h
  rw [vK_eq, vK_eq, div_eq_div_iff (ordR_pos hS0 hS).ne' (ordR_pos hR0 hR).ne']
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[vK_eq, vK_eq, vK_eq, ordK_mul x y hx hy]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_mul (l : ℕ) {x y : FractionRing R} (hx : x ≠ 0) (hy : y ≠ 0) :
    BlochKatoReduction.Gen.vK R l (x * y) = BlochKatoReduction.Gen.vK R l x + BlochKatoReduction.Gen.vK R l y := by
  rw [vK_eq, vK_eq, vK_eq, ordK_mul x y hx hy]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[vK_eq, ordK_algebraMap u.ne_zero, (ordR_eq_zero_iff u.ne_zero).2 u.isUnit]`. Simplify using the standard rewrite rules.
-/
theorem vK_unit (l : ℕ) (u : Rˣ) : BlochKatoReduction.Gen.vK R l (algebraMap R (FractionRing R) (u : R)) = 0 := by
  rw [vK_eq, ordK_algebraMap u.ne_zero, (ordR_eq_zero_iff u.ne_zero).2 u.isUnit]
  simp

end Ord

/- English proof (translation)
Establish `h : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x)` using `GlobalTheory.Idele.valuation_eq_exp_neg_count w hx`. Rewrite using `[vAdd, h, WithZero.log_exp, neg_neg]`.
-/
theorem vw_eq_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Formalism.DivisionValues.vw w x = vAdd w x := by
  have h : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  rw [vAdd, h, WithZero.log_exp, neg_neg]

/- English proof (translation)
Rewrite using `[vw_eq_vAdd w hx, vw_eq_vAdd w hy, vw_eq_vAdd w (mul_ne_zero hx hy), vAdd, vAdd, vAdd, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vw_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0)
    (hy : y ≠ 0) : Formalism.DivisionValues.vw w (x * y) = Formalism.DivisionValues.vw w x + Formalism.DivisionValues.vw w y := by
  rw [vw_eq_vAdd w hx, vw_eq_vAdd w hy, vw_eq_vAdd w (mul_ne_zero hx hy), vAdd, vAdd, vAdd, map_mul,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

/- English proof (translation)
Introduce `D nch w N0 lam a u z hC hid`. Take `⟨hne, -, hle⟩` from `hC lam`. Use `set T := BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a)) with hT`. Unfold `BlochKatoReduction.Gen.c0 twEps at hle`. Use `set S := ∑ δ, D.ntw.th (nch.twI w) ∅ lam δ with hS`.

Establish `hl` using `nch.twI_l w`. Use `set l := D.what₂.places.resChar w with hldef`. Establish `hlp : l.Prime` using `D.what₂.places.resChar_prime w`. Establish `hlL : (l : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.mpr hlp.ne_zero`. Establish `hlE : (l : nch.Oe w) ≠ 0`.

Introduce `h`. Establish `h1` using `congrArg (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))) h`. Rewrite `h1` using `[map_natCast, map_zero, ← map_natCast (nch.embW w)]`. Conclude with `hlL ((map_eq_zero _).1 h1)`. Establish `hlk : (l : D.ntw.Ok (nch.twI w) (nch.k' w)) ≠ 0`.

Introduce `h`. Establish `h1` using `congrArg (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)) h`. Rewrite `h1` using `[map_natCast, map_zero]`. Conclude with `hlE h1`. Establish `hlO : (l : D.ntw.O (nch.twI w)) ≠ 0`.

Introduce `h`. Establish `h1` using `congrArg (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w))) h`. Rewrite `h1` using `[map_natCast, map_zero]`. Conclude with `hlk h1`. Establish `huO : ¬ IsUnit (l : D.ntw.O (nch.twI w))`.

Use `D.ntw.O_l (nch.twI w)` as an intermediate fact. Rewrite `this` using `[hl]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this`. Establish `huk : ¬ IsUnit (l : D.ntw.Ok (nch.twI w) (nch.k' w))` using `by haveI := D.ntw.Ok_fin (nch.twI w) (nch.k' w) haveI : FaithfulSMul (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)) := (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj _ _)`. Introduce `h`.

Rewrite `h` using `[← map_natCast (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)))]`. Conclude with `huO (IsUnit.of_map _ _ h)`. Establish `huE : ¬ IsUnit (l : nch.Oe w)` using `by haveI := nch.Oe_loc w`. Introduce `h`. Rewrite `h` using `[← map_natCast (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w))]`.

Conclude with `huk (IsUnit.of_map _ _ h)`. Establish `hu0 : algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero`. Establish `hT0 : nch.kMapE w T ≠ 0` using `(map_ne_zero _).2 hne`. Establish `hprod` using `mul_ne_zero hu0 hT0`. Rewrite `hprod` using `[← hid]`.

Establish `hz0 : z ≠ 0` using `(map_ne_zero _).1 (left_ne_zero_of_mul hprod)`. Establish `hS1 : BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S ≠ 0` using `(map_ne_zero _).1 (right_ne_zero_of_mul hprod)`. Establish `hS0 : S ≠ 0` using `(map_ne_zero _).1 hS1`. Establish `hE : ∀ {x}, x ≠ 0 → BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.kMapE w x) = BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l x` using `fun hx => vK_map (nch.kMapE w) (algebraMap _ _) (fun b => by`. Unfold `NChoice.kMapE IsFractionRing.map`.

Conclude with `IsLocalization.map_eq _ b) l hlk huk hlE huE hx`. Establish `hk : BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S) = BlochKatoReduction.Gen.vK (D.ntw.O (nch.twI w)) l S` using `vK_map _ (algebraMap _ _) (fun b => IsFractionRing.lift_algebraMap _ b) l hlO huO hlk huk hS0`. Establish `hv` using `congrArg (BlochKatoReduction.Gen.vK (nch.Oe w) l) hid`. Rewrite `hv` using `[vK_mul l (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod), vK_mul l hu0 hT0, vK_unit, hE hS1, hE hne, hk]`. Rewrite `hle` using `[hl]`.

Establish `hz : BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) ≤ ((l : ℝ) ^ 2)⁻¹` using `by linarith`. Establish `hp` using `proportional (nch.embW w) (Formalism.DivisionValues.vw (D.plEq w)) (ordK (nch.Oe w)) (vw_mul _) ordK_mul (fun y hy h0 => ordK_nonneg_of_mem ((map_ne_zero _).2 hy) ((nch.embW_w w y).1 (by`. Rewrite using `[D.val_eq w y hy, ← vw_eq_vAdd _ hy]`. Conclude with `h0))) hz0 hlL` after adjusting the coercions. Rewrite `hp` using `[map_natCast, ← map_natCast (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))), ordK_algebraMap hlE]`.

Establish `hvl : 0 ≤ Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL)`. Establish `h` using `D.what₂.places.val_resChar w`. Rewrite `h` using `[D.val_eq w _ hlL, ← vw_eq_vAdd _ hlL]`. Establish `h1 : Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ)` using `WithTop.coe_injective h`. Rewrite using `[h1]`.

Check the signs of the components of the expression. Establish `hpos` using `ordR_pos hlE huE`. Establish `hp' : (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) = BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) * (Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) : ℝ)`. Rewrite using `[vK_eq, div_mul_eq_mul_div, eq_div_iff hpos.ne']`. Conclude with `hp.symm` after adjusting the coercions.

Rewrite using `[hp', div_eq_inv_mul]`. Conclude with `mul_le_mul_of_nonneg_right hz (by exact_mod_cast hvl)`.
-/
theorem vw_le_of_bound : ∀ {D : D7} (nch : NChoice D) (w : D.what₂.places.Pl) (N0 : D.ntw.Tw → ℕ) (lam : D.ntw.abelian₂ (nch.twI w)) (a : ℤ)
    (u : (nch.Oe w)ˣ) (z : D.what₂.LL),
    BlochKatoReduction.Gen.partC N0 (nch.twI w) (nch.Q w) (nch.k' w) (nch.psi' w ^ a) (twEps D (nch.twI w)) →
    nch.embW w z * nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) (∑ δ, D.ntw.th (nch.twI w) ∅ lam δ)) =
      algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) *
        nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
          (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a))) →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  intro D nch w N0 lam a u z hC hid
  obtain ⟨hne, -, hle⟩ := hC lam
  set T := BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
    (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a)) with hT
  unfold BlochKatoReduction.Gen.c0 twEps at hle
  set S := ∑ δ, D.ntw.th (nch.twI w) ∅ lam δ with hS
  have hl := nch.twI_l w
  set l := D.what₂.places.resChar w with hldef
  have hlp : l.Prime := D.what₂.places.resChar_prime w
  have hlL : (l : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hlp.ne_zero
  have hlE : (l : nch.Oe w) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))) h
    rw [map_natCast, map_zero, ← map_natCast (nch.embW w)] at h1
    exact hlL ((map_eq_zero _).1 h1)
  have hlk : (l : D.ntw.Ok (nch.twI w) (nch.k' w)) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)) h
    rw [map_natCast, map_zero] at h1
    exact hlE h1
  have hlO : (l : D.ntw.O (nch.twI w)) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w))) h
    rw [map_natCast, map_zero] at h1
    exact hlk h1
  have huO : ¬ IsUnit (l : D.ntw.O (nch.twI w)) := by
    have := D.ntw.O_l (nch.twI w)
    rw [hl] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have huk : ¬ IsUnit (l : D.ntw.Ok (nch.twI w) (nch.k' w)) := by
    haveI := D.ntw.Ok_fin (nch.twI w) (nch.k' w)
    haveI : FaithfulSMul (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj _ _)
    intro h
    rw [← map_natCast (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)))] at h
    exact huO (IsUnit.of_map _ _ h)
  have huE : ¬ IsUnit (l : nch.Oe w) := by
    haveI := nch.Oe_loc w
    intro h
    rw [← map_natCast (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w))] at h
    exact huk (IsUnit.of_map _ _ h)
  have hu0 : algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero
  have hT0 : nch.kMapE w T ≠ 0 := (map_ne_zero _).2 hne
  have hprod := mul_ne_zero hu0 hT0
  rw [← hid] at hprod
  have hz0 : z ≠ 0 := (map_ne_zero _).1 (left_ne_zero_of_mul hprod)
  have hS1 : BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S ≠ 0 := (map_ne_zero _).1 (right_ne_zero_of_mul hprod)
  have hS0 : S ≠ 0 := (map_ne_zero _).1 hS1
  have hE : ∀ {x}, x ≠ 0 → BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.kMapE w x) =
      BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l x := fun hx =>
    vK_map (nch.kMapE w) (algebraMap _ _) (fun b => by
      unfold NChoice.kMapE IsFractionRing.map
      exact IsLocalization.map_eq _ b) l hlk huk hlE huE hx
  have hk : BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S) =
      BlochKatoReduction.Gen.vK (D.ntw.O (nch.twI w)) l S :=
    vK_map _ (algebraMap _ _) (fun b => IsFractionRing.lift_algebraMap _ b) l hlO huO hlk huk hS0
  have hv := congrArg (BlochKatoReduction.Gen.vK (nch.Oe w) l) hid
  rw [vK_mul l (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod), vK_mul l hu0 hT0, vK_unit,
    hE hS1, hE hne, hk] at hv
  rw [hl] at hle
  have hz : BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) ≤ ((l : ℝ) ^ 2)⁻¹ := by linarith
  have hp := proportional (nch.embW w) (Formalism.DivisionValues.vw (D.plEq w)) (ordK (nch.Oe w)) (vw_mul _) ordK_mul
    (fun y hy h0 => ordK_nonneg_of_mem ((map_ne_zero _).2 hy) ((nch.embW_w w y).1 (by
      rw [D.val_eq w y hy, ← vw_eq_vAdd _ hy]
      exact_mod_cast h0))) hz0 hlL
  rw [map_natCast, ← map_natCast (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))), ordK_algebraMap hlE] at hp
  have hvl : 0 ≤ Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) := by
    have h := D.what₂.places.val_resChar w
    rw [D.val_eq w _ hlL, ← vw_eq_vAdd _ hlL] at h
    have h1 : Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := WithTop.coe_injective h
    rw [h1]
    positivity
  have hpos := ordR_pos hlE huE
  have hp' : (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) =
      BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) * (Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) : ℝ) := by
    rw [vK_eq, div_mul_eq_mul_div, eq_div_iff hpos.ne']
    exact_mod_cast hp.symm
  rw [hp', div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hz (by exact_mod_cast hvl)

end GlobalTheory.TwistValBound

end
