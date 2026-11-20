import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPowStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilLaws

/- English proof (translation)
Use `exists_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, ← hu]`. Establish `h : u ^ a * u ^ (-a).toNat = u ^ a.toNat`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `h' : ((u ^ a : Kˣ) : K) * (u : K) ^ (-a).toNat = (u : K) ^ a.toNat`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h]`. Rewrite using `[← h', mul_right_comm]`. Conclude with `(u.isUnit.pow _).mul_left_inj`.
-/
theorem toNat_iff_zpow {R K : Type} [CommRing R] [CommRing K] (ι : R →+* K) (ξ : R) (u : Kˣ)
    (hu : (u : K) = ι ξ) (a : ℤ) (x : K) :
    (∃ y : R, x * ι ξ ^ (-a).toNat = ι (ξ ^ a.toNat * y)) ↔ ∃ y : R, x = ((u ^ a : Kˣ) : K) * ι y := by
  refine exists_congr fun y => ?_
  rw [map_mul, map_pow, ← hu]
  have h : u ^ a * u ^ (-a).toNat = u ^ a.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
    congr 1
    omega
  have h' : ((u ^ a : Kˣ) : K) * (u : K) ^ (-a).toNat = (u : K) ^ a.toNat := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h]
  rw [← h', mul_right_comm]
  exact (u.isUnit.pow _).mul_left_inj

/- English proof (translation)
Take `⟨ζ, ε, h0, -, h1, hr⟩` from `GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l`. Use `⟨ε, ?_, ?_⟩` and prove the remaining obligations. Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `Subtype.ext this`.

Introduce `h`. Use `hr 1` as an intermediate fact. Establish `e : rootT ε 1 = 1` using `h`. Rewrite `this` using `[e]`. Apply `h1` to reduce the goal to its premises.

Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← this, map_one]`. Both sides reduce to the same expression.
-/
theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.sigDp_alg l g x`.
-/
theorem σDp_alg (g : Per.Gq l) (x : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) x) :=
  GlobalTheory.RingIface.sigDp_alg l g x

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.sigD_alg l g y`.
-/
theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

/- English proof (translation)
Take `⟨e, he⟩` from `exists_isEps l`. Take `⟨hP, -, -, -⟩` from `GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he`. Establish `hk` using `GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he`. Establish `h1 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ∈ Per.kerP l`. Rewrite using `[hk]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `h2 : Per.extP (Per.σA g) (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) ∈ Per.kerP l` using `Ideal.mem_comap.1 (GlobalTheory.RingBasics.ker_σ g h1)`. Rewrite `h2` using `[hk, Ideal.mem_span_singleton]`. Establish `h3 : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e))`. Unfold `aDp`.

Rewrite using `[RingHom.comp_apply, σDp_alg]`. Conclude with `map_dvd _ h2`. Take `⟨z, rfl⟩` from `(hP n y).1 hy`. Rewrite using `[hP, map_mul, map_pow]`. Conclude with `(pow_dvd_pow_of_dvd h3 n).mul_right _`.
-/
theorem σDp_mem_FilP (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l) (hy : y ∈ Per.FilP l n) :
    Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  have h1 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ∈ Per.kerP l := by
    rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : Per.extP (Per.σA g) (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) ∈ Per.kerP l :=
    Ideal.mem_comap.1 (GlobalTheory.RingBasics.ker_σ g h1)
  rw [hk, Ideal.mem_span_singleton] at h2
  have h3 : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply, σDp_alg]
    exact map_dvd _ h2
  obtain ⟨z, rfl⟩ := (hP n y).1 hy
  rw [hP, map_mul, map_pow]
  exact (pow_dvd_pow_of_dvd h3 n).mul_right _

/- English proof (translation)
Take `⟨hP, hreg, -, -⟩` from `GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he`. Establish `hξ : aDp l (xi e) ∈ Per.FilP l 1` using `(hP 1 _).2 (by rw [pow_one])`. Establish `hd : ∀ g : Per.Gq l, aDp l (xi e) ∣ Per.σDp g (aDp l (xi e))` using `fun g => by`. Use `(hP 1 _).1 (σDp_mem_FilP g 1 _ hξ)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.

Take `⟨c, hc⟩` from `hd g`. Take `⟨c', hc'⟩` from `hd g⁻¹`. Establish `hinv : Per.σDp g (Per.σDp g⁻¹ (aDp l (xi e))) = aDp l (xi e)`. Express the relevant statement in the definitionally equal form `Per.σDp g (Per.σDp g⁻¹ (algebraMap (Per.AinfP l) (Per.BdRp l) _)) = algebraMap (Per.AinfP l) (Per.BdRp l) _`. Rewrite using `[σDp_alg, σDp_alg, GlobalTheory.RingBasics.extP_inv]`.

Use `⟨c, Per.σDp g c', hc, ?_⟩` and prove the remaining obligations. Rewrite `hinv` using `[hc', map_mul, hc]`. Use `hreg (c * Per.σDp g c' - 1) (by rw [mul_sub, mul_one, ← mul_assoc, hinv, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem σDp_xi (e : Per.Fl l) (he : IsEps e) (g : Per.Gq l) :
    ∃ c d : Per.BdRp l, Per.σDp g (aDp l (xi e)) = aDp l (xi e) * c ∧ c * d = 1 := by
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have hd : ∀ g : Per.Gq l, aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := fun g => by
    have := (hP 1 _).1 (σDp_mem_FilP g 1 _ hξ)
    rwa [pow_one] at this
  obtain ⟨c, hc⟩ := hd g
  obtain ⟨c', hc'⟩ := hd g⁻¹
  have hinv : Per.σDp g (Per.σDp g⁻¹ (aDp l (xi e))) = aDp l (xi e) := by
    change Per.σDp g (Per.σDp g⁻¹ (algebraMap (Per.AinfP l) (Per.BdRp l) _)) =
      algebraMap (Per.AinfP l) (Per.BdRp l) _
    rw [σDp_alg, σDp_alg, GlobalTheory.RingBasics.extP_inv]
  refine ⟨c, Per.σDp g c', hc, ?_⟩
  rw [hc', map_mul, hc] at hinv
  have := hreg (c * Per.σDp g c' - 1) (by rw [mul_sub, mul_one, ← mul_assoc, hinv, sub_self])
  exact sub_eq_zero.1 this

/- English proof (translation)
Take `⟨e, he⟩` from `exists_isEps l`. Take `⟨hP, -, hc, -⟩` from `GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he`. Use `hc.toIsHausdorff.haus y fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `(hP n y).1 (hy n)`.
-/
theorem eq_zero_of_forall_mem_FilP (y : Per.BdRp l) (hy : ∀ n, y ∈ Per.FilP l n) : y = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, hc, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  refine hc.toIsHausdorff.haus y fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (hP n y).1 (hy n)

end GlobalTheory.MemLoc.FilLaws

open GlobalTheory.MemLoc.FilLaws in

/- English proof (translation)
Introduce `l _`. Take `⟨e, he⟩` from `exists_isEps l`. Take `⟨hdom, hinj, hfield, hden⟩` from `GlobalTheory.T.bdRPlus_isDomain_bdR_isField l`. Take `⟨hP, hreg, -, -⟩` from `GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he`. Establish `hD` using `GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he`.

Establish `hden` using `hden e he`. Establish `hσ` using `σDp_xi e he`. Generalize the expression as in `aDp l (xi e) = ξ at hP hreg hD hden hσ`. Establish `hne : algebraMap (Per.BdRp l) (Per.BdR l) ξ ≠ 0`. Introduce `h`.

Establish `h0 : ξ = 0` using `hinj (by rw [h, map_zero])`. Conclude with `one_ne_zero (hreg 1 (by rw [h0, zero_mul]))`. Take `⟨v, hv⟩` from `hfield.mul_inv_cancel hne`. Take `⟨u, hu⟩ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) ξ)` from `IsUnit.of_mul_eq_one v hv`. Establish `hZ : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) y` using `fun a x => (hD a x).trans (toNat_iff_zpow _ ξ u hu a x)`.

Establish `hlast : ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n`. Introduce `n y`. Rewrite using `[hZ, hP, zpow_natCast, Units.val_pow_eq_pow_val, hu]`. Use `exists_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul]`.

Conclude with `hinj.eq_iff`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, hlast⟩` and prove the remaining obligations. Introduce `a x hx`. Take `⟨y, hy⟩` from `(hZ _ _).1 hx`. Use `(hZ _ _).2 ⟨ξ * y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hy, zpow_add_one, Units.val_mul, hu, map_mul, mul_assoc]`. Conclude with `(hZ _ _).2 ⟨1, by rw [zpow_zero, Units.val_one, map_one, mul_one]⟩`. Introduce `a b x y hx hy`. Take `⟨x', rfl⟩` from `(hZ _ _).1 hx`. Take `⟨y', rfl⟩` from `(hZ _ _).1 hy`.

Use `(hZ _ _).2 ⟨x' * y', ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_add, Units.val_mul, map_mul, mul_mul_mul_comm]`. Introduce `x`. Take `⟨n, y, hy⟩` from `hden x`. Use `⟨-(n : ℤ), (hD _ _).2 ⟨y, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, hy]`. Introduce `x hx`. Take `⟨y, hy⟩` from `(hZ _ _).1 (hx 0)`. Rewrite `hy` using `[zpow_zero, Units.val_one, one_mul]`. Substitute `hy` using the available equality.

Rewrite using `[eq_zero_of_forall_mem_FilP y fun n => (hlast n y).1 (hx n), map_zero]`. Introduce `g a x hx`. Take `⟨c, d, hc, hcd⟩` from `hσ g`. Take `⟨y, hy⟩` from `(hD _ _).1 hx`. Establish `h1` using `congrArg (Per.σD g) hy`.

Rewrite `h1` using `[map_mul, map_pow, σD_alg, σD_alg, map_mul (Per.σDp g), map_pow, hc]`. Use `(hD _ _).2 ⟨d ^ (-a).toNat * (c ^ a.toNat * Per.σDp g y), ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap (Per.BdRp l) (Per.BdR l) ξ = algebraMap (Per.BdRp l) (Per.BdR l) (ξ * c) * algebraMap (Per.BdRp l) (Per.BdR l) d`. Rewrite using `[← map_mul, mul_assoc, hcd, mul_one]`. Rewrite using `[h2, mul_pow, ← mul_assoc, h1, ← map_pow, ← map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.MemLoc.filD_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hdom, hinj, hfield, hden⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hD := GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he
  have hden := hden e he
  have hσ := σDp_xi e he
  generalize aDp l (xi e) = ξ at hP hreg hD hden hσ
  have hne : algebraMap (Per.BdRp l) (Per.BdR l) ξ ≠ 0 := by
    intro h
    have h0 : ξ = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero (hreg 1 (by rw [h0, zero_mul]))
  obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) ξ) := IsUnit.of_mul_eq_one v hv
  have hZ : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔
      ∃ y, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun a x => (hD a x).trans (toNat_iff_zpow _ ξ u hu a x)
  have hlast : ∀ (n : ℕ) (y : Per.BdRp l),
      algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
    intro n y
    rw [hZ, hP, zpow_natCast, Units.val_pow_eq_pow_val, hu]
    refine exists_congr fun z => ?_
    rw [← map_pow, ← map_mul]
    exact hinj.eq_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlast⟩
  · intro a x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 hx
    refine (hZ _ _).2 ⟨ξ * y, ?_⟩
    rw [hy, zpow_add_one, Units.val_mul, hu, map_mul, mul_assoc]
  · exact (hZ _ _).2 ⟨1, by rw [zpow_zero, Units.val_one, map_one, mul_one]⟩
  · intro a b x y hx hy
    obtain ⟨x', rfl⟩ := (hZ _ _).1 hx
    obtain ⟨y', rfl⟩ := (hZ _ _).1 hy
    refine (hZ _ _).2 ⟨x' * y', ?_⟩
    rw [zpow_add, Units.val_mul, map_mul, mul_mul_mul_comm]
  · intro x
    obtain ⟨n, y, hy⟩ := hden x
    refine ⟨-(n : ℤ), (hD _ _).2 ⟨y, ?_⟩⟩
    rw [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, hy]
  · intro x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 (hx 0)
    rw [zpow_zero, Units.val_one, one_mul] at hy
    subst hy
    rw [eq_zero_of_forall_mem_FilP y fun n => (hlast n y).1 (hx n), map_zero]
  · intro g a x hx
    obtain ⟨c, d, hc, hcd⟩ := hσ g
    obtain ⟨y, hy⟩ := (hD _ _).1 hx
    have h1 := congrArg (Per.σD g) hy
    rw [map_mul, map_pow, σD_alg, σD_alg, map_mul (Per.σDp g), map_pow, hc] at h1
    refine (hD _ _).2 ⟨d ^ (-a).toNat * (c ^ a.toNat * Per.σDp g y), ?_⟩
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) ξ =
        algebraMap (Per.BdRp l) (Per.BdR l) (ξ * c) * algebraMap (Per.BdRp l) (Per.BdR l) d := by
      rw [← map_mul, mul_assoc, hcd, mul_one]
    rw [h2, mul_pow, ← mul_assoc, h1, ← map_pow, ← map_mul]
    congr 1
    ring
