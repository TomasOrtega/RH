import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.SecGlueInt

open GlobalTheory.Reg.ChartCompat (comp_eq away_lift away_inj)
open GlobalTheory.Reg.SecGlue (chart_comp eq_of_fields)

def zchar {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t : J → Sˣ) : S := ((∏ i, t i ^ e i : Sˣ) : S)

/- English proof (translation)
Simplify using `only [zchar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]`.
-/
theorem zchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t t' : J → Sˣ) :
    zchar e (t * t') = zchar e t * zchar e t' := by
  simp only [zchar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]

/- English proof (translation)
Simplify using `[zchar]`.
-/
theorem zchar_one {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) : zchar e (1 : J → Sˣ) = 1 := by
  simp [zchar]

/- English proof (translation)
Establish `: (∏ i, Units.map (φ : S →* T) (t i) ^ e i) = Units.map (φ : S →* T) (∏ i, t i ^ e i)`. Simplify using `only [map_prod, map_zpow]`. Unfold `zchar`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem zchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℤ) (t : J → Sˣ) :
    zchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (zchar e t) := by
  have : (∏ i, Units.map (φ : S →* T) (t i) ^ e i) = Units.map (φ : S →* T) (∏ i, t i ^ e i) := by
    simp only [map_prod, map_zpow]
  unfold zchar
  rw [this]
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor`. Establish `G` using `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c`. Establish `U` using `GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c`. Take `⟨g, hg, hopn⟩` from `C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩`. Establish `hg0 : g ≠ 0` using `fun e => hg (by rw [e, map_zero])`.

Establish `hg1 : C.R.val g ≠ 0` using `fun e => hg0 (Subtype.ext e)`. Establish `hZ : C.Z = C'.Z`. Take `⟨ψ0, z0, t0, h1, h2⟩` from `hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen`. Conclude with `comp_eq C C' ψ0 z0 t0 h1 h2`. Use `⟨hZ, ?_⟩` and prove the remaining obligations.

Take `⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩` from `C`. Take `⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩` from `C'`. Simplify using `only at *`. Substitute `hZ` using the available equality. Introduce `e b hb hb'`.

Set `S` to `Localization.Away g`. Set `lam : R →ₐ[c.F] S` to `IsScalarTower.toAlgHom c.F R S`. Establish `hlam : IsUnit (lam g)` using `IsLocalization.Away.algebraMap_isUnit g`. Take `⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val` from `away_lift g R.val hg1`. Take `⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ` from `away_lift g ψ hg`.

Establish `hinj : Function.Injective mu` using `away_inj g mu (by rw [hmu]; exact Subtype.val_injective)`. Take `⟨w, hw⟩` from `hev.bc R S lam y`. Take `⟨φ, v, s, hv, hs⟩` from `hopn S lam hlam w hw`. Take `⟨vmu, hvmu⟩` from `hev.bc S (Om Z) mu v`. Establish `m1 : FrMap mu w yg` using `frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)`.

Establish `b1` using `frBorBC _ _ mu s v w vmu yg hs hvmu m1`. Establish `m2 : FrMap (mu.comp φ) y' vmu` using `frMap_trans _ _ _ φ mu y' v vmu hv hvmu`. Establish `b2` using `(G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')`. Establish `e1 : mu.comp φ = R'.val` using `mono' _ _ _ _ _ _ m2 gen' b2`. Establish `e2 : vmu = yg'` using `(U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'`.

Substitute `e2` using the available equality. Establish `e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i)` using `(G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)`. Take `⟨vnu, hvnu⟩` from `hev.bc S L nu v`. Establish `m3 : FrMap nu w z` using `frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)`. Establish `b3` using `frBorBC _ _ nu s v w vnu z hs hvnu m3`.

Establish `m4 : FrMap (nu.comp φ) y' vnu` using `frMap_trans _ _ _ φ nu y' v vnu hv hvnu`. Establish `b4` using `(G _).2.1 _ _ _ _ _ b3 hbor`. Establish `e4 : nu.comp φ = ψ'` using `mono' _ _ _ _ _ _ m4 hz' b4`. Establish `e5 : vnu = z'` using `(U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'`. Substitute `e5` using the available equality.

Establish `e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1` using `(G _).2.2.2 _ _ _ _ b4 ((G _).1 _)`. Establish `e7 : lam ⟨_, hb⟩ = zchar e s * φ ⟨_, hb'⟩`. Apply `hinj` to reduce the goal to its premises. Establish `a1 : mu (lam ⟨_, hb⟩) = zchar e tC * b Z` using `DFunLike.congr_fun hmu ⟨_, hb⟩`. Establish `a2 : mu (φ ⟨_, hb'⟩) = zchar e tC' * b Z` using `DFunLike.congr_fun e1 ⟨_, hb'⟩`.

Establish `a0 : zchar e tC = zchar e tC' * mu (zchar e s)` using `(congrArg (zchar e) e3).trans ((zchar_mul _ _ _).trans (congrArg _ (zchar_map mu e s)))`. Rewrite using `[map_mul, a1, a2]`. Take the linear combination `(b Z) * a0`. Establish `a3 : ψ ⟨_, hb⟩ = nu (zchar e s) * ψ' ⟨_, hb'⟩`. Rewrite using `[← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]`.

Establish `a4 : nu (zchar e s) * zchar e t = 1`. Rewrite using `[← zchar_map, ← zchar_mul, e6, zchar_one]`. Take the linear combination `(-(zchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4`.
-/
theorem chart_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z) (hb : zchar e C.t * b C.Z ∈ C.R) (hb' : zchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = zchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = zchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = zchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = zchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : zchar e tC = zchar e tC' * mu (zchar e s) :=
      (congrArg (zchar e) e3).trans ((zchar_mul _ _ _).trans (congrArg _ (zchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (zchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (zchar e s) * zchar e t = 1 := by
    rw [← zchar_map, ← zchar_mul, e6, zchar_one]
  linear_combination (-(zchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℤ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, zchar e C.t * b C.Z ∈ C.R)

def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = zchar e t * ψ ⟨_, hb C⟩

/- English proof (translation)
Take `⟨C, ψ, z, t, hz, ht, rfl⟩` from `h1`. Take `⟨C', ψ', z', t', hz', ht', rfl⟩` from `h2`. Take `⟨-, hmul, hinv, -⟩` from `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L`. Use `(chart_compat E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz' (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')` as an intermediate fact. Rewrite using `[this, ← mul_assoc, ← zchar_mul, mul_comm t, mul_inv_cancel_left]`.
-/
theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (chart_compat E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← zchar_mul, mul_comm t, mul_inv_cancel_left]

/- English proof (translation)
Take `⟨C, ψ, z, t, hz, ht, rfl⟩` from `h1`. Take `⟨z', hz'⟩` from `hl.bc S T φ z`. Use `⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩` and prove the remaining obligations. Rewrite using `[zchar_map, map_mul]`. Both sides reduce to the same expression.
-/
theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [zchar_map, map_mul]; rfl

/- English proof (translation)
Take `⟨C, ψ, z, t₀, hz, ht, rfl⟩` from `h1`. Use `⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩` and prove the remaining obligations. Rewrite using `[zchar_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (zchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [zchar_mul]; ring

/- English proof (translation)
Take `⟨C, ψ, z, t, h1, h2⟩` from `hA L y`. Conclude with `⟨_, C, ψ, z, t, h1, h2, rfl⟩`.
-/
theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

/- English proof (translation)
Take `⟨C, ψ, z, t, h1, h2⟩` from `hA _ (genFr h Z)`. Take `rfl` from `chart_comp Z C ψ z t h1 h2`. Use `⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩` and prove the remaining obligations. Use `show b C.Z = zchar e C.t⁻¹ * (zchar e C.t * b C.Z)`. Rewrite using `[← mul_assoc, ← zchar_mul, inv_mul_cancel, zchar_one, one_mul]`.
-/
theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = zchar e C.t⁻¹ * (zchar e C.t * b C.Z)
  rw [← mul_assoc, ← zchar_mul, inv_mul_cancel, zchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

/- English proof (translation)
Set `I : Ideal S` to `{ carrier := {g | ∃ s, Rep hb y g s} zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩ add_mem' := by`. Introduce and unpack `g g' ⟨s, hs⟩ ⟨s', hs'⟩`. Conclude with `⟨s + s', fun L _ _ χ w v h1 h2 => by`. Rewrite using `[map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r g ⟨s, hs⟩`. Conclude with `⟨r * s, fun L _ _ χ w v h1 h2 => by`. Rewrite using `[smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }`. Assume the negation of the conclusion as `hne`. Establish `hI : I ≠ ⊤` using `fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)`.

Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hI`. Use `hP.isPrime` as an intermediate fact. Set `χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P)` to `(IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)`. Take `⟨w₀, hw₀⟩` from `hl.bc _ _ χ₀ y`. Take `⟨C, ψ₀, z₀, t₀, h1, h2⟩` from `hA _ w₀`.

Take `⟨g, hg, hloc⟩` from `C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩`. Set `lam : S →ₐ[c.F] Localization.Away g` to `IsScalarTower.toAlgHom c.F S _`. Establish `hu : IsUnit (lam g)` using `IsLocalization.Away.algebraMap_isUnit g`. Take `⟨w', hw'⟩` from `hl.bc _ _ lam y`. Take `⟨ψ, z, t, h3, h4⟩` from `hloc _ lam hu w' hw'`.

Establish `hv : Val hb w' (zchar e t * ψ ⟨_, hb C⟩)` using `⟨C, ψ, z, t, h3, h4, rfl⟩`. Generalize the expression as in `zchar e t * ψ ⟨_, hb C⟩ = u at hv`. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g u`. Establish `hmem : g ^ (n + 1) ∈ I`. Use `⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hχ : χ g = 0`. Simplify using `[hχ]`. Set `mu : Localization.Away g →ₐ[c.F] L` to `IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by`. Introduce and unpack `⟨_, k, rfl⟩`. Simplify using `using (IsUnit.mk0 _ hχ).pow k)`.

Establish `hmu' : ∀ x, mu (algebraMap S _ x) = χ x` using `fun x => by`. Simplify using `[mu]`. Establish `hmu : mu.comp lam = χ` using `AlgHom.ext hmu'`. Establish `h7 : FrMap mu w' w` using `frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)`. Establish `h8` using `val_unique hb hl h6 (val_map hb hl mu h7 hv)`.

Establish `h9` using `congrArg mu ha`. Rewrite `h9` using `[map_mul, map_pow, hmu', hmu']`. Rewrite using `[h8, map_mul, map_pow, ← h9]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgP : g ∈ P` using `this.mem_of_pow_mem _ (hIP hmem)`.

Apply `hg` to reduce the goal to its premises. Use `show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]`.
-/
theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (zchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize zchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hl h hA a b hb`. Establish `hred : ∀ p : TRing c.F, IsReduced p.R` using `fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`. Use `choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y`. Establish `hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L) (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v`. Introduce `p y L _ _ χ w v h1 h2`.

Rewrite using `[← hg p y L χ w v h1 h2, map_one, one_mul]`. Use `⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩` and prove the remaining obligations. Use `hred q` as an intermediate fact. Use `eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `hl.bc _ _ χ z`.

Take `⟨v, hv⟩` from `val_ex hb hA w`. Rewrite using `[hg' q z L χ w v hw hv]`. Conclude with `(hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm`. Use `hred p show g p y' = zchar a t * g p y` as an intermediate fact. Use `eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_` and prove the remaining obligations.

Take `⟨w, hw⟩` from `hl.bc _ _ χ y`. Take `⟨w', hw'⟩` from `hl.bc _ _ χ y'`. Take `⟨v, hv⟩` from `val_ex hb hA w`. Establish `hv'` using `val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv`. Rewrite using `[hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, zchar_map]`.

Establish `hh` using `hl.test _ (genFr h Z)`. Unfold `evC evR evalAt`. Rewrite using `[dif_pos hh]`. Conclude with `hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)`.
-/
theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, zchar a C.t * b C.Z ∈ C.R) → ∃ g ∈ GlobalTheory.AllWt.secZ Xo c a, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    show g p y' = zchar a t * g p y
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, zchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dif_pos hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c h w b hb`. Take `⟨hL, -, -, hA⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c`. Conclude with `exists_sec_of_regular E H Dw l Xo c hL h (hA h) w b hb`.
-/
theorem exists_secZ_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  intro E _ _ _ H Dw l Xo c h w b hb
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact exists_sec_of_regular E H Dw l Xo c hL h (hA h) w b hb

end GlobalTheory.SecGlueInt
