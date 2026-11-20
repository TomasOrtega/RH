import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntCoefExt

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[nval_zero, vV]`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Rewrite using `[nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]`.

Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem nval_nonneg_iff {e : ℕ} (he : 0 < e) (x : K') : 0 ≤ nval V e x ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [nval_zero, vV]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Establish `hN : Ideal.absNorm la.asIdeal ≠ 0` using `fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Use `⟨Ideal.absNorm la.asIdeal, hN, ?_⟩` and prove the remaining obligations. Establish `h1` using `ho.2 (Ideal.absNorm la.asIdeal : K)`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[h1]`.

Use `mul_pos (by exact_mod_cast ho.1) ?_` and prove the remaining obligations. Establish `h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1`. Use `(la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)` as an intermediate fact. Simplify using `using this`. Establish `h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0`.

Simplify using `using hN`. Rewrite `h2` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Simplify using `only [vLa]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_nat_pos {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {ι : K →+* K'} {e : ℕ}
    (ho : OverLa la V ι e) : ∃ N : ℕ, N ≠ 0 ∧ 0 < vV V (N : K') := by
  have hN : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm la.asIdeal, hN, ?_⟩
  have h1 := ho.2 (Ideal.absNorm la.asIdeal : K)
  rw [map_natCast] at h1
  rw [h1]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)
    simpa using this
  have h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0 := by
    simpa using hN
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
  simp only [vLa]
  omega

/- English proof (translation)
Set `u` to `(valV V (K' := K')).comap ι`. Take `⟨Q, hQ, hQm⟩` from `GlobalTheory.CommonValuation.exists_centre u`. Establish `hN' : (N : K') ≠ 0`. Rewrite using `[← map_natCast ι]`. Conclude with `(map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)`.

Establish `hNQ : (N : 𝓞 K) ∈ Q`. Rewrite using `[hQm, map_natCast]`. Use `show valV V (ι N) < 1`. Rewrite using `[map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Simplify using `only [vV] at h`.

Use linear arithmetic over natural numbers and integers. Establish `h0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))`. Set `la : HeightOneSpectrum (𝓞 K)` to `⟨Q, hQ, h0⟩`.

Take `⟨e, he, hv⟩` from `GlobalTheory.CommonValuation.exists_eq_pow la u (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)`. Use `⟨la, e, he, fun a => ?_⟩` and prove the remaining obligations. Use `hv a` as an intermediate fact. Rewrite `this` using `[Valuation.comap_apply]`. Simplify using `only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_overLa {K : Type} [Field K] [NumberField K] (ι : K →+* K') {N : ℕ} (hN : N ≠ 0)
    (h : 0 < vV V (N : K')) : ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V ι e := by
  let u := (valV V (K' := K')).comap ι
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.CommonValuation.exists_centre u
  have hN' : (N : K') ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)
  have hNQ : (N : 𝓞 K) ∈ Q := by
    rw [hQm, map_natCast]
    show valV V (ι N) < 1
    rw [map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]
    simp only [vV] at h
    omega
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))
  let la : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, h0⟩
  obtain ⟨e, he, hv⟩ := GlobalTheory.CommonValuation.exists_eq_pow la u
    (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)
  refine ⟨la, e, he, fun a => ?_⟩
  have := hv a
  rw [Valuation.comap_apply] at this
  simp only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

/- English proof (translation)
Establish `e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v` using `fun G τ v => by`. Unfold `IsEigV`. Simplify using `only [← embK_incF hle τ, h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩`.

Conclude with `⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩`. Introduce and unpack `⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩`. Conclude with `⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩`.
-/
theorem integral_res_iff (T : CDVR) (io' : c'.F →+* T.Fr) (io : c.F →+* T.Fr)
    (h : ∀ a, io' (incF c c' hle a) = io a) (y : letI := io'.toAlgebra; FrPt Xo c' T.Fr) :
    Integral T io' y ↔ Integral T io (letI := io.toAlgebra; letI := io'.toAlgebra; y.res hle h) := by
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, h]
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h T io N hN hp hT y`. Take `⟨la, e, ho⟩` from `exists_overLa io hN hp`. Conclude with `(nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)`. Introduce and unpack `h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩`.

Take `⟨N, hN, hp⟩` from `exists_nat_pos ho`. Conclude with `(nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)`.
-/
theorem intAt_iff (f : Rul Xo c) : IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (N : ℕ), N ≠ 0 →
    0 < vV T.V (N : T.Fr) → T.FinRes → ∀ y : IntFr Xo c T io, 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io N hN hp hT y
    obtain ⟨la, e, ho⟩ := exists_overLa io hN hp
    exact (nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)
  · rintro h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    obtain ⟨N, hN, hp⟩ := exists_nat_pos ho
    exact (nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c c' hle a n f hf`. Establish `hval` using `((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2`. Rewrite using `[intAt_iff, intAt_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h T io N hN hp hT y`.

Use `letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra`. Use `haveI := c.fin`. Use `haveI := c'.fin`. Use `haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp`. Use `haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _`.

Take `⟨L, _, _, g, hL, -, hg⟩` from `GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io`. Take `⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩` from `GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L`. Take `⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩` from `GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv`. Set `io' : c'.F →+* T'.Fr` to `ψ.toRingHom.comp g`. Establish `hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x` using `fun x => by`.

Use `DFunLike.congr_fun hg x` as an intermediate fact. Conclude with `(congrArg ψ this).trans (hψ _)`. Establish `hp' : 0 < vV T'.V (N : T'.Fr)`. Rewrite using `[← map_natCast iT, hv]`. Conclude with `mul_pos (by exact_mod_cast he) hp`.

Establish `e1 : evI y₁ f = iT (evI y f)`. Use `letI := io.toAlgebra`. Use `letI := (iT.comp io).toAlgebra`. Conclude with `(pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans (DFunLike.congr_fun hφ _)`. Use `letI := (iT.comp io).toAlgebra`.

Use `letI := io'.toAlgebra`. Set `y' : IntFr Xo c' T' io'` to `⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩`. Establish `e2 : evI y' (rulBC hle f) = evI y₁ f` using `hval T'.Fr hio y'.1`. Establish `key` using `h T' io' N hN hp' (hfin hT) y'`. Rewrite `key` using `[e2, e1, hv]`.

Conclude with `nonneg_of_mul_nonneg_right key (by exact_mod_cast he)`. Introduce `h T io' N hN hp hT y'`. Set `io : c.F →+* T.Fr` to `io'.comp (incF c c' hle)`. Establish `hio : ∀ x, io' (incF c c' hle x) = io x` using `fun _ => rfl`. Use `letI := io.toAlgebra`.

Use `letI := io'.toAlgebra`. Set `y : IntFr Xo c T io` to `⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, (integral_res_iff hle T io' io hio _).1 y'.2.2⟩`. Establish `e2 : evI y' (rulBC hle f) = evI y f` using `hval T.Fr hio y'.1`. Rewrite using `[e2]`. Conclude with `h T io N hN hp hT y`.
-/
theorem intAt_rulBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c c' hle a n f hf
  have hval := ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2
  rw [intAt_iff, intAt_iff]
  constructor
  · intro h T io N hN hp hT y
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI := c.fin
    haveI := c'.fin
    haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    obtain ⟨L, _, _, g, hL, -, hg⟩ := GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io
    obtain ⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    obtain ⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
    let io' : c'.F →+* T'.Fr := ψ.toRingHom.comp g
    have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x => by
      have := DFunLike.congr_fun hg x
      exact (congrArg ψ this).trans (hψ _)
    have hp' : 0 < vV T'.V (N : T'.Fr) := by
      rw [← map_natCast iT, hv]
      exact mul_pos (by exact_mod_cast he) hp
    have e1 : evI y₁ f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      exact (pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans
        (DFunLike.congr_fun hφ _)
    letI := (iT.comp io).toAlgebra
    letI := io'.toAlgebra
    let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y₁ f := hval T'.Fr hio y'.1
    have key := h T' io' N hN hp' (hfin hT) y'
    rw [e2, e1, hv] at key
    exact nonneg_of_mul_nonneg_right key (by exact_mod_cast he)
  · intro h T io' N hN hp hT y'
    let io : c.F →+* T.Fr := io'.comp (incF c c' hle)
    have hio : ∀ x, io' (incF c c' hle x) = io x := fun _ => rfl
    letI := io.toAlgebra
    letI := io'.toAlgebra
    let y : IntFr Xo c T io := ⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T io' io hio _).1 y'.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y f := hval T.Fr hio y'.1
    rw [e2]
    exact h T io N hN hp hT y

end GlobalTheory.IntCoefExt
