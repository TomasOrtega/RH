import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteNormEqZpowSiteAlg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FinLocalAtOfIntModel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInOverValuationRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsKeyIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRangeOfLetBC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DiscrMulXiIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianLetterIntegral

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.FinLoc

open GlobalTheory.IntModelExists GlobalTheory.Frames in

/- English proof (translation)
Introduce `hL hL₂ hU hL₅ E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl Yw b aw aK pw pK hN hd hw hK`. Establish `hG` using `hL.globalFns`. Establish `hinj : Function.Injective (algebraMap Tv.V Tv.Fr)` using `IsFractionRing.injective _ _`. Establish `hb : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F))` using `fun x => (RingHom.congr_fun hw.1 x).symm`. Set `ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)` to `fun τ => b.comp (embV c Wl τ)`.

Establish `hρ : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x))` using `fun τ x => hb _`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible Tv.V`. Take `⟨χ₀, hχ₀, -⟩` from `hN Tv.V b ϖ aw (Or.inr ⟨inferInstance, hϖ, by`. Rewrite using `[← hϖ.maximalIdeal_eq]`. Use the proof step `infer_instance⟩)`.

Take `⟨W₀⟩` from `(Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2`. Take `⟨ew, -, hew⟩` from `GlobalTheory.T.exists_constant_eigenbasis_tangent_arc hL hL₂ E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ (io.comp (algebraMap c.F K₁)) hw.1 hρ (exists_values c Wl)`. Take `⟨W₁, e₁, l₁, b₁⟩` from `exists_arcBasis_baseChange hL hL₂ hU hL₅ hinj hw W₀ hew`. Establish `hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (aK.restrict (c.V d.Wp).subtype) pK` using `⟨rfl, hK.2⟩`. Establish `hd' : ArcBasis (Y` using `d.Y) d.W (fun τ => (algebraMap c.F K₁).comp (embK c τ)) d.e := hd`.

Take `⟨W₂, e₂, l₂, b₂⟩` from `exists_arcBasis_baseChange hL hL₂ hU hL₅ io.injective hK' d.W hd'`. Establish `hρ' : (fun τ => io.comp ((algebraMap c.F K₁).comp (embK c τ))) = fun τ => (algebraMap Tv.V Tv.Fr).comp (ρ τ)`. Use function extensionality and compare the values at `fun τ => RingHom.ext fun x => (hρ τ x).symm`. Rewrite `b₂` using `[hρ']`. Take `⟨p, p₁, p₂, p₃⟩` from `exists_self aK.D₀ aK.gen`.

Establish `b₂'` using `(GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ d.Y Tv.Fr _ _ _ W₂ _ e₂ b₂).1 _ _ Yw _ _ _ W₁ p e₂ (fun x y => (p₂ _).trans (congrArg (x • ·) (p₂ y).symm)) (fun x => p₁ _) (fun τ k => p₃ _)`. Take `⟨g, hg, hge⟩` from `exists_matrix hG W₁ b₁ b₂'`. Establish `t₁ : ∀ τ k, GtTanR (e₁ τ k)` using `fun τ k => by`. Take `⟨v, i, hv⟩` from `b₁`. Conclude with `((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c _ _ Yw Tv.Fr _ _ _ W₁ (e₁ τ k)).2 _ (i τ k)).2 ((hv τ).1 k).1`.

Take `⟨thw, hthw, -⟩` from `GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange aw.D₀.P`. Take `⟨-, -, -, x₁, z₁⟩` from `(GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ Yw Tv.V Tv.Fr b aw _ hinj _ hw.1).2 (aK.restrict (c.V Wl).subtype) pw hw`. Take `⟨-, -, -, x₂, z₂⟩` from `(GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) io io.injective _ hK'.1).2 (aK.restrict (c.V d.Wp).subtype) pK hK'`. Take `⟨th₁, hth₁⟩` from `(x₁ thw).exists`. Take `⟨th₂, hth₂⟩` from `(x₂ d.th).exists`.

Establish `nz : ThNZ d.th`. Take `⟨_, _, _, _, h, -⟩` from `d.isArc3`. Conclude with `(GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h`. Take `⟨gm, hγ⟩` from `((GlobalTheory.ThetaOverField.nonzero_generates hL hL₂ Tv.Fr aK.D₀ th₁).2.1 (z₁ _ _ hth₁ hthw) th₂).exists`. Establish `hγ₀ : gm ≠ 0`.

Introduce and unpack `rfl`. Take `⟨j, hj⟩` from `(GlobalTheory.ThetaOverField.exists_ne_zero_iff aK.D₀ th₂).2 (z₂ _ _ hth₂ nz)`. Use `hj ((hγ j).trans ?_)` and prove the remaining obligations. Rewrite using `[constFn, map_zero, map_zero, zero_mul]`. Conclude with `⟨⟨b, hb, ρ, hρ, aw, aK, pw, pK, hw, hK, thw, hthw, ew, gm, g, ⟨th₁, th₂, hth₁, hth₂, hγ⟩, ⟨e₁, e₂, l₁, l₂, t₁, hge⟩⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, hγ₀, hg, (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ ew hew).2.1⟩`.
-/
theorem exists_intModel_heq : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (b : c.V Wl →+* Tv.V) (aw : ArcIn Dw l (c.V Wl).subtype Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io d.a.D₀ aK.D₀), Yw.N4 → ArcLieBasis d.W d.e → InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict (c.V Wl).subtype) pw → InBC io d.a aK pK → ∃ M : IntModel d Tv io Wl, M.b = b ∧ HEq M.aw aw ∧ M.aK = aK ∧ HEq M.pw pw ∧ HEq M.pK pK ∧ M.γ ≠ 0 ∧ (∀ τ, (M.g τ).det ≠ 0) ∧ ∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew := by
  intro hL hL₂ hU hL₅ E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl Yw b aw aK pw pK hN hd hw hK
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap Tv.V Tv.Fr) := IsFractionRing.injective _ _
  have hb : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F)) := fun x =>
    (RingHom.congr_fun hw.1 x).symm
  let ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V) := fun τ => b.comp (embV c Wl τ)
  have hρ : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x)) := fun τ x => hb _

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V b ϖ aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨ew, -, hew⟩ := GlobalTheory.T.exists_constant_eigenbasis_tangent_arc hL hL₂ E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ (io.comp (algebraMap c.F K₁))
    hw.1 hρ (exists_values c Wl)

  obtain ⟨W₁, e₁, l₁, b₁⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ hinj hw W₀ hew
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (aK.restrict (c.V d.Wp).subtype) pK := ⟨rfl, hK.2⟩
  have hd' : ArcBasis (Y := d.Y) d.W (fun τ => (algebraMap c.F K₁).comp (embK c τ)) d.e := hd
  obtain ⟨W₂, e₂, l₂, b₂⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ io.injective hK' d.W hd'
  have hρ' : (fun τ => io.comp ((algebraMap c.F K₁).comp (embK c τ))) = fun τ => (algebraMap Tv.V Tv.Fr).comp (ρ τ) :=
    funext fun τ => RingHom.ext fun x => (hρ τ x).symm
  rw [hρ'] at b₂
  obtain ⟨p, p₁, p₂, p₃⟩ := exists_self aK.D₀ aK.gen
  have b₂' := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ d.Y Tv.Fr _ _ _ W₂ _ e₂ b₂).1 _ _ Yw _ _ _ W₁ p e₂
    (fun x y => (p₂ _).trans (congrArg (x • ·) (p₂ y).symm)) (fun x => p₁ _) (fun τ k => p₃ _)
  obtain ⟨g, hg, hge⟩ := exists_matrix hG W₁ b₁ b₂'
  have t₁ : ∀ τ k, GtTanR (e₁ τ k) := fun τ k => by
    obtain ⟨v, i, hv⟩ := b₁
    exact ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c _ _ Yw Tv.Fr _ _ _ W₁ (e₁ τ k)).2 _ (i τ k)).2 ((hv τ).1 k).1

  obtain ⟨thw, hthw, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange aw.D₀.P
  obtain ⟨-, -, -, x₁, z₁⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ Yw Tv.V Tv.Fr b aw _ hinj _ hw.1).2
    (aK.restrict (c.V Wl).subtype) pw hw
  obtain ⟨-, -, -, x₂, z₂⟩ :=
    (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) io
      io.injective _ hK'.1).2
      (aK.restrict (c.V d.Wp).subtype) pK hK'
  obtain ⟨th₁, hth₁⟩ := (x₁ thw).exists
  obtain ⟨th₂, hth₂⟩ := (x₂ d.th).exists
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  obtain ⟨gm, hγ⟩ :=
    ((GlobalTheory.ThetaOverField.nonzero_generates hL hL₂ Tv.Fr aK.D₀ th₁).2.1 (z₁ _ _ hth₁ hthw) th₂).exists
  have hγ₀ : gm ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := (GlobalTheory.ThetaOverField.exists_ne_zero_iff aK.D₀ th₂).2 (z₂ _ _ hth₂ nz)
    refine hj ((hγ j).trans ?_)
    rw [constFn, map_zero, map_zero, zero_mul]
  exact ⟨⟨b, hb, ρ, hρ, aw, aK, pw, pK, hw, hK, thw, hthw, ew, gm, g, ⟨th₁, th₂, hth₁, hth₂, hγ⟩,
    ⟨e₁, e₂, l₁, l₂, t₁, hge⟩⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, hγ₀, hg,
    (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ ew hew).2.1⟩

section Val

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by simp [h0]⟩`. Establish `h1 : valV T.V (io x) ≠ 0` using `valV_ne_zero ((map_ne_zero io).2 h0)`. Establish `h2 : WithZero.log (w.valuation K x) ≤ 0`. Simplify using `using (WithZero.log_le_log ((w.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx`.

Establish `h3 : 0 ≤ vV T.V (io x)`. Rewrite using `[ho.2 x]`. Conclude with `mul_nonneg (Int.natCast_nonneg e) (by unfold vLa; omega)`. Use `IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) ?_` and prove the remaining obligations. Use `(WithZero.log_le_log h1 one_ne_zero).1 ?_` and prove the remaining obligations.

Rewrite using `[WithZero.log_one]`. Unfold `vV at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_range_of_le_one {w : HeightOneSpectrum (𝓞 K)} {T : CDVR} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa w T.V io e) {x : K} (hx : w.valuation K x ≤ 1) : io x ∈ Set.range (algebraMap T.V T.Fr) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have h1 : valV T.V (io x) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h2 : WithZero.log (w.valuation K x) ≤ 0 := by
    simpa using (WithZero.log_le_log ((w.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  have h3 : 0 ≤ vV T.V (io x) := by
    rw [ho.2 x]
    exact mul_nonneg (Int.natCast_nonneg e) (by unfold vLa; omega)
  refine IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) ?_
  refine (WithZero.log_le_log h1 one_ne_zero).1 ?_
  rw [WithZero.log_one]
  unfold vV at h3
  omega

/- English proof (translation)
Use `choose g hg using h`. Establish `hi : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective _ _`. Conclude with `⟨{ toFun := g map_one' := hi (by simp [hg]) map_mul' := fun x y => hi (by simp [hg]) map_zero' := hi (by simp [hg]) map_add' := fun x y => hi (by simp [hg]) }, hg⟩`.
-/
theorem exists_lift {T : CDVR} {R : Type} [CommRing R] (f : R →+* T.Fr)
    (h : ∀ x, f x ∈ Set.range (algebraMap T.V T.Fr)) : ∃ g : R →+* T.V, ∀ x, algebraMap T.V T.Fr (g x) = f x := by
  choose g hg using h
  have hi : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  exact ⟨{ toFun := g
           map_one' := hi (by simp [hg])
           map_mul' := fun x y => hi (by simp [hg])
           map_zero' := hi (by simp [hg])
           map_add' := fun x y => hi (by simp [hg]) }, hg⟩

/- English proof (translation)
Establish `h : (N : K) = algebraMap (𝓞 K) K (N : 𝓞 K)` using `by simp`. Rewrite using `[vLa, h, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ (by exact_mod_cast hN), WithZero.log_exp, neg_neg, vla]`.
-/
theorem vLa_natCast (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (hN : N ≠ 0) :
    vLa la (N : K) = vla la (Ideal.span {(N : 𝓞 K)}) := by
  classical
  have h : (N : K) = algebraMap (𝓞 K) K (N : 𝓞 K) := by simp
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ (by exact_mod_cast hN), WithZero.log_exp, neg_neg, vla]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `Or.inl hx`. Use `right`. Take `⟨v, hv⟩` from `h`. Establish `h0 : algebraMap T.V T.Fr v ≠ 0` using `hv ▸ mul_ne_zero hN hx`.

Establish `h1 : valV T.V (algebraMap T.V T.Fr v) ≤ 1` using `HeightOneSpectrum.valuation_le_one _ v`. Establish `h2` using `(WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1`. Rewrite `h2` using `[WithZero.log_one]`. Establish `h3 : 0 ≤ vV T.V (N * x)`. Rewrite using `[← hv]`.

Unfold `vV`. Use linear arithmetic over natural numbers and integers. Rewrite `h3` using `[vV_mul hN hx]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bound_of_mul_mem {T : CDVR} {N x : T.Fr} (hN : N ≠ 0) (h : N * x ∈ Set.range (algebraMap T.V T.Fr))
    {m : ℤ} (hm : vV T.V N ≤ m) : x = 0 ∨ -m ≤ vV T.V x := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨v, hv⟩ := h
  have h0 : algebraMap T.V T.Fr v ≠ 0 := hv ▸ mul_ne_zero hN hx
  have h1 : valV T.V (algebraMap T.V T.Fr v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 ≤ vV T.V (N * x) := by
    rw [← hv]
    unfold vV
    omega
  rw [vV_mul hN hx] at h3
  omega

/- English proof (translation)
Use `la.isMaximal` as an intermediate fact. Establish `: Finite (𝓞 K ⧸ la.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot`. Use `letI := Ideal.Quotient.field la.asIdeal`. Use `⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ la.asIdeal) (ringChar _))`.
-/
theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  have := la.isMaximal
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ la.asIdeal) (ringChar _))

/- English proof (translation)
Take `⟨x, hx⟩` from `p.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K p I))`. Establish `h0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hx.symm`.

Establish `h1 : ordAt p x = FractionalIdeal.count K p I`. Rewrite using `[ordAt, hx, WithZero.log_exp, neg_neg]`. Conclude with `⟨x, ⟨h0, by rw [← ordAt_eq_count p h0, h1]⟩, h1⟩`.
-/
theorem exists_locGen (p : HeightOneSpectrum (𝓞 K)) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    ∃ x : K, IsLocGen p x I ∧ vLa p x = FractionalIdeal.count K p I := by
  obtain ⟨x, hx⟩ := p.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K p I))
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have h1 : ordAt p x = FractionalIdeal.count K p I := by
    rw [ordAt, hx, WithZero.log_exp, neg_neg]
  exact ⟨x, ⟨h0, by rw [← ordAt_eq_count p h0, h1]⟩, h1⟩

end Val

end GlobalTheory.ArcCM.FinLoc

namespace GlobalTheory.ArcCM

open FinLoc in

/- English proof (translation)
Introduce `hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS la w hw a' n`. Take `⟨Tv, io, hfin, how⟩` from `(exists_finSite_norm_eq_zpow_siteAlg K₁ w).1`. Establish `hvw : ∀ x : K₁, vV Tv.V (io x) = vLa w x` using `fun x => by rw [how.2 x]; simp`. Establish `hlo : w.asIdeal.LiesOver la.asIdeal` using `⟨hw.symm⟩`. Establish `he : 0 < w.asIdeal.ramificationIdx (𝓞 c.F)`.

Rewrite using `[← Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]`. Conclude with `Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot)`. Establish `hola : OverLa la Tv.V (io.comp (algebraMap c.F K₁)) (w.asIdeal.ramificationIdx (𝓞 c.F))` using `⟨he, fun x => (hvw _).trans (ordAt_algebraMap_of_liesOver hw x)⟩`. Take `⟨p, hp, hpl⟩` from `exists_prime_mem la`. Establish `hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits`.

Rewrite using `[ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]`. Use `(la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl` as an intermediate fact. Simplify using `using this`. Take `⟨Wl, hpW, hWl⟩` from `exists_valuationSubring_complex_comap_val_eq c.F _ p hpU`. Take `⟨Yw, h4, hpush⟩` from `hM p Wl hp hpW`.

Take `⟨b, hb⟩` from `exists_lift (T := Tv) ((io.comp (algebraMap c.F K₁)).comp (c.V Wl).subtype) fun x => mem_range_of_le_one hola (by`. Establish `hx : (x : c.F) ∈ Wl.comap c.F.val.toRingHom` using `x.2`. Rewrite `hx` using `[hWl]`. Conclude with `hx)`. Take `⟨ρ, hρ⟩` from `exists_lift (T := Tv) (io.comp (algebraMap (𝓞 K₁) K₁)) fun x => mem_range_of_le_one how (w.valuation_le_one x)`.

Establish `hρ' : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)` using `hρ`. Take `⟨aw, aK, pw, pK, ψ, bw, bK, hψ, hsq, htau⟩` from `GlobalTheory.ArcCM.exists_arcIn_over_valuationRing hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s Tv io ρ _ (c.V Wl).subtype b hρ' hb`. Take `⟨M, m₁, m₂, m₃, m₄, m₅, hγ, hg, hbas⟩` from `exists_intModel_heq hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c K₁ d Tv io Wl Yw b aw aK pw pK h4 (arcDatum_arcLieBasis hK.laws hK.laws2 E H Dw l Xo c K₁ d s.tan) bw bK`. Substitute `m₁` using the available equality. Take `rfl` from `eq_of_heq m₂`.

Substitute `m₃` using the available equality. Take `rfl` from `eq_of_heq m₄`. Take `rfl` from `eq_of_heq m₅`. Establish `hn' : n' ≠ 0` using `s.n_pos.ne'`. Establish `hm : ∀ N : ℕ, N ≠ 0 → vla la (Ideal.span {(N : 𝓞 c.F)}) ≤ mOf E n' la → vV Tv.V (N : Tv.Fr) ≤ ((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ)` using `fun N hN h => by`.

Establish `e` using `hola.2 (N : c.F)`. Rewrite `e` using `[map_natCast, vLa_natCast la hN]`. Rewrite using `[e]`. Conclude with `Nat.mul_le_mul_left _ h` after adjusting the coercions. Establish `key : ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), ∃ cl : K₁, cl ≠ 0 ∧ vLa w cl = FractionalIdeal.count K₁ w (s.line τ k).I ∧ ∀ j, io cl * M.g τ k j = 0 ∨ -((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) ≤ vV Tv.V (io cl * M.g τ k j)`.

Introduce `τ k`. Consider the cases of `hk : s.kind τ k with`. Consider the case `none`. Establish `hd : (NumberField.discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)`. Use `⟨1, one_ne_zero, ?_, fun j => ?_⟩` and prove the remaining obligations.

Simplify using `[CMIn.line, hk, MLine.one, vLa, FractionalIdeal.count_one]`. Establish `h` using `GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _ (GlobalTheory.XiIntegral.discr_mul_xi_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k hk) j`. Use `bound_of_mul_mem (N := ((NumberField.discr E).natAbs : Tv.Fr)) (by exact_mod_cast hd) ?_ (hm _ hd (le_max_left _ _))` and prove the remaining obligations. Rewrite using `[map_one, _root_.one_mul]`. Take `⟨v, hv⟩` from `h`.

Break down `Int.natAbs_eq (NumberField.discr E) with h' | h'` into its components or cases. Conclude with `⟨v, by rw [hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_natCast]⟩`. Conclude with `⟨-v, by rw [map_neg, hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]⟩`. Consider the case `some m`. Take `⟨cl, hcl, hv⟩` from `exists_locGen w (s.line τ k).I`.

Use `⟨cl, hcl.1, hv, fun j => ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _ (GlobalTheory.ArcCM.abelian_letter_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k m cl hk hcl) j`. Use `bound_of_mul_mem (N := (n' : Tv.Fr)) (by exact_mod_cast hn') ?_ (hm _ hn' (le_max_right _ _))` and prove the remaining obligations. Rewrite `h` using `[map_mul, map_natCast, _root_.mul_assoc]`. Then use the resulting hypothesis. Use `choose cl hcl₀ hcl₁ hcl₂ using key`.

Establish `hio : ∀ τ k, io (cl τ k) ≠ 0` using `fun τ k => (map_ne_zero io).2 (hcl₀ τ k)`. Use `GlobalTheory.ArcQ.finLocalAt_of_intModel hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d w Tv io Wl Yw M la _ (fun τ k => (io (cl τ k))⁻¹) (fun τ => Matrix.diagonal (fun k => io (cl τ k)) * M.g τ) _ _ _ hS.1 hfin how hola h4 hpush hbas ⟨hγ, GlobalTheory. …` and prove the remaining obligations. Rewrite using `[← hcl₁, ← hvw]`. Simplify using `[vV]`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal]`.

Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hio τ k) (hg τ)`. Rewrite using `[Matrix.diagonal_mul, inv_mul_cancel_left₀ (hio τ k)]`. Rewrite using `[Matrix.diagonal_mul]`. Conclude with `hcl₂ τ k j`.
-/
theorem finLocalAt_of_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.ArcQ.FinLocalAt d w n (-FractionalIdeal.count K₁ w s.Tl.I) (fun τ k => -FractionalIdeal.count K₁ w (s.line τ k).I) (w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la) (intAt Xo c a' n la) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS la w hw a' n
  obtain ⟨Tv, io, hfin, how⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).1
  have hvw : ∀ x : K₁, vV Tv.V (io x) = vLa w x := fun x => by rw [how.2 x]; simp
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 c.F) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
    exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot)
  have hola : OverLa la Tv.V (io.comp (algebraMap c.F K₁)) (w.asIdeal.ramificationIdx (𝓞 c.F)) :=
    ⟨he, fun x => (hvw _).trans (ordAt_algebraMap_of_liesOver hw x)⟩

  obtain ⟨p, hp, hpl⟩ := exists_prime_mem la
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  obtain ⟨Wl, hpW, hWl⟩ := exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Yw, h4, hpush⟩ := hM p Wl hp hpW
  obtain ⟨b, hb⟩ := exists_lift (T := Tv) ((io.comp (algebraMap c.F K₁)).comp (c.V Wl).subtype) fun x =>
    mem_range_of_le_one hola (by
      have hx : (x : c.F) ∈ Wl.comap c.F.val.toRingHom := x.2
      rw [hWl] at hx
      exact hx)
  obtain ⟨ρ, hρ⟩ := exists_lift (T := Tv) (io.comp (algebraMap (𝓞 K₁) K₁)) fun x =>
    mem_range_of_le_one how (w.valuation_le_one x)
  have hρ' : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁) := hρ

  obtain ⟨aw, aK, pw, pK, ψ, bw, bK, hψ, hsq, htau⟩ :=
    GlobalTheory.ArcCM.exists_arcIn_over_valuationRing hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s Tv io ρ _ (c.V Wl).subtype b hρ' hb
  obtain ⟨M, m₁, m₂, m₃, m₄, m₅, hγ, hg, hbas⟩ := exists_intModel_heq hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c K₁ d
    Tv io Wl Yw b aw aK pw pK h4 (arcDatum_arcLieBasis hK.laws hK.laws2 E H Dw l Xo c K₁ d s.tan) bw bK
  subst m₁
  obtain rfl := eq_of_heq m₂
  subst m₃
  obtain rfl := eq_of_heq m₄
  obtain rfl := eq_of_heq m₅

  have hn' : n' ≠ 0 := s.n_pos.ne'
  have hm : ∀ N : ℕ, N ≠ 0 → vla la (Ideal.span {(N : 𝓞 c.F)}) ≤ mOf E n' la →
      vV Tv.V (N : Tv.Fr) ≤ ((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) := fun N hN h => by
    have e := hola.2 (N : c.F)
    rw [map_natCast, vLa_natCast la hN] at e
    rw [e]
    exact_mod_cast Nat.mul_le_mul_left _ h
  have key : ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), ∃ cl : K₁, cl ≠ 0 ∧
      vLa w cl = FractionalIdeal.count K₁ w (s.line τ k).I ∧ ∀ j, io cl * M.g τ k j = 0 ∨
        -((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) ≤ vV Tv.V (io cl * M.g τ k j) := by
    intro τ k
    cases hk : s.kind τ k with
    | none =>
      have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
      refine ⟨1, one_ne_zero, ?_, fun j => ?_⟩
      · simp [CMIn.line, hk, MLine.one, vLa, FractionalIdeal.count_one]
      · have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
          (GlobalTheory.XiIntegral.discr_mul_xi_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k hk) j
        refine bound_of_mul_mem (N := ((NumberField.discr E).natAbs : Tv.Fr)) (by exact_mod_cast hd) ?_
          (hm _ hd (le_max_left _ _))
        rw [map_one, _root_.one_mul]
        obtain ⟨v, hv⟩ := h
        rcases Int.natAbs_eq (NumberField.discr E) with h' | h'
        · exact ⟨v, by rw [hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_natCast]⟩
        · exact ⟨-v, by rw [map_neg, hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]⟩
    | some m =>
      obtain ⟨cl, hcl, hv⟩ := exists_locGen w (s.line τ k).I
      refine ⟨cl, hcl.1, hv, fun j => ?_⟩
      have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
        (GlobalTheory.ArcCM.abelian_letter_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k m cl hk hcl) j
      refine bound_of_mul_mem (N := (n' : Tv.Fr)) (by exact_mod_cast hn') ?_ (hm _ hn' (le_max_right _ _))
      rwa [map_mul, map_natCast, _root_.mul_assoc] at h
  choose cl hcl₀ hcl₁ hcl₂ using key
  have hio : ∀ τ k, io (cl τ k) ≠ 0 := fun τ k => (map_ne_zero io).2 (hcl₀ τ k)
  refine GlobalTheory.ArcQ.finLocalAt_of_intModel hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d w Tv io Wl Yw M la _
    (fun τ k => (io (cl τ k))⁻¹) (fun τ => Matrix.diagonal (fun k => io (cl τ k)) * M.g τ) _ _ _ hS.1 hfin how hola h4
    hpush hbas ⟨hγ, GlobalTheory.ArcGamma.vV_gamma hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau hγ⟩
    (fun τ k => ⟨inv_ne_zero (hio τ k), ?_⟩) (fun τ => ?_) (fun τ k j => ?_) (fun τ k j => ?_) a' n
  · rw [← hcl₁, ← hvw]
    simp [vV]
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hio τ k) (hg τ)
  · rw [Matrix.diagonal_mul, inv_mul_cancel_left₀ (hio τ k)]
  · rw [Matrix.diagonal_mul]
    exact hcl₂ τ k j

end GlobalTheory.ArcCM
