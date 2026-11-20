import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartnerPointIntegralModel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FirstFormIffSecondForm
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NaturalOfChartIndep
import Development.WeilBound.CoreStatements.AdicCompleteSpans.MinorC
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {N : Type} [NormedField N]

/- English proof (translation)
Establish `hπ0 : π ≠ 0` using `fun h => by simp [h, vV] at hπ`. Establish `hu0 : x * π ^ (-vV V x) ≠ 0` using `mul_ne_zero hx (zpow_ne_zero _ hπ0)`. Establish `hv : vV V (x * π ^ (-vV V x)) = 0`. Rewrite using `[vV_mul hx (zpow_ne_zero _ hπ0), GlobalTheory.ThetaValueIdentityCompare.vV_zpow, hπ]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨u, hu, hue⟩` from `GlobalTheory.ThetaValueIdentityCompare.exists_unit hu0 hv`. Establish `hn : ‖j (algebraMap V K u)‖ = 1`. Take `⟨w, rfl⟩` from `hu`. Establish `h1` using `hj (w : V)`. Establish `h2` using `hj ((w⁻¹ : Vˣ) : V)`.

Establish `h3 : ‖j (algebraMap V K (w : V))‖ * ‖j (algebraMap V K ((w⁻¹ : Vˣ) : V))‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← map_mul]`. Simplify using the standard rewrite rules. Use polynomial arithmetic with `[norm_nonneg (j (algebraMap V K (w : V))), norm_nonneg (j (algebraMap V K ((w⁻¹ : Vˣ) : V)))]`. Rewrite `hn` using `[hue, map_mul, norm_mul, map_zpow₀, norm_zpow, zpow_neg]`.

Establish `hb : ‖j π‖ ≠ 0` using `norm_ne_zero_iff.2 ((map_ne_zero j).2 hπ0)`. Clear denominators, using `at hn` for the nonvanishing conditions. Conclude with `hn`.
-/
theorem norm_eq_zpow (j : K →+* N) (hj : ∀ x : V, ‖j (algebraMap V K x)‖ ≤ 1) {π : K} (hπ : vV V π = 1)
    {x : K} (hx : x ≠ 0) : ‖j x‖ = ‖j π‖ ^ vV V x := by
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ
  have hu0 : x * π ^ (-vV V x) ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hv : vV V (x * π ^ (-vV V x)) = 0 := by
    rw [vV_mul hx (zpow_ne_zero _ hπ0), GlobalTheory.ThetaValueIdentityCompare.vV_zpow, hπ]
    ring
  obtain ⟨u, hu, hue⟩ := GlobalTheory.ThetaValueIdentityCompare.exists_unit hu0 hv
  have hn : ‖j (algebraMap V K u)‖ = 1 := by
    obtain ⟨w, rfl⟩ := hu
    have h1 := hj (w : V)
    have h2 := hj ((w⁻¹ : Vˣ) : V)
    have h3 : ‖j (algebraMap V K (w : V))‖ * ‖j (algebraMap V K ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul]
      simp
    nlinarith [norm_nonneg (j (algebraMap V K (w : V))), norm_nonneg (j (algebraMap V K ((w⁻¹ : Vˣ) : V)))]
  rw [hue, map_mul, norm_mul, map_zpow₀, norm_zpow, zpow_neg] at hn
  have hb : ‖j π‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hπ0)
  field_simp at hn
  exact hn

end Val

section Loc

open scoped NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Establish `h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p])` using `by simp`. Rewrite using `[h, norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zpow_zero]`.

Use `inv_lt_one_of_one_lt₀ hp1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Establish `hl` using `congrArg Real.log h`. Rewrite `hl` using `[Real.log_zpow, Real.log_inv]`.

Rewrite using `[Real.rpow_def_of_pos hp0, ← Real.exp_log (zpow_pos hb m), Real.log_zpow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(m : ℝ) * hl`.
-/
theorem zpow_eq_rpow {b : ℝ} (hb : 0 < b) {n m : ℤ} (h : b ^ n = (p : ℝ)⁻¹) :
    b ^ m = (p : ℝ) ^ (-((m : ℝ) / (n : ℝ))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : n ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at h
    have := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hl := congrArg Real.log h
  rw [Real.log_zpow, Real.log_inv] at hl
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (zpow_pos hb m), Real.log_zpow]
  congr 1
  field_simp
  linear_combination (m : ℝ) * hl

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
The claim follows from `Subtype.val_injective mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ Valued.integer.mem_iff.1 y.2, fun h => ⟨⟨x, Valued.integer.mem_iff.2 h⟩, rfl⟩⟩`.
-/
theorem unitBall : GlobalTheory.BK.IsUnitBall 𝒪[L] L where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ Valued.integer.mem_iff.1 y.2, fun h => ⟨⟨x, Valued.integer.mem_iff.2 h⟩, rfl⟩⟩

attribute [local instance] unitBall

/- English proof (translation)
Establish `: ProperSpace L` using `FiniteDimensional.proper ℚ_[p] L`. Establish `hc : CompactSpace 𝒪[L]`. Establish `: ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1`. Use extensionality with `x`. Simplify using `[Valued.integer.mem_iff]`.

Conclude with `isCompact_iff_compactSpace.1 (this ▸ isCompact_closedBall 0 1)`. Establish `: (Valued.v : Valuation L NNReal).RankOne` using `inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := L)))`. Take `⟨-, h1, h2⟩` from `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.1 hc`. Conclude with `⟨h1, h2⟩`.
-/
theorem dvr_fin [FiniteDimensional ℚ_[p] L] : IsDiscreteValuationRing 𝒪[L] ∧ Finite 𝓀[L] := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : CompactSpace 𝒪[L] := by
    have : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [Valued.integer.mem_iff]
    exact isCompact_iff_compactSpace.1 (this ▸ isCompact_closedBall 0 1)
  have : (Valued.v : Valuation L NNReal).RankOne := inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := L)))
  obtain ⟨-, h1, h2⟩ :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.1 hc
  exact ⟨h1, h2⟩

/- English proof (translation)
Take `⟨hd, hf⟩` from `dvr_fin L`. Establish `: CompleteSpace L` using `FiniteDimensional.complete ℚ_[p] L`. Establish `hc : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[L]) 𝒪[L]` using `PositivityTheory.CompleteLocalMinorRing.Minor.isAdicComplete_max (K := L) p`. Establish `h0 : CharZero 𝒪[L]` using `⟨fun a b h => Nat.cast_injective (R := L) (by`. Use `congrArg (algebraMap 𝒪[L] L) h` as an intermediate fact.

Simplify using `using this)⟩`. Set `T : CDVR` to `{ V := 𝒪[L], dvr := hd, cpl := hc, ch0 := h0 }`. Set `e : T.Fr ≃+* L` to `(FractionRing.algEquiv 𝒪[L] L).toRingEquiv`. Set `j : T.Fr →+* PadicAlgCl p` to `(algebraMap L (PadicAlgCl p)).comp e.toRingHom`. Establish `hje : ∀ x : T.Fr, j x = ((e x : L) : PadicAlgCl p)` using `fun _ => rfl`.

Establish `hea : ∀ x : 𝒪[L], e (algebraMap 𝒪[L] T.Fr x) = (x : L)` using `fun x => (FractionRing.algEquiv 𝒪[L] L).commutes x`. Establish `hj : ∀ x : T.V, ‖j (algebraMap T.V T.Fr x)‖ ≤ 1` using `fun x => by`. Rewrite using `[hje]`. Use `erw [hea x]`. Conclude with `Valued.integer.norm_le_one x`.

Take `⟨π, hπ⟩` from `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_exists_uniformizer T.Fr`. Establish `hπ1 : vV T.V π = 1` using `by simp [vV, valV, hπ]`. Establish `hπ0 : π ≠ 0` using `fun h => by simp [h, vV] at hπ1`. Establish `hb : 0 < ‖j π‖` using `norm_pos_iff.2 ((map_ne_zero j).2 hπ0)`. Establish `hp0 : ((p : ℕ) : T.Fr) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`.

Establish `hpn : ‖j π‖ ^ vV T.V ((p : ℕ) : T.Fr) = (p : ℝ)⁻¹`. Rewrite using `[← norm_eq_zpow j hj hπ1 hp0, map_natCast, norm_natCast_p]`. Use `⟨T, j, hf, ?_, fun x hx => ⟨e.symm ⟨x, hx⟩, ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use `(PositivityTheory.CompleteLocalMinorRing.Minor.mem_max_iff (K := L)).2 ?_` and prove the remaining obligations. Rewrite using `[map_natCast]`.

Establish `: ‖((p : ℕ) : L)‖ = ‖((p : ℕ) : PadicAlgCl p)‖` using `rfl`. Rewrite using `[this, norm_natCast_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)`. Rewrite using `[hje, e.apply_symm_apply]`. Rewrite using `[norm_eq_zpow j hj hπ1 hx]`.

Conclude with `zpow_eq_rpow hb hpn`.
-/
theorem exists_cdvr [FiniteDimensional ℚ_[p] L] :
    ∃ (T : CDVR) (j : T.Fr →+* PadicAlgCl p), T.FinRes ∧ ((p : ℕ) : T.V) ∈ IsLocalRing.maximalIdeal T.V ∧
      (∀ x ∈ L, x ∈ Set.range j) ∧
      ∀ x : T.Fr, x ≠ 0 → ‖j x‖ = (p : ℝ) ^ (-((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ))) := by
  obtain ⟨hd, hf⟩ := dvr_fin L
  have : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[L]) 𝒪[L] :=
    PositivityTheory.CompleteLocalMinorRing.Minor.isAdicComplete_max (K := L) p
  have h0 : CharZero 𝒪[L] := ⟨fun a b h => Nat.cast_injective (R := L) (by
    have := congrArg (algebraMap 𝒪[L] L) h
    simpa using this)⟩
  let T : CDVR := { V := 𝒪[L], dvr := hd, cpl := hc, ch0 := h0 }
  let e : T.Fr ≃+* L := (FractionRing.algEquiv 𝒪[L] L).toRingEquiv
  let j : T.Fr →+* PadicAlgCl p := (algebraMap L (PadicAlgCl p)).comp e.toRingHom
  have hje : ∀ x : T.Fr, j x = ((e x : L) : PadicAlgCl p) := fun _ => rfl
  have hea : ∀ x : 𝒪[L], e (algebraMap 𝒪[L] T.Fr x) = (x : L) := fun x =>
    (FractionRing.algEquiv 𝒪[L] L).commutes x
  have hj : ∀ x : T.V, ‖j (algebraMap T.V T.Fr x)‖ ≤ 1 := fun x => by
    rw [hje]
    erw [hea x]
    exact Valued.integer.norm_le_one x
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_exists_uniformizer T.Fr
  have hπ1 : vV T.V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have hb : 0 < ‖j π‖ := norm_pos_iff.2 ((map_ne_zero j).2 hπ0)
  have hp0 : ((p : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpn : ‖j π‖ ^ vV T.V ((p : ℕ) : T.Fr) = (p : ℝ)⁻¹ := by
    rw [← norm_eq_zpow j hj hπ1 hp0, map_natCast, norm_natCast_p]
  refine ⟨T, j, hf, ?_, fun x hx => ⟨e.symm ⟨x, hx⟩, ?_⟩, fun x hx => ?_⟩
  · refine (PositivityTheory.CompleteLocalMinorRing.Minor.mem_max_iff (K := L)).2 ?_
    rw [map_natCast]
    have : ‖((p : ℕ) : L)‖ = ‖((p : ℕ) : PadicAlgCl p)‖ := rfl
    rw [this, norm_natCast_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  · rw [hje, e.apply_symm_apply]
  · rw [norm_eq_zpow j hj hπ1 hx]
    exact zpow_eq_rpow hb hpn

end Loc

section Main

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.aeval_C]`. Simplify using `[intCast_mem L a]`. Consider the case `add f g hf hg`.

Rewrite using `[map_add]`. Conclude with `L.add_mem hf hg`. Consider the case `mul_X f i hf`. Rewrite using `[map_mul, MvPolynomial.aeval_X]`. Conclude with `L.mul_mem hf (hz i)`.
-/
theorem aeval_mem {σ : Type} {z : σ → PadicAlgCl p} {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L)
    (g : MvPolynomial σ ℤ) : MvPolynomial.aeval z g ∈ L := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    simp [intCast_mem L a]
  | add f g hf hg =>
    rw [map_add]
    exact L.add_mem hf hg
  | mul_X f i hf =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact L.mul_mem hf (hz i)

/- English proof (translation)
Take `⟨dg, dh, g, f, -, -, -, -, h0, e⟩` from `h`. Rewrite using `[eq_div_of_mul_eq h0 e.symm]`. Conclude with `L.div_mem (aeval_mem hz g) (aeval_mem hz f)`.
-/
theorem hasVal_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → PadicAlgCl p} {w : PadicAlgCl p}
    {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L) (h : Small.HasVal y a s z w) : w ∈ L := by
  obtain ⟨dg, dh, g, f, -, -, -, -, h0, e⟩ := h
  rw [eq_div_of_mul_eq h0 e.symm]
  exact L.div_mem (aeval_mem hz g) (aeval_mem hz f)

/- English proof (translation)
Establish `: Finite (Set.range z)` using `Set.finite_range z |>.to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`.
-/
theorem finite_adjoin {σ : Type} [Finite σ] (z : σ → PadicAlgCl p) :
    FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range z)) := by
  have : Finite (Set.range z) := Set.finite_range z |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/- English proof (translation)
Establish `hres : Formalism.L2.Pj.resCharOf la = p`. Assume the negation of the conclusion as `h`. Use `Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla` and prove the remaining obligations. Conclude with `(Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd`. Use `Formalism.L2.Pj.Crude.crv_vLa_char la` as an intermediate fact.

Rewrite `this` using `[hres]`. Conclude with `this`.
-/
theorem vLa_p {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} (hla : (p : 𝓞 F) ∈ la.asIdeal) :
    vLa la ((p : ℕ) : F) = ramOverZ la := by
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  have := Formalism.L2.Pj.Crude.crv_vLa_char la
  rw [hres] at this
  exact this

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr hInt hUnif A p _ z ev hz hv hG`. Take `⟨hc1, hc2, -, -⟩` from `hG`. Establish `hzL : ∀ i, z i ∈ IntermediateField.adjoin ℚ_[p] (Set.range z)` using `fun i => IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩`. Use `Pt.finite_adjoin z` as an intermediate fact. Take `⟨T₀, j, hfin, hpm, hL, hnorm⟩` from `Pt.exists_cdvr (IntermediateField.adjoin ℚ_[p] (Set.range z))`.

Establish `hev : ∀ x : A, ∃ a, j a = ev x` using `fun x => hL _ (Pt.hasVal_mem hzL (hv x))`. Use `choose f hf using hev`. Establish `hinj : Function.Injective j` using `j.injective`. Set `ev₀ : A →+* T₀.Fr` to `{ toFun := f map_one' := hinj (by rw [hf, map_one, map_one]) map_mul' := fun a b => hinj (by rw [hf, map_mul, map_mul, hf, hf]) map_zero' := hinj (by rw [hf, map_zero, map_zero]) map_add' := fun a b => hinj (by rw [hf, map_add, map_add, hf, hf]) }`. Establish `hev₀ : ∀ x, j (ev₀ x) = ev x` using `hf`.

Set `cA : c.F →+* A` to `Or.𝔐.cst.codRestrict A hc1`. Set `io₀ : c.F →+* T₀.Fr` to `ev₀.comp cA`. Take `⟨la, e₀, ho₀, hpla⟩` from `GlobalTheory.PartnerIn.exists_overLa T₀ io₀ (Fact.out : p.Prime) hpm`. Take `⟨q, φq, yq, hyq, hφA⟩` from `hc2`. Use `letI a0 : Algebra c.F T₀.Fr := io₀.toAlgebra`.

Use `letI aΩ : Algebra c.F RM.Ω := Small.cstAlg Or`. Set `ψ₀ : q.R →ₐ[c.F] T₀.Fr` to `{ ev₀.comp (φq.toRingHom.codRestrict A hφA) with commutes' := fun a => by show ev₀ _ = ev₀ (cA a)`. Conclude with `congrArg ev₀ (Subtype.ext (φq.commutes a)) }`. Take `⟨y₁, hy₁⟩` from `GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c q.R yq T₀.Fr ψ₀`. Take `⟨T', io', e', y', ho', hy', φ, z₁, t, -, hφy, hb⟩` from `hInt la T₀ io₀ e₀ ho₀ hfin y₁`.

Take `⟨T, φV, φ₂, r, yy, τ, hfe, hbc, hyA, hτ⟩` from `hUnif la T' io' e' ho' y' hy'`. Use `letI a1 : Algebra c.F T'.Fr := io'.toAlgebra`. Use `letI a2 : Algebra c.F T.Fr := (φ₂.comp io').toAlgebra`. Set `φ₂A : T'.Fr →ₐ[c.F] T.Fr` to `{ φ₂ with commutes' := fun _ => rfl }`. Take `⟨zT, hzT⟩` from `GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c T'.Fr z₁ T.Fr φ₂A`.

Establish `hFB` using `frBorBC T'.Fr T.Fr φ₂A t z₁ y'.1 zT yy.1 hb hzT hbc`. Use `⟨la, T, φ₂.comp io', r * e', yy, (φ₂.comp φ.toRingHom).comp ev₀, zT, fun i => Units.map (φ₂A : T'.Fr →* T.Fr) (t i), ?_⟩` and prove the remaining obligations. Unfold `FinRd.IsIntPt`. Use `⟨hpla, hfe.overLa ho', hyA, ⟨τ, hτ⟩, fun a h => ?_, fun x => ?_, ⟨q, φq, φ₂A.comp (φ.comp ψ₀), yq, hyq, ?_, fun r => ⟨hφA r, rfl⟩⟩, hFB⟩` and prove the remaining obligations. Use `show φ₂ (φ (ev₀ ⟨_, h⟩)) = φ₂ (io' a)`.

Establish `h1 : φ (io₀ a) = io' a` using `φ.commutes a`. Rewrite using `[← h1]`. Both sides reduce to the same expression. Establish `hio : φ.toRingHom.comp io₀ = io'` using `RingHom.ext fun a => φ.commutes a`. Establish `ho'' : OverLa la T'.V (φ.toRingHom.comp io₀) e'`.

Rewrite using `[hio]`. Conclude with `ho'`. Take `⟨r', ⟨hr'0, hr'⟩, he'⟩` from `(GlobalTheory.ThetaValueIdentityCompare.overLa_iff ho₀ hfin φ.toRingHom e').1 ho''`. Establish `hr0` using `hfe.2.2.2.2.1`. Establish `hram` using `FinRd.ram_pos hpla`.

Distinguish the cases in `hx : ev₀ x = 0`. Establish `h1 : ev x = 0` using `by rw [← hev₀ x, hx, map_zero]`. Establish `h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x = 0` using `by show φ₂ (φ (ev₀ x)) = 0`. Rewrite using `[hx, map_zero, map_zero]`. Rewrite using `[h1, norm_zero]`.

Unfold `FinRd.absT`. Rewrite using `[if_pos h2]`. Establish `h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x ≠ 0` using `by show φ₂ (φ (ev₀ x)) ≠ 0`. Conclude with `(map_ne_zero φ₂).2 ((map_ne_zero φ).2 hx)`. Rewrite using `[← hev₀ x, hnorm _ hx]`.

Unfold `FinRd.absT`. Rewrite using `[if_neg h2]`. Establish `hv1 : vV T.V (((φ₂.comp φ.toRingHom).comp ev₀) x) = r * (r' * vV T₀.V (ev₀ x))` using `by show vV T.V (φ₂ (φ (ev₀ x))) = _`. Rewrite using `[hfe.2.2.2.2.2]`. Use `congr 1`.

Conclude with `hr' _ hx`. Establish `hv2 : vV T₀.V ((p : ℕ) : T₀.Fr) = e₀ * ramOverZ la`. Establish `h3` using `ho₀.2 ((p : ℕ) : c.F)`. Rewrite `h3` using `[map_natCast, Pt.vLa_p hpla]`. Conclude with `h3`.

Establish `he0 : (e₀ : ℝ) ≠ 0` using `by exact_mod_cast ho₀.1.ne'`. Establish `hr1 : (r : ℝ) ≠ 0` using `by exact_mod_cast hr0.ne'`. Establish `hr2 : (r' : ℝ) ≠ 0` using `by exact_mod_cast hr'0.ne'`. Establish `hr3 : (ramOverZ la : ℝ) ≠ 0` using `by exact_mod_cast hram.ne'`. Rewrite using `[hv1, hv2, he']`.

Use `push_cast`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Conclude with `ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hy₁ hφy) hzT`.
-/
theorem exists_isIntPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), IntAll Xo c → Ref.UnifAll Xo c → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∃ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr hInt hUnif A p _ z ev hz hv hG
  obtain ⟨hc1, hc2, -, -⟩ := hG
  have hzL : ∀ i, z i ∈ IntermediateField.adjoin ℚ_[p] (Set.range z) := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have := Pt.finite_adjoin z
  obtain ⟨T₀, j, hfin, hpm, hL, hnorm⟩ := Pt.exists_cdvr (IntermediateField.adjoin ℚ_[p] (Set.range z))
  have hev : ∀ x : A, ∃ a, j a = ev x := fun x => hL _ (Pt.hasVal_mem hzL (hv x))
  choose f hf using hev
  have hinj : Function.Injective j := j.injective
  let ev₀ : A →+* T₀.Fr :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hf, map_add, map_add, hf, hf]) }
  have hev₀ : ∀ x, j (ev₀ x) = ev x := hf
  let cA : c.F →+* A := Or.𝔐.cst.codRestrict A hc1
  let io₀ : c.F →+* T₀.Fr := ev₀.comp cA
  obtain ⟨la, e₀, ho₀, hpla⟩ := GlobalTheory.PartnerIn.exists_overLa T₀ io₀ (Fact.out : p.Prime) hpm
  obtain ⟨q, φq, yq, hyq, hφA⟩ := hc2
  letI a0 : Algebra c.F T₀.Fr := io₀.toAlgebra
  letI aΩ : Algebra c.F RM.Ω := Small.cstAlg Or
  let ψ₀ : q.R →ₐ[c.F] T₀.Fr :=
    { ev₀.comp (φq.toRingHom.codRestrict A hφA) with
      commutes' := fun a => by
        show ev₀ _ = ev₀ (cA a)
        exact congrArg ev₀ (Subtype.ext (φq.commutes a)) }
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c q.R yq T₀.Fr ψ₀
  obtain ⟨T', io', e', y', ho', hy', φ, z₁, t, -, hφy, hb⟩ := hInt la T₀ io₀ e₀ ho₀ hfin y₁
  obtain ⟨T, φV, φ₂, r, yy, τ, hfe, hbc, hyA, hτ⟩ := hUnif la T' io' e' ho' y' hy'
  letI a1 : Algebra c.F T'.Fr := io'.toAlgebra
  letI a2 : Algebra c.F T.Fr := (φ₂.comp io').toAlgebra
  let φ₂A : T'.Fr →ₐ[c.F] T.Fr := { φ₂ with commutes' := fun _ => rfl }
  obtain ⟨zT, hzT⟩ := GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c T'.Fr z₁ T.Fr φ₂A
  have hFB := frBorBC T'.Fr T.Fr φ₂A t z₁ y'.1 zT yy.1 hb hzT hbc
  refine ⟨la, T, φ₂.comp io', r * e', yy, (φ₂.comp φ.toRingHom).comp ev₀, zT,
    fun i => Units.map (φ₂A : T'.Fr →* T.Fr) (t i), ?_⟩
  unfold FinRd.IsIntPt
  refine ⟨hpla, hfe.overLa ho', hyA, ⟨τ, hτ⟩, fun a h => ?_, fun x => ?_,
    ⟨q, φq, φ₂A.comp (φ.comp ψ₀), yq, hyq, ?_, fun r => ⟨hφA r, rfl⟩⟩, hFB⟩
  · show φ₂ (φ (ev₀ ⟨_, h⟩)) = φ₂ (io' a)
    have h1 : φ (io₀ a) = io' a := φ.commutes a
    rw [← h1]
    rfl
  · have hio : φ.toRingHom.comp io₀ = io' := RingHom.ext fun a => φ.commutes a
    have ho'' : OverLa la T'.V (φ.toRingHom.comp io₀) e' := by
      rw [hio]
      exact ho'
    obtain ⟨r', ⟨hr'0, hr'⟩, he'⟩ :=
      (GlobalTheory.ThetaValueIdentityCompare.overLa_iff ho₀ hfin φ.toRingHom e').1 ho''
    have hr0 := hfe.2.2.2.2.1
    have hram := FinRd.ram_pos hpla
    by_cases hx : ev₀ x = 0
    · have h1 : ev x = 0 := by rw [← hev₀ x, hx, map_zero]
      have h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x = 0 := by
        show φ₂ (φ (ev₀ x)) = 0
        rw [hx, map_zero, map_zero]
      rw [h1, norm_zero]
      unfold FinRd.absT
      rw [if_pos h2]
    · have h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x ≠ 0 := by
        show φ₂ (φ (ev₀ x)) ≠ 0
        exact (map_ne_zero φ₂).2 ((map_ne_zero φ).2 hx)
      rw [← hev₀ x, hnorm _ hx]
      unfold FinRd.absT
      rw [if_neg h2]
      have hv1 : vV T.V (((φ₂.comp φ.toRingHom).comp ev₀) x) = r * (r' * vV T₀.V (ev₀ x)) := by
        show vV T.V (φ₂ (φ (ev₀ x))) = _
        rw [hfe.2.2.2.2.2]
        congr 1
        exact hr' _ hx
      have hv2 : vV T₀.V ((p : ℕ) : T₀.Fr) = e₀ * ramOverZ la := by
        have h3 := ho₀.2 ((p : ℕ) : c.F)
        rw [map_natCast, Pt.vLa_p hpla] at h3
        exact h3
      have he0 : (e₀ : ℝ) ≠ 0 := by exact_mod_cast ho₀.1.ne'
      have hr1 : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
      have hr2 : (r' : ℝ) ≠ 0 := by exact_mod_cast hr'0.ne'
      have hr3 : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hram.ne'
      rw [hv1, hv2, he']
      push_cast
      congr 2
      field_simp
  · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hy₁ hφy) hzT

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
