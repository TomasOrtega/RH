import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioConjOfToricRatioConjugates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

/- English proof (translation)
Establish `h` using `SqNum.Model.gap_le D C i j τ`. Establish `h2` using `(GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1`. Establish `h4 : bigN D ≤ bigN D ^ 3` using `Nat.le_self_pow (by norm_num) _`. Unfold `kap`. Use linear arithmetic over natural numbers and integers.
-/
theorem kap_add_big (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ bigN D + 1) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := SqNum.Model.gap_le D C i j τ
  have h2 := (GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

/- English proof (translation)
Take `⟨a, b, c, d⟩` from `h`. Establish `: (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s` using `funext fun i => (e i).symm`. Conclude with `⟨a, b, this ▸ c, d⟩`.
-/
theorem isValChar_shift {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s s' : ℕ}
    {κ κ' : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E}
    (h : IsValChar φ s κ 𝔣 Q χ) (e : ∀ i, (κ i : ℤ) + s = κ' i + s') : IsValChar φ s' κ' 𝔣 Q χ := by
  obtain ⟨a, b, c, d⟩ := h
  have : (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s := funext fun i => (e i).symm
  exact ⟨a, b, this ▸ c, d⟩

/- English proof (translation)
Take `⟨w, hw, hφw⟩` from `hfd.2.2.2.2.2.2.2`. Use `GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_` and prove the remaining obligations. Establish `hs` using `Formalism.BasicNotions.Host.sqrtMinusD_sq D.host`. Establish `h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0` using `by linear_combination hs - hw`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases.

Rewrite using `[sub_eq_zero.1 h, hφw, hφw]`. Rewrite using `[eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]`.
-/
theorem cmPhi_comp_eq {D : D7} (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (τ τ' : D.what₂.Tau) :
    (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = (cmPhi D τ').comp (algebraMap D.host.K D.host.E) := by
  obtain ⟨w, hw, hφw⟩ := hfd.2.2.2.2.2.2.2
  refine GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0 := by linear_combination hs - hw
  rcases mul_eq_zero.1 h0 with h | h
  · rw [sub_eq_zero.1 h, hφw, hφw]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]

open Classical in

/- English proof (translation)
Use `haveI := hcm`. Establish `hU : UnramFin D.host.E` using `hfd.2.2.1`. Establish `hφ : IsCMType (cmPhi D)` using `hfd.2.2.2.2.2.2.1`. Establish `e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s` using `fun τ => (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm`. Establish `hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j)` using `isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e`.

Take `⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)), Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)` from `⟨_, rfl⟩`. Establish `hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j)` using `hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e`. Establish `hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q` using `hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t`. Establish `hQram` using `GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j`. Establish `hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q` using `fun q hq => by`.

Rewrite `hq` using `[hQdef]`. Conclude with `Finset.mem_image.1 hq`. Set `Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E)` to `fun q => if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0`. Establish `hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q` using `fun q hq => by`. Establish `h` using `hex q hq`.

Simplify using `only [Pq, dif_pos h]`. Conclude with `h.choose_spec`. Establish `hov : ∀ q ∈ Q, Over (Pq q) q` using `fun q hq => (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)`. Establish `htor` using `GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ`. Rewrite `htor` using `[Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one]`.

Establish `htor0` using `GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd …`. Simplify using `only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0`. Establish `hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t`. Rewrite using `[nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]`. Take `⟨k, hk, hko⟩` from `hL.xi_fin t`.

Establish `hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1` using `fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y`. Establish `hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1` using `fun u hu => by`. Establish `a` using `GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu`. Establish `hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅`. Simplify using `only [condQ, Finset.prod_empty, mul_one]`.

Conclude with `Ideal.mul_le_left`. Establish `b` using `GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u (hatOUnits_mono hle hu)`. Rewrite `a` using `[hnu, finPart_mul, b, one_mul]`. Conclude with `a`. Establish `hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker`.

Use `sup_le ?_ fun u hu' => hu u hu'` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `finPart_mul_inf (Lc.xiH t) a` as an intermediate fact. Rewrite `this` using `[hinf a, mul_one]`. Conclude with `this`.

Set `ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ` to `QuotientGroup.lift _ (finPart (Lc.xiH t)) hker`. Use `haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)`. Set `τ₀ : D.what₂.Tau` to `Classical.arbitrary _`. Establish `hK2 : Module.finrank ℚ D.host.K = 2` using `Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D`. Set `δ : D.host.K` to `⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩`.

Establish `hδ : δ ^ 2 = -(D.host.d : D.host.K)` using `Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)`. Take `⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩` from `hTR D.host.E D.host.K D.host.d δ ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1 (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv …`. Establish `e1 : T₀ = Λ₀ s` using `hT₀.unique htor0`. Establish `e2 : Tf ψ = Λ s` using `((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)`. Rewrite using `[← e1, ← e2]`.

Conclude with `hAlg ψ`.
-/
theorem ratio_algebraic (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (t : T) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ bigN D + 1) (Λ Λ₀ : ℂ → ℂ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) :
    IsAlgebraic ℚ (Λ s / Λ₀ s) := by
  haveI := hcm
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1
  have e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s := fun τ =>
    (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm
  have hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) :=
    isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) :=
    hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e
  have hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q := hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t
  have hQram := GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)

  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have htor0 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
    (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
  simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]

  obtain ⟨k, hk, hko⟩ := hL.xi_fin t
  have hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1 := fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y
  have hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1 := fun u hu => by
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a
  have hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker := by
    refine sup_le ?_ fun u hu' => hu u hu'
    rintro _ ⟨a, rfl⟩
    have := finPart_mul_inf (Lc.xiH t) a
    rw [hinf a, mul_one] at this
    exact this
  let ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ := QuotientGroup.lift _ (finPart (Lc.xiH t)) hker

  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  have hK2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩ := hTR D.host.E D.host.K D.host.d δ
    ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q
    (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv0
  have e1 : T₀ = Λ₀ s := hT₀.unique htor0
  have e2 : Tf ψ = Λ s :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)
  rw [← e1, ← e2]
  exact hAlg ψ

end GlobalTheory.RowEx.RatioField

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

/- English proof (translation)
Set `S : Set ℂ` to `⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)), {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}`. Establish `hS : S.Finite`. Use `Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t => (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩`. Rewrite using `[h1.unique h1', h2.unique h2']`.

Establish `hSa : ∀ z ∈ S, IsAlgebraic ℚ z`. Introduce `z hz`. Simplify using `only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz`. Take `⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩` from `hz`. Conclude with `ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀`.

Use `haveI : Finite S := hS.to_subtype`. Use `⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral, fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩` and prove the remaining obligations. Simplify using `only [S, Set.mem_iUnion, Set.mem_setOf_eq]`. Conclude with `⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩`.
-/
theorem inNF_ratios (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} [Finite T] {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl)) :
    InNF fun _ σ => ∀ i j, LRatiosIn G σ μ₀ i j := by
  let S : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)),
    {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t =>
      (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_
    rintro _ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩
    rw [h1.unique h1', h2.unique h2']
  have hSa : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩ := hz
    exact ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral,
    fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩
  simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩

/- English proof (translation)
Introduce `_ hTR hFD _`. Take `⟨CF0, hF⟩` from `hFD`. Use `⟨CF0, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x₀, hF⟩` from `hF ε CF hCF`. Use `⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hsc => ?_⟩` and prove the remaining obligations.

Establish `hRec : GlobalTheory.SqTop.Rec large₂` using `(GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hS.size, hS.host⟩`. Use `haveI : Finite T := hS.fin`. Establish `key : ∀ (sc : Consts) (G : GridData R.toLevCh sc), sc = ⟨1, CF, large₂.sc.b⟩ → InNF fun _ σ => ∀ i j, LRatiosIn G σ A.μ0 i j`. Introduce and unpack `sc G rfl`. Take `⟨hcm, -, hfd, hbc, -⟩` from `hF C0 le_rfl D large₂ he hx hRec T R.toLevCh A.μ0 hS.core.lev G`.

Conclude with `inNF_ratios hTR hS.core.lev G hcm hfd hbc`. Conclude with `key ch.sc ch.G hsc`.
-/
theorem nfRatio : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → NFRatio := by
  intro _ hTR hFD _
  obtain ⟨CF0, hF⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hsc => ?_⟩
  have hRec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hS.size, hS.host⟩
  haveI : Finite T := hS.fin
  have key : ∀ (sc : Consts) (G : GridData R.toLevCh sc), sc = ⟨1, CF, large₂.sc.b⟩ →
      InNF fun _ σ => ∀ i j, LRatiosIn G σ A.μ0 i j := by
    rintro sc G rfl
    obtain ⟨hcm, -, hfd, hbc, -⟩ := hF C0 le_rfl D large₂ he hx hRec T R.toLevCh A.μ0 hS.core.lev G
    exact inNF_ratios hTR hS.core.lev G hcm hfd hbc
  exact key ch.sc ch.G hsc

end GlobalTheory.RowEx.RatioField
