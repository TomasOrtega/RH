import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentStep
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsLE

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

/- English proof (translation)
Use `haveI : Fact PD.p.Prime := Fact.mk PD.hp`. Take `⟨hl11, hSet, h20w, h20η, h20S, -⟩` from `hB`. Take `⟨-, hsur, hsize, -, -, hnt, -⟩` from `hSet`. Establish `hl5 : 5 ≤ PD.p` using `by omega`. Establish `hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 2` using `hlen`.

Establish `hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hlen'` using `[h, Nat.sInf_empty]`. Conclude with `absurd hlen' (by norm_num)`.

Establish `h2mem` using `Nat.sInf_mem hne`. Rewrite `h2mem` using `[hlen']`. Establish `hnt1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1)`. Establish `e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1` using `by push_cast; ring`. Use `h2mem.2` as an intermediate fact.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hthc : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c`. Assume the negation of the conclusion as `h`. Establish `h1 : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}` using `⟨le_refl 1, by simpa using h⟩`. Use `Nat.sInf_le h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hup1 : up (c - 1) = false`. Rewrite `hdiff` using `[hup]`. Simplify using `using hdiff`. Establish `htyc : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.up (size c)`.

Simplify using `[arcOf, hup]`. Establish `hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1))`. Simplify using `[arcOf, hup1]`. Establish `hps0 : ps W 0 = qA W` using `by simp [ps]`. Establish `hnn : nnDen W (arcOf b w S η up size) c = qA W ^ size c`.

Unfold `nnDen prodTy`. Rewrite using `[hlen, Finset.prod_range_succ, Finset.prod_range_one]`. Simplify using `only [Nat.cast_zero, sub_zero, Nat.cast_one, htyc, hty1, hps0, pow_zero, mul_one]`. Establish `hthick : ∀ s < (arcOf b w S η up size).len c, ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick`. Introduce `s _`.

Use `show (if up (c - (s : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s : ZMod n))) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n)))).thick = true`. Apply the tactic sequence `split_ifs <;> rfl`. Take `⟨hf1, hf2⟩` from `hf`. Rewrite `hf1` using `[hnn]`. Take `⟨κ, x, hκx⟩` from `hf2 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)`.

Rewrite `hκx` using `[hnn]`. Express the relevant statement in the definitionally equal form `InFr W c (ps W 1 ^ (size (c - 1) + S)) (qA W ^ size c) _ at hκx`. Establish `hw1 : 1 ≤ size (c - 1)` using `by have := hsize (c - 1); omega`. Establish `hwle : size (c - 1) ≤ w` using `hnt (c - 1) hnt1`. Establish `hb1 : 1 ≤ b` using `by omega`.

Establish `hb₀1 : 1 ≤ size c` using `by have := hsize c; omega`. Take `⟨x'', hx''⟩` from `ArcLengthOneTwo.content_step W hcase hP9 hO c (size c) (size (c - 1) + S) κ (by omega) f x hf1 hκx`. Establish `hxE : ∀ z : O, algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) = algebraMap O W.EE z` using `fun z => (IsScalarTower.algebraMap_apply O (LetA O n) W.EE z).symm`. Establish `hlE : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k`. Introduce `k`.

Simplify using `[lA, lE]`. Establish `hg1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c) (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'')`. Rewrite using `[hnn]`. Take `⟨u₀, hu₀, e1⟩` from `hf1`. Use `⟨lA W ^ ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) * u₀ - qA W ^ size c * algebraMap O (LetA O n) x'', Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hu₀) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (GS.qA_mem W) _) (Sub …` and prove the remaining obligations.

Simplify using `only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e1 ⊢`. Take the linear combination `lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * e1`. Establish `hgdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs, (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs → InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c) (lE W (ArcLengthOneTwo.deA PD.p (size …`. Introduce `s hs bs hbs`. Rewrite `hs` using `[hlen]`.

Use `interval_cases s`. Simplify using `[htyc] at hbs`. Simplify using `only [Nat.cast_one, hty1, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs`. Substitute `hbs` using the available equality. Rewrite using `[hnn]`.

Conclude with `hx''`. Establish `hNg` using `liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ hg1 hgdown`. Take `⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩` from `constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5 hHF hArcL hW₁ hsur rr hkill hbb`. Establish `hC` using `liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL hW₁ hW₂ hsur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x''`. Establish `hCL` using `LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hC`.

Establish `hsum` using `LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hNg hCL`. Rewrite `hsum` using `[sub_add_cancel]`. Establish `hfin` using `ArcLengthOneTwo.lifts_lE W (arcOf b w S η up size) F c bb sol k₀ hsum`. Use `⟨ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) + (rr + (arcOf b w S η up size).σ PD.p), ?_, hfin⟩` and prove the remaining obligations. Establish `hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S`.

Unfold `Formalism.MainNotions.TruncatedSeriesCountingBounds.hB`. Rewrite using `[if_pos ⟨c, hthc⟩]`. Establish `hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η`. Rewrite using `[CaseA.sg_eq]`. Unfold `Formalism.MainNotions.N.Ln17.Sg`.

Rewrite using `[hhB]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hrr`, `hσ`, the goal using `[hSgeq]`. Take `⟨-, -, -, -, a5, a6, a7⟩` from `CaseA.sg_ge PD.p (b + η + S) w S η hl11 (by omega)`.

Establish `hde` using `ArcLengthOneTwo.deA_le (l := PD.p) (size c) (size (c - 1) + S) (by omega) hb₀1`. Apply the tactic sequence `have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num`. Establish `hηb : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb` using `mul_nonneg (Nat.cast_nonneg _) hband0`. Establish `hlr1 : (1 : ℝ) < PD.p` using `by exact_mod_cast (by omega : 1 < PD.p)`. Establish `hlr0 : (0 : ℝ) < PD.p` using `by linarith`.

Use `push_cast`. Distinguish the cases in `h1c : PD.p * (size (c - 1) + S) ≤ size c`. Establish `hc1` using `case1c PD.p hl11 b w (size (c - 1)) S η (size c) hb1 h20η h20S h20w hwle hthc.1 hthc.2 h1c (Nat.le_of_not_lt hnb) (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) : ℝ) (by push_cast at hde; exact hde)`. Establish `hBand : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb` using `⟨c - 1, hnt1, Or.inl (by rw [sub_add_cancel]; exact hthc), by rw [hhB]; exact hc1.2 Cb hCb⟩`. Establish `hbandI : bandI PD.p b w S η size Cb = 1` using `by unfold bandI; rw [if_pos hBand]`.

Rewrite using `[hbandI]`. Combine the linear relations using `[hc1.1]`. Establish `hlt : (size c : ℝ) / PD.p < (size (c - 1) : ℝ) + S`. Rewrite using `[div_lt_iff₀ hlr0]`. Establish `: size c < PD.p * (size (c - 1) + S)` using `Nat.lt_of_not_le h1c`.

Establish `hr : ((size c : ℕ) : ℝ) < ((PD.p * (size (c - 1) + S) : ℕ) : ℝ)` using `by exact_mod_cast this`. Move the coercions through the operations in `at hr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog0 : 0 ≤ Real.logb PD.p (size c : ℝ)` using `Real.logb_nonneg hlr1 (by exact_mod_cast hb₀1)`. Establish `hlogle : Real.logb PD.p (size c : ℝ) ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ))`.

Apply `Real.logb_le_logb_of_le hlr1 (by exact_mod_cast (by omega : 0 < size c))` to reduce the goal to its premises. Establish `: (size c : ℝ) ≤ b + η` using `by exact_mod_cast hthc.2`. Use `push_cast`. Establish `: (0 : ℝ) ≤ S` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmax : max 0 ((size c : ℝ) / PD.p - ((size (c - 1) + S : ℕ) : ℝ) + 2 + Real.logb PD.p (size c)) ≤ 2 + Real.logb PD.p (size c)`. Use `push_cast`. Conclude with `max_le (by linarith) (by linarith)`. Establish `hη0 : (0 : ℝ) ≤ η * (PD.p : ℝ)⁻¹` using `mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hlr0.le)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arc_length_one_or_two_case_c [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = true) (hnb : ¬ (PD.p * (size (c - 1) + S + η) + η < size c)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  haveI : Fact PD.p.Prime := Fact.mk PD.hp
  obtain ⟨hl11, hSet, h20w, h20η, h20S, -⟩ := hB
  obtain ⟨-, hsur, hsize, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 2 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    exact absurd hlen' (by norm_num)
  have h2mem := Nat.sInf_mem hne
  rw [hlen'] at h2mem
  have hnt1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    have := h2mem.2
    rwa [e] at this
  have hthc : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra h
    have h1 : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨le_refl 1, by simpa using h⟩
    have := Nat.sInf_le h1
    omega
  have hup1 : up (c - 1) = false := by
    rw [hup] at hdiff; simpa using hdiff
  have htyc : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.up (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1)) := by
    simp [arcOf, hup1]
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hnn : nnDen W (arcOf b w S η up size) c = qA W ^ size c := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one, htyc, hty1, hps0, pow_zero, mul_one]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    show (if up (c - (s : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n)))).thick = true
    split_ifs <;> rfl

  obtain ⟨hf1, hf2⟩ := hf
  rw [hnn] at hf1
  obtain ⟨κ, x, hκx⟩ := hf2 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)
  rw [hnn] at hκx
  change InFr W c (ps W 1 ^ (size (c - 1) + S)) (qA W ^ size c) _ at hκx
  have hw1 : 1 ≤ size (c - 1) := by have := hsize (c - 1); omega
  have hwle : size (c - 1) ≤ w := hnt (c - 1) hnt1
  have hb1 : 1 ≤ b := by omega
  have hb₀1 : 1 ≤ size c := by have := hsize c; omega

  obtain ⟨x'', hx''⟩ := ArcLengthOneTwo.content_step W hcase hP9 hO c (size c) (size (c - 1) + S) κ (by omega) f x
    hf1 hκx
  have hxE : ∀ z : O, algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) = algebraMap O W.EE z :=
    fun z => (IsScalarTower.algebraMap_apply O (LetA O n) W.EE z).symm
  have hlE : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
    intro k; simp [lA, lE]
  have hg1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c)
      (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
        algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    rw [hnn]
    obtain ⟨u₀, hu₀, e1⟩ := hf1
    refine ⟨lA W ^ ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) * u₀ - qA W ^ size c * algebraMap O (LetA O n) x'',
      Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hu₀)
        (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (GS.qA_mem W) _) (Subalgebra.algebraMap_mem _ _)), ?_⟩
    simp only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e1 ⊢
    linear_combination lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * e1
  have hgdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c)
        (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
          algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp [htyc] at hbs
    · simp only [Nat.cast_one, hty1, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hx''

  have hNg := liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ hg1 hgdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hsur rr hkill hbb
  have hC := liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hW₁ hW₂ hsur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x''
  have hCL := LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hC
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hNg hCL
  rw [sub_add_cancel] at hsum
  have hfin := ArcLengthOneTwo.lifts_lE W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) + (rr + (arcOf b w S η up size).σ PD.p), ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hthc⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [CaseA.sg_eq]; unfold Formalism.MainNotions.N.Ln17.Sg; rw [hhB]; push_cast; ring
  rw [hSgeq] at hrr hσ ⊢
  obtain ⟨-, -, -, -, a5, a6, a7⟩ := CaseA.sg_ge PD.p (b + η + S) w S η hl11 (by omega)
  have hde := ArcLengthOneTwo.deA_le (l := PD.p) (size c) (size (c - 1) + S) (by omega) hb₀1
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hηb : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) hband0
  have hlr1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hlr0 : (0 : ℝ) < PD.p := by linarith
  push_cast
  by_cases h1c : PD.p * (size (c - 1) + S) ≤ size c
  · have hc1 := case1c PD.p hl11 b w (size (c - 1)) S η (size c) hb1 h20η h20S h20w hwle hthc.1 hthc.2 h1c
      (Nat.le_of_not_lt hnb) (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) : ℝ) (by push_cast at hde; exact hde)
    have hBand : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb :=
      ⟨c - 1, hnt1, Or.inl (by rw [sub_add_cancel]; exact hthc), by rw [hhB]; exact hc1.2 Cb hCb⟩
    have hbandI : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hBand]
    rw [hbandI]
    linarith [hc1.1]
  · have hlt : (size c : ℝ) / PD.p < (size (c - 1) : ℝ) + S := by
      rw [div_lt_iff₀ hlr0]
      have : size c < PD.p * (size (c - 1) + S) := Nat.lt_of_not_le h1c
      have hr : ((size c : ℕ) : ℝ) < ((PD.p * (size (c - 1) + S) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hr
      linarith
    have hlog0 : 0 ≤ Real.logb PD.p (size c : ℝ) := Real.logb_nonneg hlr1 (by exact_mod_cast hb₀1)
    have hlogle : Real.logb PD.p (size c : ℝ) ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) := by
      apply Real.logb_le_logb_of_le hlr1 (by exact_mod_cast (by omega : 0 < size c))
      have : (size c : ℝ) ≤ b + η := by exact_mod_cast hthc.2
      push_cast
      have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      linarith
    have hmax : max 0 ((size c : ℝ) / PD.p - ((size (c - 1) + S : ℕ) : ℝ) + 2 + Real.logb PD.p (size c)) ≤
        2 + Real.logb PD.p (size c) := by
      push_cast
      exact max_le (by linarith) (by linarith)
    have hη0 : (0 : ℝ) ≤ η * (PD.p : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hlr0.le)
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
