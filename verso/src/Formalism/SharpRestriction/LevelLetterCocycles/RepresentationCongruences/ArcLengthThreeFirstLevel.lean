import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftMapEqPrimePowSmul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.NumericBoundExponentEg
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypFirst
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypSecond
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsCyclotomicCharQuotient

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
Use `set A := arcOf b w S η up size with hAdef`. Establish `hB'` using `hB`. Take `⟨hp11, hSet, hwb, hηb, hSb, -⟩` from `hB'`. Take `⟨-, hSur, hηs, hJA, -, hnt, -⟩` from `hSet`. Establish `hl5 : 5 ≤ PD.p` using `by omega`.

Establish `hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3` using `hlen`. Establish `hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hlen'` using `[hcon, Nat.sInf_empty]`.

Use linear arithmetic over natural numbers and integers. Establish `hm2` using `Nat.notMem_of_lt_sInf (s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}) (m := 2) (by rw [hlen']; norm_num)`. Establish `e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1` using `by push_cast; ring`. Establish `hT1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1)`. Assume the negation of the conclusion as `hcon`.

Conclude with `hm2 ⟨by norm_num, by rw [e2]; exact hcon⟩`. Establish `hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S`. Unfold `Formalism.MainNotions.TruncatedSeriesCountingBounds.hB`. Rewrite using `[if_pos ⟨c - 1, hT1⟩]`. Establish `eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η`.

Rewrite using `[show Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η from rfl, hhB]`. Establish `e21 : c - 2 + 1 = c - 1` using `by ring`. Establish `hup1 : up (c - 1) = true`. Use `(halt (c - 2)).1` as an intermediate fact. Rewrite `this` using `[e21, hD]`.

Apply the tactic sequence `cases h : up (c - 1) <;> simp_all`. Establish `hty : ∀ i, A.ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i)` using `fun i => rfl`. Establish `hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1))` using `by rw [hty, hup1]; rfl`. Establish `hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 2))` using `by rw [hty, hD]; rfl`. Establish `hb1 : 1 ≤ b` using `by have := hηs (c - 1); have := hT1.2; omega`.

Establish `hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 (size (c - 1))` using `hk₀ 1 (by rw [hlen]; norm_num) (size (c - 1)) (by rw [Nat.cast_one]; exact hty1)`. Establish `hH1 : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s = algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam)` using `fun s hs => arc_length_three_hyp_first W hcase hl5 hArc hFL A hOK c hc hlen rfl hty1 hty2 hW₂ bb sol hbb k₀ hFil lam hlam κ Hh hHh h4a s hs`. Establish `hR` using `GS.ringData_of_caseA_of_p9 W hcase hP9`. Establish `hqU : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)))`. Rewrite using `[map_pow]`.

Conclude with `(GS.isUnit_qA hR).pow _`. Take `⟨uq, huq⟩` from `hqU`. Use `set s₀ : W.EE := ((uq⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) with hs₀`. Establish `hs₀eq : algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s₀ = algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S))`. Rewrite using `[hs₀, ← huq, ← mul_assoc, Units.mul_inv, one_mul]`.

Establish `huniq : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s = algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → s = s₀`. Introduce `s hs`. Establish `h` using `hs.trans hs₀eq.symm`. Rewrite `h` using `[← huq]`. Conclude with `(Units.mul_right_inj uq).1 h`.

Set `Mi' : ZMod n → ℕ` to `fun i => if up i then η else size i + S`. Set `hi' : ZMod n → ℕ` to `fun i => if up i then size i + S else η`. Establish `hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi'`. Introduce `i τ hτ a ha`. Establish `h1` using `hJA i τ hτ a ha`.

Establish `h2` using `hηs i`. Consider the cases of `hu : up i`. Simplify using `only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hAS : A.S = S` using `rfl`. Establish `hAη : A.η = η` using `rfl`.

Establish `hAG : A.G₀ = w + S` using `rfl`. Establish `hJ₂ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi'`. Introduce `τ i hτ a ha`. Establish `h1` using `hW₂.2 i τ hτ a ha`. Establish `h2` using `hηs i`.

Rewrite `h1` using `[hty i]`. Consider the cases of `hu : up i`. Simplify using `only [hu, Mi', hi', Bool.false_eq_true, if_false, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hu, Mi', hi', if_true, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hwid : ∀ i, Mi' i + hi' i = size i + S + η`. Introduce `i`.

Apply the tactic sequence `cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega`. Establish `hsz : ∀ i, size i ≤ b + η`. Introduce `i`. Distinguish the cases in `ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i`. Conclude with `ht.2`.

Use `hnt i ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ b + 2 * η + S` using `Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega`. Take `⟨-, hKA, -, hKr, -, -, hAr, -⟩` from `hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)`. Use `set Ai := Formalism.MainNotions.LiftingTheory.AI W F (c - 1) with hAidef`.

Use `set ri := Formalism.MainNotions.LiftingTheory.rI W F (c - 1) with hridef`. Use `set b₁ := size (c - 1) with hb₁def`. Establish `hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) = (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ)` using `rfl`. Rewrite `hAr` using `[hcW]`. Establish `hsm' : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η ≤ (b : ℝ) / 4` using `by rw [← eSg]; exact hsm`.

Establish `hk6` using `numeric_bound_two_a_le_b1 PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hHle hsm' ((Ai + ri : ℕ) : ℝ) hAr`. Establish `hb : 2 * (Ai + ri) + η + 1 ≤ b₁`. Establish `: ((2 * (Ai + ri) + η + 1 : ℕ) : ℝ) ≤ b₁` using `by push_cast at hk6 ⊢; linarith`. Conclude with `this` after adjusting the coercions. Establish `hE` using `numeric_bound_exponent_eg PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hT1.2 hHle (Ai + ri) hAr`.

Establish `hl0 : ((PD.p : ℕ) : O) ≠ 0` using `GS.p_ne_zero W`. Use `haveI : CharZero O := charZero_of_prime_ne_zero W hO hl0`. Establish `hA4` using `gamma_q_expansion_of_points W hcase hP9 hO hOv hinj Pt hPtEx`. Take `⟨dop₁, hd₁⟩` from `exists_gamma_sub_one_div_pi0 W hP9 hcase T₁`. Take `⟨dop₂, hd₂⟩` from `exists_gamma_sub_one_div_pi0 W hP9 hcase T₂`.

Take `⟨cc, hcc⟩` from `exists_cyclotomic_char_quotient W hcase hOv hinj`. Establish `hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ (c - 1) ((Set.Icc (b₁ : ℤ) (b₁ + S)) ∪ Set.Icc (-(η : ℤ)) η)`. Use `hJA (c - 1)` as an intermediate fact. Rewrite `this` using `[hup1, if_pos rfl]`. Conclude with `this`.

Establish `hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (qA W ^ (Ai + ri) • y) → Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (Polynomial.aeval dop₁ (TruncatedCoefficientPoly cc b₁ S η (Ai + ri)) y)`. Break down `Nat.eq_zero_or_pos (Ai + ri) with h0 | hpos` into its components or cases. Introduce `y hy`. Rewrite `hy` using `[h0, pow_zero, one_smul]`. Establish `h1 : TruncatedCoefficientPoly cc b₁ S η (Ai + ri) = 1` using `by rw [h0]; simp [TruncatedCoefficientPoly, TruncationIndexSet]`.

Rewrite using `[h1, map_one]`. Conclude with `hy`. Use `hC4 hcase T₁ hW₁.1 (c - 1) (Ai + ri) hpos dop₁ hd₁ cc hcc (TruncationIndexSet b₁ S η (Ai + ri)) (fun τ a j hτ ha hj1 hj2 => ?_)` and prove the remaining obligations. Establish `hmem` using `hU τ hτ a ha`. Use `Finset.mem_image.2 ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, Finset.mem_Icc.2 ⟨by dsimp only; exact_mod_cast hj1, by dsimp only; exact_mod_cast hj2⟩⟩, rfl⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_union, Set.mem_Icc] at hmem`. Simplify using `only [winU, Finset.mem_union, Finset.mem_Icc]`. Conclude with `hmem`. Establish `hs' : ps W 1 ^ (size (c - 2) + S) ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k}` using `Submonoid.pow_mem _ (Submonoid.subset_closure (show ps W 1 ∈ {x | ∃ k ≥ 1, x = ps W k} from ⟨1, le_rfl, rfl⟩)) _`. Establish `hM1 : Mi' (c - 2) = size (c - 2) + A.S` using `by simp only [Mi', hD, Bool.false_eq_true, if_false]; rfl`.

Establish `hM2 : Mi' (c - 1) = A.η` using `by simp only [Mi', hup1, if_true]; rfl`. Establish `hAh : A.h = b + η + S` using `hhB`. Establish `hN : b₁ + (Ai + ri) + A.η ≤ (PD.p - 1) * A.M PD.p`. Establish `h1` using `Nat.lt_mul_div_succ (2 * A.h) (show 0 < PD.p - 1 by omega)`. Establish `h2 : A.M PD.p = 2 * A.h / (PD.p - 1) + 1` using `rfl`.

Rewrite using `[h2, hAη]`. Use `hT1.2` as an intermediate fact. Generalize the expression as in `(PD.p - 1) * (2 * A.h / (PD.p - 1) + 1) = Z at h1 ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hM : 1 ≤ A.M PD.p` using `by show 1 ≤ 2 * A.h / (PD.p - 1) + 1`.

Conclude with `Nat.le_add_left _ _`. Establish `hH2` using `arc_length_three_hyp_second W hcase hP9 hP5 A c hlen hW₂.1 Mi' hi' hJ₂ hM1 hM2 hN hM lam hlamγ s₀ hs₀eq`. Take `⟨x₁, hx₁, hmap⟩` from `existsLiftMapEqPrimePowSmul W hcase hP9 (c - 1) F hSur hW₁.1 hW₂.1 Ai ri hKA hKr b₁ S η hU hb (gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9) (fun k hk => gamma_level_eq_mul W hcase hP9 k hk) hA4 hl0 hO hOv hinj (gamma_sub_self_mem_pi0_lattice W hP9 hcase (c - 1) T₁ hW₁.1) …`. Use `⟨x₁, EG PD.p (Ai + ri) S η b₁, hx₁, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[eSg]`.

Conclude with `hE`. Take `rfl` from `huniq s hs`. Conclude with `⟨hH1 s₀ hs₀eq, hmap⟩`.
-/
theorem arc_length_three_first_level [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh))) :
    ∃ (n₁ : W.DD T₁) (E : ℕ), Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁ ∧ (E : ℝ) ≤ 8 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
        algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam) := by
  classical
  set A := arcOf b w S η up size with hAdef
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB'
  obtain ⟨-, hSur, hηs, hJA, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Nat.sInf_empty] at hlen'
    omega
  have hm2 := Nat.notMem_of_lt_sInf (s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)})
    (m := 2) (by rw [hlen']; norm_num)
  have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
  have hT1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hcon
    exact hm2 ⟨by norm_num, by rw [e2]; exact hcon⟩
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c - 1, hT1⟩]
  have eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [show Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size =
      Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η from rfl, hhB]
  have e21 : c - 2 + 1 = c - 1 := by ring
  have hup1 : up (c - 1) = true := by
    have := (halt (c - 2)).1; rw [e21, hD] at this
    cases h : up (c - 1) <;> simp_all
  have hty : ∀ i, A.ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
    fun i => rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by rw [hty, hup1]; rfl
  have hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 2)) := by rw [hty, hD]; rfl
  have hb1 : 1 ≤ b := by have := hηs (c - 1); have := hT1.2; omega

  have hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 (size (c - 1)) :=
    hk₀ 1 (by rw [hlen]; norm_num) (size (c - 1)) (by rw [Nat.cast_one]; exact hty1)
  have hH1 : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) :=
    fun s hs => arc_length_three_hyp_first W hcase hl5 hArc hFL A hOK c hc hlen rfl hty1 hty2 hW₂ bb sol hbb k₀ hFil lam hlam κ Hh
      hHh h4a s hs

  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ size (c - 1))) := by
    rw [map_pow]; exact (GS.isUnit_qA hR).pow _
  obtain ⟨uq, huq⟩ := hqU
  set s₀ : W.EE := ((uq⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) with hs₀
  have hs₀eq : algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s₀ =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) := by
    rw [hs₀, ← huq, ← mul_assoc, Units.mul_inv, one_mul]
  have huniq : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → s = s₀ := by
    intro s hs
    have h := hs.trans hs₀eq.symm
    rw [← huq] at h
    exact (Units.mul_right_inj uq).1 h

  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hAS : A.S = S := rfl
  have hAη : A.η = η := rfl
  have hAG : A.G₀ = w + S := rfl
  have hJ₂ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi' := by
    intro τ i hτ a ha
    have h1 := hW₂.2 i τ hτ a ha
    have h2 := hηs i
    rw [hty i] at h1
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union,
        Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢
      push_cast
      omega
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ b + 2 * η + S :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨-, hKA, -, hKr, -, -, hAr, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  set Ai := Formalism.MainNotions.LiftingTheory.AI W F (c - 1) with hAidef
  set ri := Formalism.MainNotions.LiftingTheory.rI W F (c - 1) with hridef
  set b₁ := size (c - 1) with hb₁def
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) = (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  rw [hcW] at hAr
  have hsm' : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η ≤ (b : ℝ) / 4 := by rw [← eSg]; exact hsm
  have hk6 := numeric_bound_two_a_le_b1 PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hHle hsm' ((Ai + ri : ℕ) : ℝ) hAr
  have hb : 2 * (Ai + ri) + η + 1 ≤ b₁ := by
    have : ((2 * (Ai + ri) + η + 1 : ℕ) : ℝ) ≤ b₁ := by push_cast at hk6 ⊢; linarith
    exact_mod_cast this
  have hE := numeric_bound_exponent_eg PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hT1.2 hHle (Ai + ri) hAr

  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := GS.p_ne_zero W
  haveI : CharZero O := charZero_of_prime_ne_zero W hO hl0
  have hA4 := gamma_q_expansion_of_points W hcase hP9 hO hOv hinj Pt hPtEx
  obtain ⟨dop₁, hd₁⟩ := exists_gamma_sub_one_div_pi0 W hP9 hcase T₁
  obtain ⟨dop₂, hd₂⟩ := exists_gamma_sub_one_div_pi0 W hP9 hcase T₂
  obtain ⟨cc, hcc⟩ := exists_cyclotomic_char_quotient W hcase hOv hinj
  have hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ (c - 1) ((Set.Icc (b₁ : ℤ) (b₁ + S)) ∪ Set.Icc (-(η : ℤ)) η) := by
    have := hJA (c - 1)
    rw [hup1, if_pos rfl] at this
    exact this
  have hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (Polynomial.aeval dop₁ (TruncatedCoefficientPoly cc b₁ S η (Ai + ri)) y) := by
    rcases Nat.eq_zero_or_pos (Ai + ri) with h0 | hpos
    · intro y hy
      rw [h0, pow_zero, one_smul] at hy
      have h1 : TruncatedCoefficientPoly cc b₁ S η (Ai + ri) = 1 := by rw [h0]; simp [TruncatedCoefficientPoly, TruncationIndexSet]
      rw [h1, map_one]
      exact hy
    · refine hC4 hcase T₁ hW₁.1 (c - 1) (Ai + ri) hpos dop₁ hd₁ cc hcc (TruncationIndexSet b₁ S η (Ai + ri))
        (fun τ a j hτ ha hj1 hj2 => ?_)
      have hmem := hU τ hτ a ha
      refine Finset.mem_image.2 ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_,
        Finset.mem_Icc.2 ⟨by dsimp only; exact_mod_cast hj1, by dsimp only; exact_mod_cast hj2⟩⟩, rfl⟩
      simp only [Set.mem_union, Set.mem_Icc] at hmem
      simp only [winU, Finset.mem_union, Finset.mem_Icc]
      exact hmem
  have hs' : ps W 1 ^ (size (c - 2) + S) ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k} :=
    Submonoid.pow_mem _ (Submonoid.subset_closure (show ps W 1 ∈ {x | ∃ k ≥ 1, x = ps W k} from ⟨1, le_rfl, rfl⟩)) _

  have hM1 : Mi' (c - 2) = size (c - 2) + A.S := by simp only [Mi', hD, Bool.false_eq_true, if_false]; rfl
  have hM2 : Mi' (c - 1) = A.η := by simp only [Mi', hup1, if_true]; rfl
  have hAh : A.h = b + η + S := hhB
  have hN : b₁ + (Ai + ri) + A.η ≤ (PD.p - 1) * A.M PD.p := by
    have h1 := Nat.lt_mul_div_succ (2 * A.h) (show 0 < PD.p - 1 by omega)
    have h2 : A.M PD.p = 2 * A.h / (PD.p - 1) + 1 := rfl
    rw [h2, hAη]
    have := hT1.2
    generalize (PD.p - 1) * (2 * A.h / (PD.p - 1) + 1) = Z at h1 ⊢
    omega
  have hM : 1 ≤ A.M PD.p := by
    show 1 ≤ 2 * A.h / (PD.p - 1) + 1
    exact Nat.le_add_left _ _
  have hH2 := arc_length_three_hyp_second W hcase hP9 hP5 A c hlen hW₂.1 Mi' hi' hJ₂ hM1 hM2 hN hM lam hlamγ s₀ hs₀eq

  obtain ⟨x₁, hx₁, hmap⟩ := existsLiftMapEqPrimePowSmul W hcase hP9 (c - 1) F hSur hW₁.1 hW₂.1 Ai ri hKA hKr b₁ S η hU hb
    (gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9) (fun k hk => gamma_level_eq_mul W hcase hP9 k hk) hA4 hl0 hO hOv hinj
    (gamma_sub_self_mem_pi0_lattice W hP9 hcase (c - 1) T₁ hW₁.1) (gamma_sub_self_mem_pi0_lattice W hP9 hcase (c - 1) T₂ hW₂.1)
    dop₁ hd₁ dop₂ hd₂ cc hcc hCONS s₀ (ps W 1 ^ (size (c - 2) + S)) hs' hs₀eq lam (hH1 s₀ hs₀eq) hH2
  refine ⟨x₁, EG PD.p (Ai + ri) S η b₁, hx₁, ?_, fun s hs => ?_⟩
  · rw [eSg]; exact hE
  · obtain rfl := huniq s hs
    exact ⟨hH1 s₀ hs₀eq, hmap⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
