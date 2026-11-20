import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PhiSqPi0PowPowerSeries
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Numerics

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
Establish `hpF : Fact PD.p.Prime` using `⟨PD.hp⟩`. Take `⟨hp11, hSet, hw20, hη20, hS20, -⟩` from `hB`. Take `⟨-, hSur, hηs, hJ, -, hnt, hJL⟩` from `hSet`. Establish `hl5 : 5 ≤ PD.p` using `by omega`. Take `⟨hTc, hTc1, hTc2⟩` from `ArcLengthThreeFiltration.arc_len_three_thick_letters hlen`.

Take `⟨hu1, hu0⟩` from `ArcLengthThreeFiltration.arc_types halt hD`. Establish `hty1 : (arcOf b w S η up size).ty (c - 1) = .up (size (c - 1))` using `by simp [ArcLengthThreeFiltration.arc_ty, hu1]`. Establish `hty2 : (arcOf b w S η up size).ty (c - 2) = .down (size (c - 2))` using `by simp [ArcLengthThreeFiltration.arc_ty, hD]`. Establish `hty0 : (arcOf b w S η up size).ty c = .down (size c)` using `by simp [ArcLengthThreeFiltration.arc_ty, hu0]`. Establish `hw' : size (c - 2) ≤ w` using `hnt _ hTc2`.

Establish `hηw' : η < size (c - 2)` using `hηs _`. Establish `hb₁b : b ≤ size (c - 1)` using `hTc1.1`. Establish `hb₁b' : size (c - 1) ≤ b + η` using `hTc1.2`. Establish `hAh : (arcOf b w S η up size).h = b + η + S` using `by show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S`. Unfold `Formalism.MainNotions.TruncatedSeriesCountingBounds.hB`.

Rewrite using `[if_pos ⟨c, hTc⟩]`. Establish `hj2 : (arcOf b w S η up size).j ≤ 2` using `by show 1 ≤ 2; norm_num`. Establish `h2l : 2 ≤ (arcOf b w S η up size).len c` using `by rw [hlen]; norm_num`. Establish `hT₁ : IsCrys PD T₁.ρ` using `hW₁.1`. Establish `hT₂ : IsCrys PD T₂.ρ` using `hW₂.1`.

Take `⟨Br⟩` from `exists_phiBridge W hcase hP9 T₁ hT₁ hO hinj`. Take `⟨-, hqu, hΔu⟩` from `lemG_units W hcase hP9 hT₁ hO hOv hinj`. Establish `hpu : IsUnit (algebraMap (LetA O n) W.EE (ps W 1))`. Establish `e : algebraMap (LetA O n) W.EE (ps W 1) = W.φE (algebraMap (LetA O n) W.EE (qA W))`. Rewrite using `[W.φE_ext]`.

Use `show _ = algebraMap (LetA O n) W.EE (W.φA (qA W))`. Unfold `ps`. Rewrite using `[pow_one]`. Rewrite using `[e]`. Conclude with `hqu.map W.φE`.

Establish `hXu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst PowerSeries.X))` using `Br.qA_eq ▸ hqu`. Establish `hPu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst (Br.P.p 1)))` using `(ArcLengthThreeFiltration.ps_cst Br 1) ▸ hpu`. Establish `hπ₀mem : W.π₀ ∈ W.AΔ` using `(qA_mem_AΔ W hcase hP9 hT₁).1`. Take `⟨-, hACT⟩` from `hArc hcase hl5 _ hOK c hc 2 hj2 h2l`. Take `⟨-, hAC3₂, -, hfr₂⟩` from `hACT T₂ hW₂`.

Take `⟨-, -, -, -, hAC9₂, -, -⟩` from `hfr₂ d bb sol hbb`. Take `⟨d₁, b₁, sol₁, hb₁⟩` from `hHF hcase hl5 _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))`. Take `⟨-, hAC3₁, -, hfr₁⟩` from `hACT T₁ hW₁`. Take `⟨⟨hli₁, -⟩, -, -, hAC8₁, -, -, -⟩` from `hfr₁ d₁ b₁ sol₁ hb₁`. Take `⟨-, μ, hμ, hRep⟩` from `hSec hcase hl5 _ hOK c hc 2 hj2 h2l T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d bb sol hbb`.

Establish `hFL₁` using `hFL hcase hl5 _ hOK c hc 2 hj2 h2l T₁ hW₁ d₁ b₁ sol₁ hb₁`. Establish `hFL₂` using `hFL hcase hl5 _ hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb`. Establish `ha1 : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n) = c - 1`. Rewrite using `[hlen]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hΛ : abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2 = Br.cst (PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S))`. Rewrite using `[ArcLengthThreeFiltration.lam_inner W hlen, ArcLengthThreeFiltration.ps_cst Br, ArcLengthThreeFiltration.ps_cst Br, ArcLengthThreeFiltration.p_zero, hAh, Br.cst_mul, Br.cst_pow, Br.cst_pow]`. Both sides reduce to the same expression. Use `set a := c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n) with ha`.

Establish `ha0 : a - ((0 : ℕ) : ZMod n) = c - 1` using `by rw [ha1]; simp`. Establish `ha2 : a - ((1 : ℕ) : ZMod n) = c - 2` using `by rw [ha1]; push_cast; ring`. Establish `ha3 : a + 1 = c` using `by rw [ha1]; ring`. Establish `hΛmem : abelian₂ W (arcOf b w S η up size) a 2 ∈ W.AΔ` using `by rw [hΛ]; exact Br.cst_mem _`. Establish `hΛu : IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W (arcOf b w S η up size) a 2))`.

Rewrite using `[hΛ, Br.cst_mul, Br.cst_pow, Br.cst_pow, map_mul, map_pow, map_pow]`. Conclude with `(hXu.pow _).mul (hPu.pow _)`. Establish `hℓa : dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 (size (c - 1))`. Establish `h1` using `hk₀ 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)`. Rewrite `h1` using `[hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthThreeFiltration.dv_succ, show FilS W T₂ c 1 (size (c - 1)) = FilS W T₂ (a + 1) 1 (size (c - 1)) by rw [ha3]]`.

Rewrite using `[ArcLengthThreeFiltration.dvO_single]`. Conclude with `ArcLengthThreeFiltration.filS_zero_of W T₂ a _ _ h1`. Establish `hℓa1 : dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 1 (-((size (c - 2) + S : ℕ) : ℤ))`. Use `(hFL₂ (Pi.single k₀ 1) 1 (by norm_num)).1 _ ?_` and prove the remaining obligations. Rewrite using `[ha2, hty2]`.

Introduce `x hx`. Simplify using `only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx`. Use `push_cast`. Apply the tactic sequence `rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega`. Set `g₂ : W.EE` to `(((hXu.unit⁻¹ : W.EEˣ) : W.EE)) ^ size (c - 1) * ArcLengthThreeFiltration.ea Br a (Br.P.p 1 ^ (size (c - 2) + S))`.

Establish `hg₂ : algebraMap (LetA O n) W.EE (Br.cst (PowerSeries.X ^ size (c - 1))) * g₂ = ArcLengthThreeFiltration.ea Br a (Br.P.p 1 ^ (size (c - 2) + S))`. Simplify using `only [g₂]`. Rewrite using `[Br.cst_pow, map_pow, ← mul_assoc, ← mul_pow, hXu.mul_val_inv, one_pow, one_mul]`. Set `f₂ : Fin d → W.EE` to `fun k => g₂ * algebraMap O W.EE ((Pi.single k₀ (1 : O) : Fin d → O) k)`. Set `α₂ : ℕ → ℤ` to `fun s => if s = 0 then -((size (c - 1) : ℕ) : ℤ) else ((size (c - 2) + S : ℕ) : ℤ)`.

Establish `hNL₂ : InNL W T₂ a 2 (abelian₂ W (arcOf b w S η up size) a 2) bb f₂`. Use `⟨fun k => ?_, 0, 1, fun _ => g₂, fun _ => Pi.single k₀ 1, fun _ => α₂, fun _ => ⟨?_, ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hΛ]`. Establish `e : algebraMap (LetA O n) W.EE (Br.cst (PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S))) * f₂ k = ArcLengthThreeFiltration.ea Br a (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) * Br.P.p 1 ^ (size (c - 2) + S) * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O …`. Establish `es : PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S) = (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S)) * PowerSeries.X ^ size (c - 1)`.

Rewrite using `[show PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) * PowerSeries.X ^ size (c - 1) = PowerSeries.X ^ (b + η + S - size (c - 1) + size (c - 1)) * Br.P.p 1 ^ (w + S) by ring, Nat.sub_add_cancel (by omega)]`. Simplify using `only [f₂]`. Rewrite using `[es, Br.cst_mul, map_mul, show ∀ x y z t : W.EE, x * y * (z * t) = x * (y * z) * t by intros; ring, hg₂, ArcLengthThreeFiltration.cst_mul_ea, ArcLengthThreeFiltration.ea_mul_algO]`. Use `⟨Br.cst (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) * Br.P.p 1 ^ (size (c - 2) + S) * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) k)), Br.cst_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ArcLengthThreeFiltration.ea_def]`.

Use `beta_reduce`. Rewrite using `[ArcLengthThreeFiltration.inId_two Br]`. Establish `h0 : α₂ 0 = -((size (c - 1) : ℕ) : ℤ)` using `if_pos rfl`. Establish `h1 : α₂ 1 = ((size (c - 2) + S : ℕ) : ℤ)` using `if_neg one_ne_zero`. Rewrite using `[h0, h1, neg_neg, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_eq_zero.2 (show -((size (c - 1) : ℕ) : ℤ) ≤ 0 by omega), Int.toNat_eq_zero.2 (show -((size (c - 2) + S : ℕ) : ℤ) ≤ 0 by omega), pow_zero, pow_zero, one_mul, mul_one]`.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hg₂, mul_one]`. Both sides reduce to the same expression. Introduce `s hs interval_cases s`. Use `show dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 (-(α₂ 0))`.

Rewrite using `[show α₂ 0 = -((size (c - 1) : ℕ) : ℤ) from if_pos rfl, neg_neg]`. Conclude with `hℓa`. Use `show dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 1 (-(α₂ 1))`. Rewrite using `[show α₂ 1 = ((size (c - 2) + S : ℕ) : ℤ) from if_neg one_ne_zero]`. Conclude with `hℓa1`.

Simplify using `[f₂, lE]`. Take `⟨n₂, ⟨y₂, hy₂N, hy₂a, rfl⟩, hn₂R⟩` from `hAC9₂ f₂ hNL₂`. Rewrite `hn₂R` using `[one_smul]`. Establish `hy₂N'` using `(lemGB_memNΔ W).1 hy₂N`. Establish `hy₂Nl : y₂ ∈ W.Nl T₂ a` using `Submodule.mem_map.2 ⟨y₂, hy₂N'.1, by simpa using hy₂a⟩`.

Establish `hy₂i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ a y₂` using `⟨hy₂N, hy₂Nl⟩`. Take `⟨-, hKill, -⟩` from `hWR hcase T₁ T₂ F Mi hi hSur hJL a`. Establish `hz` using `hKill y₂ hy₂Nl hy₂N'.2`. Establish `hzΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a • y₂) = W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a • y₂`. Establish `h'` using `(lemGB_inNΔi_iff W).1 (inNΔi_smulA W T₂ a (W.AΔ.pow_mem hπ₀mem (Formalism.MainNotions.LiftingTheory.AI W F a)) hy₂i)`.

Conclude with `((lemGB_memNΔ W).1 h'.1).2`. Take `⟨n₁, hn₁i, hn₁F⟩` from `inImg_of_Nimg W hΔu F a hz hzΔ`. Establish `hn₁c : InFNc W T₁ a 1 n₁`. Use `⟨n₁, hn₁i.1, ?_, (one_smul _ _).symm⟩` and prove the remaining obligations. Take `⟨z, -, hz⟩` from `Submodule.mem_map.1 hn₁i.2`.

Rewrite using `[← hz]`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ArcLengthThreeFiltration.letE_mul_self]`. Take `⟨f₁, hf₁NL, hf₁R⟩` from `hAC8₁ n₁ hn₁c`. Establish `hli : ∀ c₀ : Fin d₁ → O, dvO W T₁ 2 b₁ c₀ = 0 → c₀ = 0`. Introduce `c₀ h`.

Rewrite `h` using `[ArcLengthThreeFiltration.dvO_eq]`. Use function extensionality and compare the values at `m`. Use `Fintype.linearIndependent_iff.1 hli₁ (fun m => algebraMap O LL (c₀ m)) h m` as an intermediate fact. Conclude with `hinj (by rw [this, Pi.zero_apply, map_zero])`. Establish `hTop0 : ∀ (c₀ : Fin d₁ → O) (u : ℤ), ((size (c - 1) + S : ℕ) : ℤ) < u → dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 u → dvO W T₁ 2 b₁ c₀ = 0`.

Introduce `c₀ u hu hm`. Rewrite `hm` using `[filS_top W hcase _ T₁ hW₁ a 0 u ?_]`. Conclude with `(Submodule.mem_bot _).1 hm`. Rewrite using `[ha0, hty1]`. Introduce `x hx`.

Simplify using `only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx`. Move the coercions through the operations in `at hu`. Use `hηs (c - 1)` as an intermediate fact. Apply the tactic sequence `rcases hx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega`. Establish `hTop1 : ∀ (c₀ : Fin d₁ → O) (u : ℤ), ((η : ℕ) : ℤ) < u → dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 1 u → dvO W T₁ 2 b₁ c₀ = 0`.

Introduce `c₀ u hu hm`. Rewrite `hm` using `[filS_top W hcase _ T₁ hW₁ a 1 u ?_]`. Conclude with `(Submodule.mem_bot _).1 hm`. Rewrite using `[ha2, hty2]`. Introduce `x hx`.

Simplify using `only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx`. Move the coercions through the operations in `at hu`. Apply the tactic sequence `rcases hx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega`. Establish `hGap : ∀ (c₀ : Fin d₁ → O) (u : ℤ), (η : ℤ) + 1 ≤ u → dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 u → dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 (size (c - 1))`. Introduce `c₀ u hu hm`.

Establish `h1` using `ArcLengthThreeFiltration.filS_anti W T₁ a 0 hu hm`. Conclude with `(hFL₁ c₀ 0 (by norm_num)).2 (size (c - 1)) (by rw [ha0]; exact hty1) h1`. Take `⟨Gs, hGs1, hGs2⟩` from `ArcLengthThreeFiltration.coef_fil Br hinj b₁ a (b + η + S) (w + S) (size (c - 1) + S) η η (by omega) (by omega) (size (c - 1)) hqu hpu hli hTop0 hTop1 hGap f₁ (hΛ ▸ hf₁NL)`. Establish `hlE : ∀ j, lE W j = algebraMap O W.EE (((PD.p : ℕ) : O) ^ j)` using `fun j => by simp [lE]`. Set `t₁ : LetA O n` to `Br.cst (PowerSeries.X ^ (size (c - 1) + S) * Br.P.p 1 ^ η)`.

Establish `ht₁ : t₁ ∈ W.AΔ` using `Br.cst_mem _`. Establish `hRep₁ : RepVV W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 ((arcOf b w S η up size).M PD.p) (abelian₂ W (arcOf b w S η up size) a 2) b₁ sol₁ (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁)) (fun k => ArcLengthThreeFiltration.ea Br a (Gs k))` using `TypesA.RepVV_congr W (ArcLengthThreeFiltration.repVV_smulA W hf₁R ht₁) rfl (fun k => hGs1 k)`. Establish `hx₁c : InFNc W T₁ a 1 (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁))` using `TypesA.InFNc_smul W ht₁ (TypesA.InFNc_smul W (TypesA.lA_pow_mem W _) hn₁c)`. Establish `hRep₂` using `hRep _ _ (hAC3₁ _ hx₁c) (fun m => by rw [hΛ]; exact ArcLengthThreeFiltration.inFr_one_ea Br a _ _) hRep₁`. Establish `ht₂ : t₁ * lA W ^ (arcOf b w S η up size).σ PD.p * W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a ∈ W.AΔ` using `mul_mem (mul_mem ht₁ (TypesA.lA_pow_mem W _)) (W.AΔ.pow_mem hπ₀mem _)`.

Establish `hmap : W.map F (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁)) = (t₁ * lA W ^ (arcOf b w S η up size).σ PD.p * W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a) • y₂`. Rewrite using `[TypesA.map_smulA, TypesA.map_smulA, hn₁F, smul_smul, smul_smul]`. Establish `hRep₂'` using `ArcLengthThreeFiltration.repVV_smulA W hn₂R ht₂`. Set `Fser : PowerSeries O` to `PowerSeries.C ((PD.p : ℕ) : O) ^ (2 * (arcOf b w S η up size).σ PD.p) * (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ Formalism.MainNotions.LiftingTheory.AI W F a * PowerSeries.X ^ S * Br.P.p 1 ^ (size (c - 2) + S + η)`. Establish `hcomp : ∀ k, algebraMap (LetA O n) W.EE (t₁ * lA W ^ (arcOf b w S η up size).σ PD.p * W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a) * (lE W ((arcOf b w S η up size).σ PD.p) * f₂ k) = ArcLengthThreeFiltration.ea Br a (Fser * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) …`.

Introduce `k`. Establish `eX : t₁ = Br.cst (PowerSeries.X ^ size (c - 1)) * Br.cst (PowerSeries.X ^ S * Br.P.p 1 ^ η)`. Simplify using `only [t₁]`. Rewrite using `[← Br.cst_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `eL : lA W ^ (arcOf b w S η up size).σ PD.p = Br.cst (PowerSeries.C ((PD.p : ℕ) : O) ^ (arcOf b w S η up size).σ PD.p)`. Rewrite using `[Br.lA_eq, Br.cst_pow]`. Establish `eP : W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a = Br.cst ((PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ Formalism.MainNotions.LiftingTheory.AI W F a)`. Rewrite using `[ArcLengthThreeFiltration.pi0_eq_cst_X_sub_C_prime Br, Br.cst_pow]`.

Rewrite using `[eX, eL, eP, map_mul, map_mul, map_mul, hlE]`. Simplify using `only [f₂]`. Rewrite using `[show ∀ x₁ x₂ x₃ x₄ x₅ y z : W.EE, x₁ * x₂ * x₃ * x₄ * (x₅ * (y * z)) = (x₁ * y) * x₂ * x₃ * x₄ * x₅ * z by intros; ring, hg₂, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_algO, ArcL …`. Use `congr 1`. Simplify using `only [Fser, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hRep0 : RepVV W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 ((arcOf b w S η up size).M PD.p) (abelian₂ W (arcOf b w S η up size) a 2) bb sol 0 (fun k => ArcLengthThreeFiltration.ea Br a ((∑ m, PowerSeries.C (μ m k) * Gs m) - Fser * PowerSeries.C ((Pi.single k₀ (1 : …`. Establish `h` using `TypesA.RepVV_add W hRep₂ (TypesA.RepVV_neg W hRep₂')`. Use `TypesA.RepVV_congr W h (by rw [hmap, add_neg_cancel]) (fun k => ?_)` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[hcomp k, ArcLengthThreeFiltration.ea_sub, ArcLengthThreeFiltration.ea_sum, sub_eq_add_neg]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [ArcLengthThreeFiltration.ea_C_mul, mul_comm]`. Establish `hM1 : 1 ≤ (arcOf b w S η up size).M PD.p` using `by unfold ArcP.M; exact Nat.le_add_left 1 _`. Take `⟨K, hK⟩` from `repVV_zero_coord W hcase hP9 hinj T₂ hT₂ _ 2 _ hM1 _ hΛmem hΛu (by rw [hΛ]; exact ArcLengthThreeFiltration.phi_sq_pi0_pow_power_series Br _ _) bb sol hbb _ hRep0`.

Establish `hcoef : ∀ j < size (c - 1) + S - η, ∀ k, ∑ m, μ m k * PowerSeries.coeff j (Gs m) = PowerSeries.coeff j Fser * (Pi.single k₀ (1 : O) : Fin d → O) k`. Introduce `j hj k`. Take `⟨u, hu, hku⟩` from `hK k`. Rewrite `hku` using `[hΛ]`. Establish `h0` using `ArcLengthThreeFiltration.coeff_zero_of_coord Br hinj a K (b + η + S) _ _ u hu hku j (by omega)`.

Rewrite `h0` using `[map_sub, map_sum, sub_eq_zero]`. Simplify `h0` using `only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C]`. Establish `hpr2 : ∀ j < size (c - 1) + S - η, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 2 b₁ (fun m => PowerSeries.coeff j (Gs m))) = algebraMap O LL (PowerSeries.coeff j Fser) • dv W T₂ 2 bb (Pi.single k₀ 1)`. Introduce `j hj`. Rewrite using `[ArcLengthThreeFiltration.dvO_eq, map_sum]`.

Repeatedly rewrite using `[map_smul, hμ]`. Rewrite using `[← ArcLengthThreeFiltration.dvO_lin, ← ArcLengthThreeFiltration.dvO_single, ← ArcLengthThreeFiltration.dvO_smulO]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← hcoef j hj k]`.

Conclude with `Finset.sum_congr rfl fun m _ => mul_comm _ _`. Establish `hSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η`. Unfold `Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg`. Rewrite using `[show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S from hAh]`. Set `Mi' : ZMod n → ℕ` to `fun i => if up i then η else size i + S`.

Set `hi' : ZMod n → ℕ` to `fun i => if up i then size i + S else η`. Establish `hJL' : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi'`. Introduce `i τ hτ x hx`. Establish `h1` using `hJ i τ hτ x hx`. Establish `h2` using `hηs i`.

Simplify using `only [Mi', hi']`. Apply the tactic sequence `split_ifs at h1 ⊢ with hui <;> simp only [Set.mem_union, Set.mem_Icc] at h1 ⊢ <;> omega`. Take `⟨-, -, -, -, -, hAIle, -⟩` from `hWR hcase T₁ T₂ F Mi' hi' hSur hJL' a`. Establish `hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ b + η + S + η`. Unfold `Formalism.MainNotions.LiftingTheory.Hmax`.

Use `Finset.sup_le fun k _ => ?_` and prove the remaining obligations. Establish `hsz : size (k : ZMod n) ≤ b + η`. Distinguish the cases in `ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (k : ZMod n)`. Conclude with `ht.2`. Use `hnt _ ht` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Mi', hi']`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hA' : (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ (((b + η + S : ℕ) : ℝ) + η) / ((PD.p : ℝ) - 1) + 1`. Establish `hp1 : (0 : ℝ) < (PD.p : ℝ) - 1`.

Establish `: (11 : ℝ) ≤ PD.p` using `by exact_mod_cast hp11`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℕ) : ℝ) ≤ ((b + η + S : ℕ) : ℝ) + η`. Establish `: ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℕ) : ℝ) ≤ ((b + η + S + η : ℕ) : ℝ)` using `by exact_mod_cast hHle`. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `div_le_div_of_nonneg_right h3 hp1.le`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s₁, hs₁σ, hs₁k, hs₁c2, hs₁10⟩` from `ArcLengthThreeFiltration.numerics PD.p b w S η (size (c - 1)) (size (c - 2)) ((arcOf b w S η up size).σ PD.p) (Formalism.MainNotions.LiftingTheory.AI W F a) hp11 hη20 hS20 hw20 hb₁b hw' hηw' hy (hSg ▸ hσ) hA' (hSg ▸ hsm)`. Establish `hnot` using `ArcLengthThreeFiltration.content_notMem Br.P ((arcOf b w S η up size).σ PD.p) (Formalism.MainNotions.LiftingTheory.AI W F a) S (size (c - 2) + S + η) (size (c - 1)) η s₁ hs₁σ hs₁k (by omega) hs₁c2`.

Establish `hex : ∃ j < size (c - 1) + S - η, ¬ (((PD.p : ℕ) : O) ^ s₁ ∣ PowerSeries.coeff j Fser)`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hnot` to reduce the goal to its premises. Establish `e : Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ s₁, (PowerSeries.X : PowerSeries O) ^ (size (c - 1) + S - η)} = Ideal.span {PowerSeries.C (((PD.p : ℕ) : O) ^ s₁), PowerSeries.X ^ (size (c - 1) + S - η)}`.

Rewrite using `[map_pow]`. Rewrite using `[e]`. Conclude with `(ArcLengthThreeFiltration.mem_pair_X_iff _ _ _).2 hall`. Take `⟨j, hj, hjd⟩` from `hex`. Take `⟨t, ht⟩` from `ArcLengthThreeFiltration.dvd_of_not_dvd hjd`.

Set `c₁ : Fin d₁ → O` to `fun m => t * PowerSeries.coeff j (Gs m)`. Establish `hlt2 : dvO W T₁ 2 b₁ c₁ ∈ FilS W T₁ a 0 (size (c - 1))`. Simplify using `only [c₁]`. Rewrite using `[ArcLengthThreeFiltration.dvO_smulO]`. Conclude with `Submodule.smul_mem _ _ (hGs2 j hj)`.

Establish `hpr3 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 2 b₁ c₁) = ((PD.p : LL) ^ s₁) • dv W T₂ 2 bb (Pi.single k₀ 1)`. Simplify using `only [c₁]`. Rewrite using `[ArcLengthThreeFiltration.dvO_smulO, map_smul, hpr2 j hj, smul_smul, ← map_mul, mul_comm t, ← ht, map_pow, map_natCast]`. Establish `hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1)`. Unfold `nnDen prodTy`.

Rewrite using `[hlen]`. Simplify using `[Finset.prod_range_succ, hty0, hty1, hty2]`. Establish `hty1' : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .up (size (c - 1))` using `by simpa using hty1`. Establish `hC` using `liftsAt_thin_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc (fun s _ => ArcLengthThreeFiltration.arc_thick _) hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hW₁ hW₂ hbb {1} (fun s hs => by`. Rewrite `hs` using `[Finset.mem_singleton]`.

Substitute `hs` using the available equality. Conclude with `⟨by rw [hlen]; norm_num, size (c - 1), by simpa using hty1⟩)`. Use `b₁ sol₁ hb₁ c₁ s₁`. Use the proof step `(fun s hs bs hbs => by`. Rewrite `hs` using `[Finset.mem_singleton]`.

Substitute `hs` using the available equality. Establish `hbs' : bs = size (c - 1)`. Establish `h1 : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .up (size (c - 1))` using `by simpa using hty1`. Rewrite `hbs` using `[h1]`. Conclude with `(Formalism.MainNotions.LocalTheoryWindows.LT.up.inj hbs).symm`.

Substitute `hbs'` using the available equality. Rewrite using `[hlen, show (3 : ℕ) = 2 + 1 from rfl]`. Use `show dv W T₁ (2 + 1) b₁ _ ∈ _`. Rewrite using `[ArcLengthThreeFiltration.dv_succ W T₁ 2]`. Establish `h2` using `ArcLengthThreeFiltration.filS_one_of W T₁ a _ _ hlt2`.

Rewrite `h2` using `[ha3]`. Conclude with `h2)`. Use the proof step `(by`. Rewrite using `[hlen, show (3 : ℕ) = 2 + 1 from rfl]`. Use `show Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ (2 + 1) b₁ _) = _ • dv W T₂ (2 + 1) bb _`.

Rewrite using `[ArcLengthThreeFiltration.dv_succ W T₁ 2, ArcLengthThreeFiltration.dv_succ W T₂ 2, ArcLengthThreeFiltration.crisMap_φ]`. Establish `h3 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ 2 b₁ fun m => algebraMap O LL (c₁ m)) = ((PD.p : LL) ^ s₁) • dv W T₂ 2 bb (Pi.single k₀ 1)` using `hpr3`. Rewrite using `[h3, map_smul])`. Use `f (by`. Simplify using `only [Finset.prod_singleton]`.

Rewrite using `[hty1']`. Simplify using `only`. Rewrite using `[← hnn]`. Conclude with `hf.1)`. Use the proof step `(fun s hs bs hbs => by`.

Take `⟨κ, x, hx⟩` from `hf.2 s hs bs hbs`. Use `⟨κ, x, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.prod_singleton]`. Rewrite using `[hty1']`. Simplify using `only`.

Rewrite `hx` using `[hnn]`. Conclude with `hx)`. Use the proof step `(fun s hs hs1 bs hbs => by`. Rewrite `hs` using `[hlen]`. Use `interval_cases s`.

Simplify using `[hty0] at hbs`. Simplify using `at hs1`. Establish `h2 : (arcOf b w S η up size).ty (c - ((2 : ℕ) : ZMod n)) = .down (size (c - 2))` using `by simpa using hty2`. Rewrite using `[h2] at hbs; exact absurd hbs (by simp))`. Use `⟨s₁ + (arcOf b w S η up size).σ PD.p, ?_, hC⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite `hσ`, the goal using `[hSg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arc_length_three_case_c [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hy : PD.p * (size (c - 2) + S + η) ≤ size (c - 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 13 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨hp11, hSet, hw20, hη20, hS20, -⟩ := hB
  obtain ⟨-, hSur, hηs, hJ, -, hnt, hJL⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega
  obtain ⟨hTc, hTc1, hTc2⟩ := ArcLengthThreeFiltration.arc_len_three_thick_letters hlen
  obtain ⟨hu1, hu0⟩ := ArcLengthThreeFiltration.arc_types halt hD
  have hty1 : (arcOf b w S η up size).ty (c - 1) = .up (size (c - 1)) := by simp [ArcLengthThreeFiltration.arc_ty, hu1]
  have hty2 : (arcOf b w S η up size).ty (c - 2) = .down (size (c - 2)) := by simp [ArcLengthThreeFiltration.arc_ty, hD]
  have hty0 : (arcOf b w S η up size).ty c = .down (size c) := by simp [ArcLengthThreeFiltration.arc_ty, hu0]
  have hw' : size (c - 2) ≤ w := hnt _ hTc2
  have hηw' : η < size (c - 2) := hηs _
  have hb₁b : b ≤ size (c - 1) := hTc1.1
  have hb₁b' : size (c - 1) ≤ b + η := hTc1.2
  have hAh : (arcOf b w S η up size).h = b + η + S := by
    show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hTc⟩]
  have hj2 : (arcOf b w S η up size).j ≤ 2 := by show 1 ≤ 2; norm_num
  have h2l : 2 ≤ (arcOf b w S η up size).len c := by rw [hlen]; norm_num
  have hT₁ : IsCrys PD T₁.ρ := hW₁.1
  have hT₂ : IsCrys PD T₂.ρ := hW₂.1
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hT₁ hO hinj
  obtain ⟨-, hqu, hΔu⟩ := lemG_units W hcase hP9 hT₁ hO hOv hinj
  have hpu : IsUnit (algebraMap (LetA O n) W.EE (ps W 1)) := by
    have e : algebraMap (LetA O n) W.EE (ps W 1) = W.φE (algebraMap (LetA O n) W.EE (qA W)) := by
      rw [W.φE_ext]; show _ = algebraMap (LetA O n) W.EE (W.φA (qA W)); unfold ps; rw [pow_one]
    rw [e]; exact hqu.map W.φE
  have hXu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst PowerSeries.X)) := Br.qA_eq ▸ hqu
  have hPu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst (Br.P.p 1))) := (ArcLengthThreeFiltration.ps_cst Br 1) ▸ hpu
  have hπ₀mem : W.π₀ ∈ W.AΔ := (qA_mem_AΔ W hcase hP9 hT₁).1

  obtain ⟨-, hACT⟩ := hArc hcase hl5 _ hOK c hc 2 hj2 h2l
  obtain ⟨-, hAC3₂, -, hfr₂⟩ := hACT T₂ hW₂
  obtain ⟨-, -, -, -, hAC9₂, -, -⟩ := hfr₂ d bb sol hbb
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
  obtain ⟨-, hAC3₁, -, hfr₁⟩ := hACT T₁ hW₁
  obtain ⟨⟨hli₁, -⟩, -, -, hAC8₁, -, -, -⟩ := hfr₁ d₁ b₁ sol₁ hb₁
  obtain ⟨-, μ, hμ, hRep⟩ := hSec hcase hl5 _ hOK c hc 2 hj2 h2l T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d bb sol hbb
  have hFL₁ := hFL hcase hl5 _ hOK c hc 2 hj2 h2l T₁ hW₁ d₁ b₁ sol₁ hb₁
  have hFL₂ := hFL hcase hl5 _ hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb
  have ha1 : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n) = c - 1 := by
    rw [hlen]; push_cast; ring
  have hΛ : abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2 =
      Br.cst (PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S)) := by
    rw [ArcLengthThreeFiltration.lam_inner W hlen, ArcLengthThreeFiltration.ps_cst Br, ArcLengthThreeFiltration.ps_cst Br, ArcLengthThreeFiltration.p_zero, hAh, Br.cst_mul, Br.cst_pow, Br.cst_pow]
    rfl
  set a := c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n) with ha
  have ha0 : a - ((0 : ℕ) : ZMod n) = c - 1 := by rw [ha1]; simp
  have ha2 : a - ((1 : ℕ) : ZMod n) = c - 2 := by rw [ha1]; push_cast; ring
  have ha3 : a + 1 = c := by rw [ha1]; ring
  have hΛmem : abelian₂ W (arcOf b w S η up size) a 2 ∈ W.AΔ := by rw [hΛ]; exact Br.cst_mem _
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W (arcOf b w S η up size) a 2)) := by
    rw [hΛ, Br.cst_mul, Br.cst_pow, Br.cst_pow, map_mul, map_pow, map_pow]
    exact (hXu.pow _).mul (hPu.pow _)

  have hℓa : dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 (size (c - 1)) := by
    have h1 := hk₀ 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)
    rw [hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthThreeFiltration.dv_succ,
      show FilS W T₂ c 1 (size (c - 1)) = FilS W T₂ (a + 1) 1 (size (c - 1)) by rw [ha3]] at h1
    rw [ArcLengthThreeFiltration.dvO_single]
    exact ArcLengthThreeFiltration.filS_zero_of W T₂ a _ _ h1
  have hℓa1 : dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 1 (-((size (c - 2) + S : ℕ) : ℤ)) := by
    refine (hFL₂ (Pi.single k₀ 1) 1 (by norm_num)).1 _ ?_
    rw [ha2, hty2]
    intro x hx
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx
    push_cast
    rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  let g₂ : W.EE := (((hXu.unit⁻¹ : W.EEˣ) : W.EE)) ^ size (c - 1) * ArcLengthThreeFiltration.ea Br a (Br.P.p 1 ^ (size (c - 2) + S))
  have hg₂ : algebraMap (LetA O n) W.EE (Br.cst (PowerSeries.X ^ size (c - 1))) * g₂ =
      ArcLengthThreeFiltration.ea Br a (Br.P.p 1 ^ (size (c - 2) + S)) := by
    simp only [g₂]
    rw [Br.cst_pow, map_pow, ← mul_assoc, ← mul_pow, hXu.mul_val_inv, one_pow, one_mul]
  let f₂ : Fin d → W.EE := fun k => g₂ * algebraMap O W.EE ((Pi.single k₀ (1 : O) : Fin d → O) k)
  let α₂ : ℕ → ℤ := fun s => if s = 0 then -((size (c - 1) : ℕ) : ℤ) else ((size (c - 2) + S : ℕ) : ℤ)
  have hNL₂ : InNL W T₂ a 2 (abelian₂ W (arcOf b w S η up size) a 2) bb f₂ := by
    refine ⟨fun k => ?_, 0, 1, fun _ => g₂, fun _ => Pi.single k₀ 1, fun _ => α₂, fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
    · rw [hΛ]
      have e : algebraMap (LetA O n) W.EE (Br.cst (PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S))) * f₂ k =
          ArcLengthThreeFiltration.ea Br a (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) *
            Br.P.p 1 ^ (size (c - 2) + S) * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) k)) := by
        have es : PowerSeries.X ^ (b + η + S) * Br.P.p 1 ^ (w + S) =
            (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S)) * PowerSeries.X ^ size (c - 1) := by
          rw [show PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) * PowerSeries.X ^ size (c - 1) =
            PowerSeries.X ^ (b + η + S - size (c - 1) + size (c - 1)) * Br.P.p 1 ^ (w + S) by ring,
            Nat.sub_add_cancel (by omega)]
        simp only [f₂]
        rw [es, Br.cst_mul, map_mul, show ∀ x y z t : W.EE, x * y * (z * t) = x * (y * z) * t by intros; ring,
          hg₂, ArcLengthThreeFiltration.cst_mul_ea, ArcLengthThreeFiltration.ea_mul_algO]
      refine ⟨Br.cst (PowerSeries.X ^ (b + η + S - size (c - 1)) * Br.P.p 1 ^ (w + S) *
        Br.P.p 1 ^ (size (c - 2) + S) * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) k)), Br.cst_mem _, ?_⟩
      rw [e, ArcLengthThreeFiltration.ea_def]
    · beta_reduce
      rw [ArcLengthThreeFiltration.inId_two Br]
      have h0 : α₂ 0 = -((size (c - 1) : ℕ) : ℤ) := if_pos rfl
      have h1 : α₂ 1 = ((size (c - 2) + S : ℕ) : ℤ) := if_neg one_ne_zero
      rw [h0, h1, neg_neg, Int.toNat_natCast, Int.toNat_natCast,
        Int.toNat_eq_zero.2 (show -((size (c - 1) : ℕ) : ℤ) ≤ 0 by omega),
        Int.toNat_eq_zero.2 (show -((size (c - 2) + S : ℕ) : ℤ) ≤ 0 by omega),
        pow_zero, pow_zero, one_mul, mul_one]
      refine ⟨1, one_mem _, ?_⟩
      rw [hg₂, mul_one]; rfl
    · intro s hs
      interval_cases s
      · show dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 (-(α₂ 0))
        rw [show α₂ 0 = -((size (c - 1) : ℕ) : ℤ) from if_pos rfl, neg_neg]; exact hℓa
      · show dvO W T₂ 2 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 1 (-(α₂ 1))
        rw [show α₂ 1 = ((size (c - 2) + S : ℕ) : ℤ) from if_neg one_ne_zero]; exact hℓa1
    · simp [f₂, lE]
  obtain ⟨n₂, ⟨y₂, hy₂N, hy₂a, rfl⟩, hn₂R⟩ := hAC9₂ f₂ hNL₂
  rw [one_smul] at hn₂R

  have hy₂N' := (lemGB_memNΔ W).1 hy₂N
  have hy₂Nl : y₂ ∈ W.Nl T₂ a := Submodule.mem_map.2 ⟨y₂, hy₂N'.1, by simpa using hy₂a⟩
  have hy₂i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ a y₂ := ⟨hy₂N, hy₂Nl⟩
  obtain ⟨-, hKill, -⟩ := hWR hcase T₁ T₂ F Mi hi hSur hJL a
  have hz := hKill y₂ hy₂Nl hy₂N'.2
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a • y₂) = W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a • y₂ := by
    have h' := (lemGB_inNΔi_iff W).1 (inNΔi_smulA W T₂ a (W.AΔ.pow_mem hπ₀mem (Formalism.MainNotions.LiftingTheory.AI W F a)) hy₂i)
    exact ((lemGB_memNΔ W).1 h'.1).2
  obtain ⟨n₁, hn₁i, hn₁F⟩ := inImg_of_Nimg W hΔu F a hz hzΔ
  have hn₁c : InFNc W T₁ a 1 n₁ := by
    refine ⟨n₁, hn₁i.1, ?_, (one_smul _ _).symm⟩
    obtain ⟨z, -, hz⟩ := Submodule.mem_map.1 hn₁i.2
    rw [← hz]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ArcLengthThreeFiltration.letE_mul_self]
  obtain ⟨f₁, hf₁NL, hf₁R⟩ := hAC8₁ n₁ hn₁c

  have hli : ∀ c₀ : Fin d₁ → O, dvO W T₁ 2 b₁ c₀ = 0 → c₀ = 0 := by
    intro c₀ h
    rw [ArcLengthThreeFiltration.dvO_eq] at h
    funext m
    have := Fintype.linearIndependent_iff.1 hli₁ (fun m => algebraMap O LL (c₀ m)) h m
    exact hinj (by rw [this, Pi.zero_apply, map_zero])
  have hTop0 : ∀ (c₀ : Fin d₁ → O) (u : ℤ), ((size (c - 1) + S : ℕ) : ℤ) < u →
      dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 u → dvO W T₁ 2 b₁ c₀ = 0 := by
    intro c₀ u hu hm
    rw [filS_top W hcase _ T₁ hW₁ a 0 u ?_] at hm
    · exact (Submodule.mem_bot _).1 hm
    rw [ha0, hty1]
    intro x hx
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx
    push_cast at hu
    have := hηs (c - 1)
    rcases hx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  have hTop1 : ∀ (c₀ : Fin d₁ → O) (u : ℤ), ((η : ℕ) : ℤ) < u →
      dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 1 u → dvO W T₁ 2 b₁ c₀ = 0 := by
    intro c₀ u hu hm
    rw [filS_top W hcase _ T₁ hW₁ a 1 u ?_] at hm
    · exact (Submodule.mem_bot _).1 hm
    rw [ha2, hty2]
    intro x hx
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, arcOf] at hx
    push_cast at hu
    rcases hx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  have hGap : ∀ (c₀ : Fin d₁ → O) (u : ℤ), (η : ℤ) + 1 ≤ u → dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 u →
      dvO W T₁ 2 b₁ c₀ ∈ FilS W T₁ a 0 (size (c - 1)) := by
    intro c₀ u hu hm
    have h1 := ArcLengthThreeFiltration.filS_anti W T₁ a 0 hu hm
    exact (hFL₁ c₀ 0 (by norm_num)).2 (size (c - 1)) (by rw [ha0]; exact hty1) h1
  obtain ⟨Gs, hGs1, hGs2⟩ := ArcLengthThreeFiltration.coef_fil Br hinj b₁ a (b + η + S) (w + S) (size (c - 1) + S) η η
    (by omega) (by omega) (size (c - 1)) hqu hpu hli hTop0 hTop1 hGap f₁ (hΛ ▸ hf₁NL)

  have hlE : ∀ j, lE W j = algebraMap O W.EE (((PD.p : ℕ) : O) ^ j) := fun j => by simp [lE]
  let t₁ : LetA O n := Br.cst (PowerSeries.X ^ (size (c - 1) + S) * Br.P.p 1 ^ η)
  have ht₁ : t₁ ∈ W.AΔ := Br.cst_mem _
  have hRep₁ : RepVV W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 ((arcOf b w S η up size).M PD.p)
      (abelian₂ W (arcOf b w S η up size) a 2) b₁ sol₁
      (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁)) (fun k => ArcLengthThreeFiltration.ea Br a (Gs k)) :=
    TypesA.RepVV_congr W (ArcLengthThreeFiltration.repVV_smulA W hf₁R ht₁) rfl (fun k => hGs1 k)
  have hx₁c : InFNc W T₁ a 1 (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁)) :=
    TypesA.InFNc_smul W ht₁ (TypesA.InFNc_smul W (TypesA.lA_pow_mem W _) hn₁c)
  have hRep₂ := hRep _ _ (hAC3₁ _ hx₁c) (fun m => by rw [hΛ]; exact ArcLengthThreeFiltration.inFr_one_ea Br a _ _) hRep₁
  have ht₂ : t₁ * lA W ^ (arcOf b w S η up size).σ PD.p * W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a ∈ W.AΔ :=
    mul_mem (mul_mem ht₁ (TypesA.lA_pow_mem W _)) (W.AΔ.pow_mem hπ₀mem _)
  have hmap : W.map F (t₁ • (lA W ^ (arcOf b w S η up size).σ PD.p • n₁)) =
      (t₁ * lA W ^ (arcOf b w S η up size).σ PD.p * W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a) • y₂ := by
    rw [TypesA.map_smulA, TypesA.map_smulA, hn₁F, smul_smul, smul_smul]
  have hRep₂' := ArcLengthThreeFiltration.repVV_smulA W hn₂R ht₂
  let Fser : PowerSeries O := PowerSeries.C ((PD.p : ℕ) : O) ^ (2 * (arcOf b w S η up size).σ PD.p) *
    (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ Formalism.MainNotions.LiftingTheory.AI W F a * PowerSeries.X ^ S *
    Br.P.p 1 ^ (size (c - 2) + S + η)
  have hcomp : ∀ k, algebraMap (LetA O n) W.EE (t₁ * lA W ^ (arcOf b w S η up size).σ PD.p *
      W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a) * (lE W ((arcOf b w S η up size).σ PD.p) * f₂ k) =
      ArcLengthThreeFiltration.ea Br a (Fser * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) k)) := by
    intro k
    have eX : t₁ = Br.cst (PowerSeries.X ^ size (c - 1)) * Br.cst (PowerSeries.X ^ S * Br.P.p 1 ^ η) := by
      simp only [t₁]; rw [← Br.cst_mul]; congr 1; ring
    have eL : lA W ^ (arcOf b w S η up size).σ PD.p =
        Br.cst (PowerSeries.C ((PD.p : ℕ) : O) ^ (arcOf b w S η up size).σ PD.p) := by
      rw [Br.lA_eq, Br.cst_pow]
    have eP : W.π₀ ^ Formalism.MainNotions.LiftingTheory.AI W F a =
        Br.cst ((PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ Formalism.MainNotions.LiftingTheory.AI W F a) := by
      rw [ArcLengthThreeFiltration.pi0_eq_cst_X_sub_C_prime Br, Br.cst_pow]
    rw [eX, eL, eP, map_mul, map_mul, map_mul, hlE]
    simp only [f₂]
    rw [show ∀ x₁ x₂ x₃ x₄ x₅ y z : W.EE, x₁ * x₂ * x₃ * x₄ * (x₅ * (y * z)) = (x₁ * y) * x₂ * x₃ * x₄ * x₅ * z by
        intros; ring, hg₂, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_cst, ArcLengthThreeFiltration.ea_mul_algO, ArcLengthThreeFiltration.ea_mul_algO]
    congr 1
    simp only [Fser, map_pow]
    ring
  have hRep0 : RepVV W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 ((arcOf b w S η up size).M PD.p)
      (abelian₂ W (arcOf b w S η up size) a 2) bb sol 0
      (fun k => ArcLengthThreeFiltration.ea Br a ((∑ m, PowerSeries.C (μ m k) * Gs m) -
        Fser * PowerSeries.C ((Pi.single k₀ (1 : O) : Fin d → O) k))) := by
    have h := TypesA.RepVV_add W hRep₂ (TypesA.RepVV_neg W hRep₂')
    refine TypesA.RepVV_congr W h (by rw [hmap, add_neg_cancel]) (fun k => ?_)
    beta_reduce
    rw [hcomp k, ArcLengthThreeFiltration.ea_sub, ArcLengthThreeFiltration.ea_sum, sub_eq_add_neg]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by rw [ArcLengthThreeFiltration.ea_C_mul, mul_comm]
  have hM1 : 1 ≤ (arcOf b w S η up size).M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  obtain ⟨K, hK⟩ := repVV_zero_coord W hcase hP9 hinj T₂ hT₂ _ 2 _ hM1 _ hΛmem hΛu
    (by rw [hΛ]; exact ArcLengthThreeFiltration.phi_sq_pi0_pow_power_series Br _ _) bb sol hbb _ hRep0
  have hcoef : ∀ j < size (c - 1) + S - η, ∀ k, ∑ m, μ m k * PowerSeries.coeff j (Gs m) =
      PowerSeries.coeff j Fser * (Pi.single k₀ (1 : O) : Fin d → O) k := by
    intro j hj k
    obtain ⟨u, hu, hku⟩ := hK k
    rw [hΛ] at hku
    have h0 := ArcLengthThreeFiltration.coeff_zero_of_coord Br hinj a K (b + η + S) _ _ u hu hku j (by omega)
    rw [map_sub, map_sum, sub_eq_zero] at h0
    simpa only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C] using h0

  have hpr2 : ∀ j < size (c - 1) + S - η, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 2 b₁ (fun m => PowerSeries.coeff j (Gs m))) =
      algebraMap O LL (PowerSeries.coeff j Fser) • dv W T₂ 2 bb (Pi.single k₀ 1) := by
    intro j hj
    rw [ArcLengthThreeFiltration.dvO_eq, map_sum]
    simp_rw [map_smul, hμ]
    rw [← ArcLengthThreeFiltration.dvO_lin, ← ArcLengthThreeFiltration.dvO_single, ← ArcLengthThreeFiltration.dvO_smulO]
    congr 1
    funext k
    rw [← hcoef j hj k]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

  have hSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S from hAh]
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJL' : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ x hx
    have h1 := hJ i τ hτ x hx
    have h2 := hηs i
    simp only [Mi', hi']
    split_ifs at h1 ⊢ with hui <;> simp only [Set.mem_union, Set.mem_Icc] at h1 ⊢ <;> omega
  obtain ⟨-, -, -, -, -, hAIle, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJL' a
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ b + η + S + η := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    refine Finset.sup_le fun k _ => ?_
    have hsz : size (k : ZMod n) ≤ b + η := by
      by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (k : ZMod n)
      · exact ht.2
      · have := hnt _ ht; omega
    simp only [Mi', hi']
    split_ifs <;> omega
  have hA' : (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ (((b + η + S : ℕ) : ℝ) + η) / ((PD.p : ℝ) - 1) + 1 := by
    have hp1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by
      have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
      linarith
    have h3 : ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℕ) : ℝ) ≤ ((b + η + S : ℕ) : ℝ) + η := by
      have : ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℕ) : ℝ) ≤ ((b + η + S + η : ℕ) : ℝ) := by exact_mod_cast hHle
      push_cast at this ⊢; linarith
    have h4 := div_le_div_of_nonneg_right h3 hp1.le
    linarith
  obtain ⟨s₁, hs₁σ, hs₁k, hs₁c2, hs₁10⟩ := ArcLengthThreeFiltration.numerics PD.p b w S η (size (c - 1)) (size (c - 2))
    ((arcOf b w S η up size).σ PD.p) (Formalism.MainNotions.LiftingTheory.AI W F a) hp11 hη20 hS20 hw20 hb₁b hw' hηw' hy
    (hSg ▸ hσ) hA' (hSg ▸ hsm)
  have hnot := ArcLengthThreeFiltration.content_notMem Br.P ((arcOf b w S η up size).σ PD.p) (Formalism.MainNotions.LiftingTheory.AI W F a) S
    (size (c - 2) + S + η) (size (c - 1)) η s₁ hs₁σ hs₁k (by omega) hs₁c2
  have hex : ∃ j < size (c - 1) + S - η, ¬ (((PD.p : ℕ) : O) ^ s₁ ∣ PowerSeries.coeff j Fser) := by
    by_contra hall
    push Not at hall
    apply hnot
    have e : Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ s₁,
        (PowerSeries.X : PowerSeries O) ^ (size (c - 1) + S - η)} =
        Ideal.span {PowerSeries.C (((PD.p : ℕ) : O) ^ s₁), PowerSeries.X ^ (size (c - 1) + S - η)} := by
      rw [map_pow]
    rw [e]
    exact (ArcLengthThreeFiltration.mem_pair_X_iff _ _ _).2 hall
  obtain ⟨j, hj, hjd⟩ := hex
  obtain ⟨t, ht⟩ := ArcLengthThreeFiltration.dvd_of_not_dvd hjd
  let c₁ : Fin d₁ → O := fun m => t * PowerSeries.coeff j (Gs m)
  have hlt2 : dvO W T₁ 2 b₁ c₁ ∈ FilS W T₁ a 0 (size (c - 1)) := by
    simp only [c₁]; rw [ArcLengthThreeFiltration.dvO_smulO]; exact Submodule.smul_mem _ _ (hGs2 j hj)
  have hpr3 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 2 b₁ c₁) = ((PD.p : LL) ^ s₁) • dv W T₂ 2 bb (Pi.single k₀ 1) := by
    simp only [c₁]
    rw [ArcLengthThreeFiltration.dvO_smulO, map_smul, hpr2 j hj, smul_smul, ← map_mul, mul_comm t, ← ht, map_pow, map_natCast]

  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen]
    simp [Finset.prod_range_succ, hty0, hty1, hty2]
  have hty1' : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .up (size (c - 1)) := by simpa using hty1
  have hC := liftsAt_thin_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc (fun s _ => ArcLengthThreeFiltration.arc_thick _) hcase hl5
    hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hW₁ hW₂ hbb {1}
    (fun s hs => by
      rw [Finset.mem_singleton] at hs; subst hs
      exact ⟨by rw [hlen]; norm_num, size (c - 1), by simpa using hty1⟩)
    b₁ sol₁ hb₁ c₁ s₁
    (fun s hs bs hbs => by
      rw [Finset.mem_singleton] at hs; subst hs
      have hbs' : bs = size (c - 1) := by
        have h1 : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .up (size (c - 1)) := by simpa using hty1
        rw [h1] at hbs
        exact (Formalism.MainNotions.LocalTheoryWindows.LT.up.inj hbs).symm
      subst hbs'
      rw [hlen, show (3 : ℕ) = 2 + 1 from rfl]
      show dv W T₁ (2 + 1) b₁ _ ∈ _
      rw [ArcLengthThreeFiltration.dv_succ W T₁ 2]
      have h2 := ArcLengthThreeFiltration.filS_one_of W T₁ a _ _ hlt2
      rw [ha3] at h2
      exact h2)
    (by
      rw [hlen, show (3 : ℕ) = 2 + 1 from rfl]
      show Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ (2 + 1) b₁ _) = _ • dv W T₂ (2 + 1) bb _
      rw [ArcLengthThreeFiltration.dv_succ W T₁ 2, ArcLengthThreeFiltration.dv_succ W T₂ 2, ArcLengthThreeFiltration.crisMap_φ]
      have h3 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ 2 b₁ fun m => algebraMap O LL (c₁ m)) =
          ((PD.p : LL) ^ s₁) • dv W T₂ 2 bb (Pi.single k₀ 1) := hpr3
      rw [h3, map_smul])
    f (by
      simp only [Finset.prod_singleton]
      rw [hty1']
      dsimp only
      rw [← hnn]; exact hf.1)
    (fun s hs bs hbs => by
      obtain ⟨κ, x, hx⟩ := hf.2 s hs bs hbs
      refine ⟨κ, x, ?_⟩
      simp only [Finset.prod_singleton]
      rw [hty1']
      dsimp only
      rw [hnn] at hx; exact hx)
    (fun s hs hs1 bs hbs => by
      rw [hlen] at hs
      interval_cases s
      · simp [hty0] at hbs
      · simp at hs1
      · have h2 : (arcOf b w S η up size).ty (c - ((2 : ℕ) : ZMod n)) = .down (size (c - 2)) := by simpa using hty2
        rw [h2] at hbs; exact absurd hbs (by simp))
  refine ⟨s₁ + (arcOf b w S η up size).σ PD.p, ?_, hC⟩
  push_cast
  rw [hSg] at hσ ⊢
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
