import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

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
Establish `hj2 : A.j ≤ 2` using `by rw [hj]; norm_num`. Establish `h2l : 2 ≤ A.len c` using `by rw [hlen]; norm_num`. Take `⟨⟨u, hu, hJJ⟩, hT⟩` from `hArc hcase hl5 A hOK c hc 2 hj2 h2l`. Take `⟨-, -, -, hfr⟩` from `hT T₂ hW₂`. Take `⟨-, -, hc3, -, -, -, hcrit⟩` from `hfr d bb sol hbb`.

Establish `hFL'` using `hFL hcase hl5 A hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) 1 (by norm_num)`. Use `set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'`. Use `set a : ZMod n := c' + ((2 : ℕ) : ZMod n) with ha_def`. Establish `ha : a = c - 1` using `by rw [ha_def, hc', hlen]; push_cast; ring`. Use `set Λ : LetA O n := abelian₂ W A a 2 with hΛdef`.

Establish `hps0 : ps W 0 = qA W` using `by simp [ps]`. Establish `hHs0 : A.Hs a 2 0 = A.h`. Unfold `ArcP.Hs`. Rewrite using `[if_neg]`. Use `push Not`.

Use `⟨?_, by rw [hj]; norm_num⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_zero, sub_zero, ha, hty1]`. Introduce `h`. Consider the cases of `h`. Establish `hHs1 : A.Hs a 2 1 = A.G₀`.

Unfold `ArcP.Hs`. Rewrite using `[if_pos (Or.inr (by rw [hj]))]`. Establish `hΛ : Λ = qA W ^ A.h * ps W 1 ^ A.G₀`. Rewrite using `[hΛdef, abelian₂, Finset.prod_range_succ, Finset.prod_range_one, hHs0, hHs1, hps0]`. Establish `hb1h : b₁ + A.S ≤ A.h`.

Use `hOK.2.2.2.2.2.2.2.1 (c - 1) (by rw [hty1]; rfl)` as an intermediate fact. Rewrite `this` using `[hty1]`. Then use the resulting hypothesis. Establish `hw'η : A.η < w'`. Use `hOK.2.2.2.2.1 (c - 2)` as an intermediate fact. Rewrite `this` using `[hty2]`. Then use the resulting hypothesis.

Establish `hqmem : qA W ∈ W.AΔ` using `by rw [← hps0]; exact TypesA.ps_mem W 0`. Use `set R : LetA O n := qA W ^ (A.h - b₁) * ps W 1 ^ (A.G₀ + (w' + A.S)) with hRdef`. Establish `hRmem : R ∈ W.AΔ` using `W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)`. Establish `hΛs : (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) R`. Establish `hq : qA W ^ A.h = qA W ^ (A.h - b₁) * qA W ^ b₁`.

Rewrite using `[← pow_add, Nat.sub_add_cancel (by omega)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hΛ, hq]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * (algebraMap (LetA O n) W.EE) (ps W 1 ^ (w' + A.S)) := by rw [hs]`. Use `_ = (algebraMap (LetA O n) W.EE) R := by rw [hRdef]; simp only [pow_add, map_mul]; ring`. Establish `hΛx : Λ • (s • lam) = R • lam`. Rewrite using `[← algebraMap_smul W.EE Λ (s • lam), smul_smul, hΛs, algebraMap_smul]`. Establish `hInFP : InFP W T₂ c' 2 1 (Λ • (s • lam))`.

Rewrite using `[hΛx]`. Take `⟨y, hy, rfl⟩` from `hlam`. Conclude with `⟨R • y, TypesA.Pp_smul W hRmem hy, by rw [one_smul, one_smul]⟩`. Establish `hΛmem : Λ ∈ W.AΔ` using `TypesA.Ps_mem W (TC.lam_mem_Ps W A a 2)`. Establish `hletmem : (letE a : LetA O n) ∈ W.AΔ` using `TypesD.letE_mem W a`.

Take `⟨-, -, κ₁, κ₁', Hh1, a1, hHh1, -, -⟩` from `hc3 (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) else 0) (by`. Introduce `k`. Distinguish the cases in `hk : k = k₀`. Simplify using `only [if_pos hk]`. Conclude with `⟨Λ, hΛmem, by rw [← map_mul]; congr 1; ring⟩`.

Simplify using `only [if_neg hk]`. Conclude with `⟨0, W.AΔ.zero_mem, by simp⟩)`. Use `set σ := A.σ PD.p with hσdef`. Take `⟨κ', y, hy, hyeq⟩` from `h4a`. Rewrite `hJJ` using `[hj]`.

Establish `hJJ' : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) = W.π₀ * Λ ^ 2 * u`. Rewrite using `[← hJJ]`. Simplify using the standard rewrite rules. Establish `hlet2 : (letE a : LetA O n) • ((W.φD T₂) ^ 2) Hh = ((W.φD T₂) ^ 2) Hh` using `TypesD.φDpow_letter W (TypesD.horTr_letter W hbb hHh) 2`. Establish `hφl : ((W.φD T₂) ^ 2) (lA W ^ κ₁ • Hh) = lA W ^ κ₁ • ((W.φD T₂) ^ 2) Hh`.

Rewrite using `[← TypesA.pO_smul, map_smul, TypesA.pO_smul]`. Establish `hRep : RepVV W T₂ c' 2 (A.M PD.p) Λ bb sol (lA W ^ 0 • (s • lam)) (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0)`. Use `⟨κ + κ₁, κ', fun k => if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k, fun k => if k = k₀ then letE a * R * lA W ^ σ else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Distinguish the cases in `hk : k = k₀`.

Substitute `hk` using the available equality. Simplify using `only [if_pos rfl]`. Conclude with `TypesA.IsHorTr_smul W κ₁ hHh`. Simplify using `only [if_neg hk]`. Rewrite using `[add_comm]`.

Conclude with `TypesA.IsHorTr_smul W κ (hHh1 k)`. Introduce `k`. Distinguish the cases in `hk : k = k₀`. Simplify using `only [if_pos hk]`. Use `⟨W.AΔ.mul_mem (W.AΔ.mul_mem hletmem hRmem) (TypesA.lA_pow_mem W σ), ?_⟩` and prove the remaining obligations.

Rewrite using `[TC.lE_eq W σ]`. Rewrite using `[show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg hk]; exact ⟨W.AΔ.zero_mem, by simp⟩`.

Establish `hsum : ∑ k, (if k = k₀ then letE a * R * lA W ^ σ else 0) • ((W.φD T₂) ^ 2) (if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k) = (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh`. Rewrite using `[Finset.sum_eq_single k₀ (fun k _ hk => by simp only [if_neg hk, zero_smul]) (by simp)]`. Rewrite using `[if_pos rfl, if_pos rfl]`. Rewrite using `[hφl, smul_smul, show letE a * R * lA W ^ σ * lA W ^ κ₁ = (R * lA W ^ σ * lA W ^ κ₁) * letE a by ring, mul_smul, hlet2]`. Rewrite using `[hsum, pow_zero, one_smul, hΛx]`.

Use `⟨(u * (R * lA W ^ κ₁)) • y, TypesA.Pp_smul W (W.AΔ.mul_mem hu (W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W κ₁))) hy, ?_⟩` and prove the remaining obligations. Establish `e1 : lA W ^ κ' • (lA W ^ (κ + κ₁) • R • lam - (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh) = (R * lA W ^ κ₁) • (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ σ • ((W.φD T₂) ^ 2) Hh))`. Simplify using `only [smul_sub, smul_smul]`. Apply the tactic sequence `congr 2 <;> ring`. Rewrite using `[e1, hyeq, hJJ', smul_smul, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hfr : ∀ m, InFr W a 1 Λ (if m = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0)`. Introduce `m`. Distinguish the cases in `hm : m = k₀`.

Simplify using `only [if_pos hm]`. Use `⟨R * lA W ^ σ, W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W σ), ?_⟩` and prove the remaining obligations. Rewrite using `[TC.lE_eq W σ]`. Rewrite using `[show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]`. Simplify using `only [map_mul, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg hm]; exact ⟨0, W.AΔ.zero_mem, by simp⟩`. Establish `hN : InFNc W T₂ a 1 (s • lam)`. Use `(hcrit (s • lam) 0 _ hInFP hRep hfr).2 ⟨0, 1, fun _ => (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s, fun _ => Pi.single k₀ 1, fun _ t => if t = 0 then -(b₁ : ℤ) else ((w' + A.S : ℕ) : ℤ), fun _ => ⟨?_, ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Use `⟨lA W ^ σ, TypesA.lA_pow_mem W σ, ?_⟩` and prove the remaining obligations.

Establish `e1 : (-(b₁ : ℤ)).toNat = 0` using `by omega`. Establish `e2 : (-(-(b₁ : ℤ))).toNat = b₁` using `by omega`. Establish `e3 : (((w' + A.S : ℕ) : ℤ)).toNat = w' + A.S` using `by omega`. Establish `e4 : (-(((w' + A.S : ℕ) : ℤ))).toNat = 0` using `by omega`. Simplify using `only [Finset.prod_range_succ, Finset.prod_range_zero, one_ne_zero, ↓reduceIte, e1, e2, e3, e4, pow_zero, one_mul, mul_one, hps0]`.

Rewrite using `[TC.lE_eq W σ]`. Simplify using `only [map_mul]`. Rewrite using `[show (algebraMap (LetA O n) W.EE) (qA W ^ b₁) * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s) by ring, hs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `t ht interval_cases t`.

Simplify using `only [↓reduceIte, neg_neg]`. Rewrite `hFil` using `[hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthTwo.dv_succ]`. Rewrite using `[ArcLengthTwo.dvO_single]`. Conclude with `ArcLengthTwo.filS_φ_inv W T₂ (by rw [ha]; push_cast; ring) hFil`. Simplify using `only [one_ne_zero, ↓reduceIte]`.

Use `hFL'.1 _ fun x hx => ?_` and prove the remaining obligations. Establish `e : a - ((1 : ℕ) : ZMod n) = c - 2` using `by rw [ha]; push_cast; ring`. Rewrite `hx` using `[e, hty2]`. Simplify using `only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.sum_univ_one, lE, pow_zero, one_mul]`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[if_neg hk, Pi.single_apply, hk]`. Take `⟨y, hyΔ, hyl, hxy⟩` from `hN`. Rewrite using `[← ha, hxy, one_smul]`. Conclude with `⟨hyΔ, ⟨y, hyΔ.1, by simpa using hyl⟩⟩`.
-/
theorem arc_length_three_hyp_first (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl5 : 5 ≤ PD.p)
    (hArc : ArcCore W) (hFL : ArcFilLowCore W) (A : ArcP n) (hOK : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (hlen : A.len c = 3) (hj : A.j = 1) {b₁ w' : ℕ} (hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up b₁)
    (hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down w')
    {T₂ : LocLat G Qp LL O} (hW₂ : Win W A T₂) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 b₁)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 1 lam) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol (A.M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2
      (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ (A.σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) := by
  classical
  have hj2 : A.j ≤ 2 := by rw [hj]; norm_num
  have h2l : 2 ≤ A.len c := by rw [hlen]; norm_num
  obtain ⟨⟨u, hu, hJJ⟩, hT⟩ := hArc hcase hl5 A hOK c hc 2 hj2 h2l
  obtain ⟨-, -, -, hfr⟩ := hT T₂ hW₂
  obtain ⟨-, -, hc3, -, -, -, hcrit⟩ := hfr d bb sol hbb
  have hFL' := hFL hcase hl5 A hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) 1 (by norm_num)
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a : ZMod n := c' + ((2 : ℕ) : ZMod n) with ha_def
  have ha : a = c - 1 := by rw [ha_def, hc', hlen]; push_cast; ring
  set Λ : LetA O n := abelian₂ W A a 2 with hΛdef
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hHs0 : A.Hs a 2 0 = A.h := by
    unfold ArcP.Hs
    rw [if_neg]
    push Not
    refine ⟨?_, by rw [hj]; norm_num⟩
    rw [Nat.cast_zero, sub_zero, ha, hty1]
    intro h; cases h
  have hHs1 : A.Hs a 2 1 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by rw [hj]))]
  have hΛ : Λ = qA W ^ A.h * ps W 1 ^ A.G₀ := by
    rw [hΛdef, abelian₂, Finset.prod_range_succ, Finset.prod_range_one, hHs0, hHs1, hps0]
  have hb1h : b₁ + A.S ≤ A.h := by
    have := hOK.2.2.2.2.2.2.2.1 (c - 1) (by rw [hty1]; rfl)
    rwa [hty1] at this
  have hw'η : A.η < w' := by
    have := hOK.2.2.2.2.1 (c - 2)
    rwa [hty2] at this
  have hqmem : qA W ∈ W.AΔ := by rw [← hps0]; exact TypesA.ps_mem W 0
  set R : LetA O n := qA W ^ (A.h - b₁) * ps W 1 ^ (A.G₀ + (w' + A.S)) with hRdef
  have hRmem : R ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
  have hΛs : (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) R := by
    have hq : qA W ^ A.h = qA W ^ (A.h - b₁) * qA W ^ b₁ := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    calc (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s) := by
          rw [hΛ, hq]; simp only [map_mul]; ring
      _ = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * (algebraMap (LetA O n) W.EE) (ps W 1 ^ (w' + A.S)) := by rw [hs]
      _ = (algebraMap (LetA O n) W.EE) R := by rw [hRdef]; simp only [pow_add, map_mul]; ring
  have hΛx : Λ • (s • lam) = R • lam := by
    rw [← algebraMap_smul W.EE Λ (s • lam), smul_smul, hΛs, algebraMap_smul]
  have hInFP : InFP W T₂ c' 2 1 (Λ • (s • lam)) := by
    rw [hΛx]
    obtain ⟨y, hy, rfl⟩ := hlam
    exact ⟨R • y, TypesA.Pp_smul W hRmem hy, by rw [one_smul, one_smul]⟩
  have hΛmem : Λ ∈ W.AΔ := TypesA.Ps_mem W (TC.lam_mem_Ps W A a 2)
  have hletmem : (letE a : LetA O n) ∈ W.AΔ := TypesD.letE_mem W a

  obtain ⟨-, -, κ₁, κ₁', Hh1, a1, hHh1, -, -⟩ := hc3 (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) else 0) (by
    intro k
    by_cases hk : k = k₀
    · simp only [if_pos hk]
      exact ⟨Λ, hΛmem, by rw [← map_mul]; congr 1; ring⟩
    · simp only [if_neg hk]
      exact ⟨0, W.AΔ.zero_mem, by simp⟩)
  set σ := A.σ PD.p with hσdef
  obtain ⟨κ', y, hy, hyeq⟩ := h4a
  rw [hj] at hJJ
  have hJJ' : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) = W.π₀ * Λ ^ 2 * u := by
    rw [← hJJ]; simp
  have hlet2 : (letE a : LetA O n) • ((W.φD T₂) ^ 2) Hh = ((W.φD T₂) ^ 2) Hh :=
    TypesD.φDpow_letter W (TypesD.horTr_letter W hbb hHh) 2
  have hφl : ((W.φD T₂) ^ 2) (lA W ^ κ₁ • Hh) = lA W ^ κ₁ • ((W.φD T₂) ^ 2) Hh := by
    rw [← TypesA.pO_smul, map_smul, TypesA.pO_smul]
  have hRep : RepVV W T₂ c' 2 (A.M PD.p) Λ bb sol (lA W ^ 0 • (s • lam))
      (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    refine ⟨κ + κ₁, κ', fun k => if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k,
      fun k => if k = k₀ then letE a * R * lA W ^ σ else 0, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = k₀
      · subst hk; simp only [if_pos rfl]; exact TypesA.IsHorTr_smul W κ₁ hHh
      · simp only [if_neg hk]; rw [add_comm]; exact TypesA.IsHorTr_smul W κ (hHh1 k)
    · intro k
      by_cases hk : k = k₀
      · simp only [if_pos hk]
        refine ⟨W.AΔ.mul_mem (W.AΔ.mul_mem hletmem hRmem) (TypesA.lA_pow_mem W σ), ?_⟩
        rw [TC.lE_eq W σ]
        rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
        simp only [map_mul]; ring
      · simp only [if_neg hk]; exact ⟨W.AΔ.zero_mem, by simp⟩
    · have hsum : ∑ k, (if k = k₀ then letE a * R * lA W ^ σ else 0) •
          ((W.φD T₂) ^ 2) (if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k) =
          (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh := by
        rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp only [if_neg hk, zero_smul]) (by simp)]
        rw [if_pos rfl, if_pos rfl]
        rw [hφl, smul_smul, show letE a * R * lA W ^ σ * lA W ^ κ₁ = (R * lA W ^ σ * lA W ^ κ₁) * letE a by ring,
          mul_smul, hlet2]
      rw [hsum, pow_zero, one_smul, hΛx]
      refine ⟨(u * (R * lA W ^ κ₁)) • y, TypesA.Pp_smul W (W.AΔ.mul_mem hu (W.AΔ.mul_mem hRmem
        (TypesA.lA_pow_mem W κ₁))) hy, ?_⟩
      have e1 : lA W ^ κ' • (lA W ^ (κ + κ₁) • R • lam - (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh) =
          (R * lA W ^ κ₁) • (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ σ • ((W.φD T₂) ^ 2) Hh)) := by
        simp only [smul_sub, smul_smul]
        congr 2 <;> ring
      rw [e1, hyeq, hJJ', smul_smul, smul_smul]
      congr 1
      ring
  have hfr : ∀ m, InFr W a 1 Λ (if m = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    intro m
    by_cases hm : m = k₀
    · simp only [if_pos hm]
      refine ⟨R * lA W ^ σ, W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W σ), ?_⟩
      rw [TC.lE_eq W σ]
      rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
      simp only [map_mul, map_one]; ring
    · simp only [if_neg hm]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
  have hN : InFNc W T₂ a 1 (s • lam) := by
    refine (hcrit (s • lam) 0 _ hInFP hRep hfr).2 ⟨0, 1, fun _ => (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s,
      fun _ => Pi.single k₀ 1, fun _ t => if t = 0 then -(b₁ : ℤ) else ((w' + A.S : ℕ) : ℤ),
      fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
    · refine ⟨lA W ^ σ, TypesA.lA_pow_mem W σ, ?_⟩
      have e1 : (-(b₁ : ℤ)).toNat = 0 := by omega
      have e2 : (-(-(b₁ : ℤ))).toNat = b₁ := by omega
      have e3 : (((w' + A.S : ℕ) : ℤ)).toNat = w' + A.S := by omega
      have e4 : (-(((w' + A.S : ℕ) : ℤ))).toNat = 0 := by omega
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_ne_zero, ↓reduceIte,
        e1, e2, e3, e4, pow_zero, one_mul, mul_one, hps0]
      rw [TC.lE_eq W σ]
      simp only [map_mul]
      rw [show (algebraMap (LetA O n) W.EE) (qA W ^ b₁) * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s)
        by ring, hs]
      ring
    · intro t ht
      interval_cases t
      · simp only [↓reduceIte, neg_neg]
        rw [hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthTwo.dv_succ] at hFil
        rw [ArcLengthTwo.dvO_single]
        exact ArcLengthTwo.filS_φ_inv W T₂ (by rw [ha]; push_cast; ring) hFil
      · simp only [one_ne_zero, ↓reduceIte]
        refine hFL'.1 _ fun x hx => ?_
        have e : a - ((1 : ℕ) : ZMod n) = c - 2 := by rw [ha]; push_cast; ring
        rw [e, hty2] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
        push_cast
        omega
    · simp only [Fin.sum_univ_one, lE, pow_zero, one_mul]
      by_cases hk : k = k₀
      · subst hk; simp
      · simp [if_neg hk, Pi.single_apply, hk]
  obtain ⟨y, hyΔ, hyl, hxy⟩ := hN
  rw [← ha, hxy, one_smul]
  exact ⟨hyΔ, ⟨y, hyΔ.1, by simpa using hyl⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
