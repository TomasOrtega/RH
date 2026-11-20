import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramSumElimSmulSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordHeight

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
include hϖ

/- English proof (translation)
Establish `h` using `(GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero`. Rewrite `h` using `[mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vE_one : vE L ϖ (algebraMap F E 1) = 0 := by
  have h := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/- English proof (translation)
Take `⟨hadd, -, hint, -⟩` from `GlobalTheory.UnramVal.vE_valuation L ϖ hϖ`. Take `⟨-, -, -, -, hO, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Take `⟨y, hy, hxy⟩` from `h2`. Establish `e : y = algebraMap F E x⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Establish `a1` using `(hint x hx).2 ((hO x).1 h1)`. Establish `a2` using `(hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))`. Establish `a3` using `hadd x x⁻¹ hx (inv_ne_zero hx)`. Rewrite `a3` using `[mul_inv_cancel₀ hx, vE_one L ϖ hϖ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vE_unit (x : F) (hx : x ≠ 0) (h1 : algebraMap F E x ∈ L.O)
    (h2 : ∃ y ∈ L.O, algebraMap F E x * y = 1) : vE L ϖ (algebraMap F E x) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨-, -, -, -, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨y, hy, hxy⟩ := h2
  have e : y = algebraMap F E x⁻¹ := by
    calc y = algebraMap F E (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
      _ = algebraMap F E x⁻¹ := by rw [map_mul, mul_assoc, hxy, mul_one]
  have a1 := (hint x hx).2 ((hO x).1 h1)
  have a2 := (hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))
  have a3 := hadd x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vE_one L ϖ hϖ] at a3
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using vE_one L ϖ hϖ`. Consider the case `succ n ih`. Rewrite using `[pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vE_pow (x : F) (hx : x ≠ 0) (n : ℕ) :
    vE L ϖ (algebraMap F E (x ^ n)) = n * vE L ϖ (algebraMap F E x) := by
  induction n with
  | zero => simpa using vE_one L ϖ hϖ
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

/- English proof (translation)
Establish `h` using `vE_pow L ϖ hϖ (-1) (by simp) 2`. Rewrite `h` using `[neg_one_sq, vE_one L ϖ hϖ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vE_neg_one : vE L ϖ (algebraMap F E (-1)) = 0 := by
  have h := vE_pow L ϖ hϖ (-1) (by simp) 2
  rw [neg_one_sq, vE_one L ϖ hϖ] at h
  omega

omit [IsNonarchimedeanLocalField F] [CharZero F] hϖ in
/- English proof (translation)
Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`. Take `⟨c, hc⟩` from `(L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])`. Use `⟨c, ?_, hc.symm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`.

Conclude with `(hx.mul (hx.map L.cj)).ne_zero hc.symm`.
-/
theorem norm_mem (x : E) (hx : IsUnit x) : ∃ c : F, c ≠ 0 ∧ x * L.cj x = algebraMap F E c := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨c, hc⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [map_zero] at hc
  exact (hx.mul (hx.map L.cj)).ne_zero hc.symm

end Val

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
include c

/- English proof (translation)
Establish `hZ : H.Zhat P.A.f P.B.f = S.Zh`. Use extensionality with `a b`. Simplify using `only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]`. Unfold `LocNG.FPair.Dm HermSp.Dl Frames.D lead`. Rewrite using `[dif_pos (Nat.lt_succ_iff.mp l.2), hZ]`.
-/
theorem Dm_eq (l : Fin (r + 2)) : P.Dm l = S.D l := by
  have hZ : H.Zhat P.A.f P.B.f = S.Zh := by
    ext a b
    simp only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  unfold LocNG.FPair.Dm HermSp.Dl Frames.D lead
  rw [dif_pos (Nat.lt_succ_iff.mp l.2), hZ]

/- English proof (translation)
Establish `h1` using `Dm_eq c (Fin.last (r + 1))`. Establish `h2` using `Dm_eq c (Fin.last r).castSucc`. Unfold `LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G`. Rewrite using `[← h1, ← h2, c.T_eq, c.T'_eq]`. Both sides reduce to the same expression.
-/
theorem Gv_eq : P.Gv = S.G := by
  have h1 := Dm_eq c (Fin.last (r + 1))
  have h2 := Dm_eq c (Fin.last r).castSucc
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G
  rw [← h1, ← h2, c.T_eq, c.T'_eq]
  rfl

/- English proof (translation)
Unfold `LocNG.theta Frames.th`. Consider the cases of `h : M.split with`. Consider the case `none => simp [c.gg_none h]`. Consider the case `some g`. Take `⟨h1, h2⟩` from `c.gg_some g h`.

Simplify using `[h1, h2]`.
-/
theorem theta_eq : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  cases h : M.split with
  | none => simp [c.gg_none h]
  | some g =>
    obtain ⟨h1, h2⟩ := c.gg_some g h
    simp [h1, h2]

end Transport

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c`. Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Take `⟨hq, hmod⟩` from `GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr`. Take `⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩` from `GlobalTheory.FrameBasic.main M.L r k S`.

Take `⟨hadd, hvp, -, -⟩` from `GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr`. Take `⟨-, hcj, -, -, -, -, hq2, -⟩` from `GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr`. Establish `hnt : Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)`. Establish `hgram` using `GlobalTheory.det_gram_frame_generators M hM H r k P`. Rewrite `hgram` using `[theta_eq c, Gv_eq c, hg]`.

Establish `hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth`. Unfold `Frames.th Frames.vth`. Use `split_ifs`. Conclude with `hvp`. Conclude with `vE_one M.L S.ϖ S.ϖ_irr`.

Establish `hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0`. Introduce `l`. Unfold `LocNG.FPair.ends`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Rewrite using `[Dm_eq c]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h1, h2⟩`. Use `⟨?_, h2.ne_zero⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at h1`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨l.2, ?_, hD l h2⟩` and prove the remaining obligations. Conclude with `Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)`. Use `⟨?_, hq, ?_⟩` and prove the remaining obligations. Establish `hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ)`.

Establish `: 0 < resQ S.ϖ` using `by omega`. Conclude with `this` after adjusting the coercions. Use `set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd`. Establish `hp0 : S.th ^ (2 * (r + 1)) ≠ 0` using `pow_ne_zero _ hth`. Establish `hs0 : ((-1 : F) ^ (r + 1)) ≠ 0` using `pow_ne_zero _ (by simp)`.

Establish `hd0 : d ≠ 0` using `mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)`. Establish `hdet : (H.gram P.MMgen).det = algebraMap F E d`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_cancel₀ hp0, map_one, mul_one]`. Use `_ = algebraMap F E d := by`.

Rewrite using `[map_mul, ← mul_assoc, map_pow, hgram, hd]`. Simplify using `only [map_mul, map_pow, map_neg, map_one]`. Establish `hva : vE M.L S.ϖ (algebraMap F E d) = S.a`. Establish `e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g`. Rewrite using `[hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]`.

Establish `h1` using `hadd _ _ hd0 hp0`. Rewrite `h1` using `[e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp), vE_neg_one M.L S.ϖ S.ϖ_irr, hvth]`. Unfold `Frames.a`. Rewrite using `[hg]`. Move the coercions through the operations in `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD))`. Establish `hsub : P.ends ⊆ Finset.range (r + 2)`. Unfold `LocNG.FPair.ends`. Conclude with `@Finset.filter_subset _ _ (_) _`.

Rewrite using `[← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]`. Unfold `Frames.vD`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Establish `hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ), (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i`. Introduce `s f`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]`. Rewrite using `[hz]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : l ≠ 0 ∧ S.D l ≠ 0`. Rewrite using `[if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]`. Take `⟨n, hn0, hn⟩` from `norm_mem M.L _ (hD l hl.2)`. Rewrite using `[hn, hmod n hn0]`. Rewrite using `[if_neg (fun h => hl ((hends l).1 h)), if_neg hl]`.

Simplify using the standard rewrite rules. Unfold `LocNG.FPair.Hp Frames.Hp Frames.q`. Rewrite using `[hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne', ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨c.gg_none h1, ?_, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[Gv_eq c, hg]`. Rewrite using `[hg]`.

Conclude with `vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2`. Establish `hu : LocNG.IsUnitO M (S.D l)`. Distinguish the cases in `h0 : l = 0`. Establish `: S.D l = 1`. Substitute `h0` using the available equality.

Unfold `Frames.D lead`. Conclude with `Matrix.det_isEmpty (n := Fin 0)`. Rewrite using `[this]`. Conclude with `⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩`. Use `h3 l ((hends l).2 ⟨h0, hl⟩)` as an intermediate fact.

Rewrite `this` using `[Dm_eq c]`. Then use the resulting hypothesis. Take `⟨n, hn0, hn⟩` from `norm_mem M.L _ (hD l hl)`. Take `⟨hm, y, hy, hxy⟩` from `hu`. Rewrite using `[hn]`. Use `vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hn]`. Conclude with `M.L.O.mul_mem hm (hcj _ hm).1`. Rewrite using `[← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]`.
-/
theorem height_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have := hM.loc
  have := hM.char0
  obtain ⟨hq, hmod⟩ := GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr
  obtain ⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨hadd, hvp, -, -⟩ := GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr
  obtain ⟨-, hcj, -, -, -, -, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  have hgram := GlobalTheory.det_gram_frame_generators M hM H r k P
  rw [theta_eq c, Gv_eq c, hg] at hgram
  have hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hvp
    · exact vE_one M.L S.ϖ S.ϖ_irr
  have hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0 := by
    intro l
    unfold LocNG.FPair.ends
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Dm_eq c]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨?_, h2.ne_zero⟩
      rintro rfl
      simp at h1
    · rintro ⟨h1, h2⟩
      refine ⟨l.2, ?_, hD l h2⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)
  refine ⟨?_, hq, ?_⟩
  · have hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ) := by
      have : 0 < resQ S.ϖ := by omega
      exact_mod_cast this
    set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd
    have hp0 : S.th ^ (2 * (r + 1)) ≠ 0 := pow_ne_zero _ hth
    have hs0 : ((-1 : F) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)
    have hdet : (H.gram P.MMgen).det = algebraMap F E d := by
      calc (H.gram P.MMgen).det
          = (H.gram P.MMgen).det * algebraMap F E (S.th ^ (2 * (r + 1)) * (S.th ^ (2 * (r + 1)))⁻¹) := by
            rw [mul_inv_cancel₀ hp0, map_one, mul_one]
        _ = algebraMap F E d := by
            rw [map_mul, ← mul_assoc, map_pow, hgram, hd]
            simp only [map_mul, map_pow, map_neg, map_one]
    have hva : vE M.L S.ϖ (algebraMap F E d) = S.a := by
      have e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g := by
        rw [hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
      have h1 := hadd _ _ hd0 hp0
      rw [e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp),
        vE_neg_one M.L S.ϖ S.ϖ_irr, hvth] at h1
      unfold Frames.a
      rw [hg]
      push_cast at h1
      linarith
    have hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD)) := by
      have hsub : P.ends ⊆ Finset.range (r + 2) := by
        unfold LocNG.FPair.ends
        exact @Finset.filter_subset _ _ (_) _
      rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]
      unfold Frames.vD
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ),
          (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]
      rw [hz]
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l ≠ 0 ∧ S.D l ≠ 0
      · rw [if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]
        obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl.2)
        rw [hn, hmod n hn0]
      · rw [if_neg (fun h => hl ((hends l).1 h)), if_neg hl]
        simp
    unfold LocNG.FPair.Hp Frames.Hp Frames.q
    rw [hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne',
      ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.gg_none h1, ?_, fun l hl => ?_⟩
    · rw [Gv_eq c, hg] at h2
      rw [hg]
      exact vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2
    · have hu : LocNG.IsUnitO M (S.D l) := by
        by_cases h0 : l = 0
        · have : S.D l = 1 := by
            subst h0
            unfold Frames.D lead
            exact Matrix.det_isEmpty (n := Fin 0)
          rw [this]
          exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
        · have := h3 l ((hends l).2 ⟨h0, hl⟩)
          rwa [Dm_eq c] at this
      obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl)
      obtain ⟨hm, y, hy, hxy⟩ := hu
      rw [hn]
      refine vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩
      · rw [← hn]
        exact M.L.O.mul_mem hm (hcj _ hm).1
      · rw [← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]

end GlobalTheory.HL.CoordHeight
