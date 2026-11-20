import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruentStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.BotPairSmall.BlockK

/- English proof (translation)
Introduce `D 𝔪 o d j hj i l hi hl`. Establish `hj' : j⁻¹ ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d` using `inv_mem hj`. Rewrite `hj'` using `[GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet]`. Establish `h1` using `hj'.2 l i hi hl`. Establish `hu` using `(GlobalTheory.NormSum.PtsMem.mem_GA D _).1 j.2`.

Establish `hJJ : ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `hinv : (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h1` using `[hinv, Matrix.transpose_apply, Matrix.map_apply]`. Establish `h2` using `GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId h1`. Rewrite `h2` using `[GlobalTheory.NormSum.VacMove.sgA_sgA]`. Then use the resulting hypothesis.
-/
theorem blockJ_upper : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (o d : ℕ) (j : GA D d), j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d →
    ∀ i l : Fin d, i.1 < o → o ≤ l.1 →
      ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 o d j hj i l hi hl
  have hj' : j⁻¹ ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d := inv_mem hj
  rw [GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet] at hj'
  have h1 := hj'.2 l i hi hl
  have hu := (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 j.2
  have hJJ : ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) *
      (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by
    rw [← Units.val_mul]; simp
  have hinv : (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) =
      (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose := by
    calc _ = ((((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose *
          ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) *
          (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) := by rw [hu, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  rw [hinv, Matrix.transpose_apply, Matrix.map_apply] at h1
  have h2 := GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId h1
  rwa [GlobalTheory.NormSum.VacMove.sgA_sgA] at h2

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
theorem det_mem_OhE {D : D7} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D) : M.det ∈ OhE D := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

/- English proof (translation)
Introduce `i l` and use `by rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (h _ _) (h' _ _)`.
-/
theorem mul_mem_OhE {D : D7} {a : ℕ} (M M' : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D)
    (h' : ∀ i l, M' i l ∈ OhE D) : ∀ i l, (M * M') i l ∈ OhE D := fun i l => by
  rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (h _ _) (h' _ _)

/- English proof (translation)
Establish `hn : D.host.conj • 𝔪 ≠ ⊥` using `GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm`. Use `choose Z hZ using fun i l => GlobalTheory.CongIdx.exists_rep hn (hDt i l)`. Use `set Zm : Matrix (Fin a) (Fin a) (𝓞 D.host.E) := Matrix.of Z with hZm`. Use `set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ`. Use `set Zi : Matrix (Fin a) (Fin a) (AE D) := Zm.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) with hZi`.

Establish `hZiO : ∀ i l, Zi i l ∈ OhE D` using `fun i l => GlobalTheory.NormSum.VacMove.inc_int D _`. Establish `hP : ∀ i l, (Dp * Zi - 1) i l ∈ hatId D (D.host.conj • 𝔪)`. Introduce `i l`. Establish `e : Dp * Zi - 1 = Dp * (Zi - Dt) + (Dp * Dt - 1)`. Rewrite using `[Matrix.mul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply]`. Use `add_mem ?_ (hc i l)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hDp _ _) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.sub_apply, ← neg_sub]`. Conclude with `neg_mem (hZ m l)`. Establish `hdet` using `GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (mul_mem_OhE _ _ hDp hZiO) hP`. Establish `hZdet : Zi.det = inc D ((Zm.det : 𝓞 D.host.E) : D.host.E)`. Establish `: Zi = φ.mapMatrix Zm` using `rfl`.

Rewrite using `[this, ← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite `hdet` using `[Matrix.det_mul, hZdet]`. Take `⟨u, hu⟩` from `GlobalTheory.CongIdx.exists_rep hn (det_mem_OhE Dp hDp)`. Establish `key : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪)`.

Establish `e : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 = -(inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) * (Dp.det - inc D (u : D.host.E))) + (Dp.det * inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) - 1)` using `by push_cast; rw [map_mul]; ring`. Rewrite using `[e]`. Conclude with `add_mem (neg_mem (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.NormSum.VacMove.inc_int D _) hu)) hdet`. Take `⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩` from `hB3 D 𝔪 hcop _ _ key`. Take `⟨k, hk, hkc⟩` from `hB2 D _ a Zm f w hf hw hff hfs hfw h1f`.

Use `⟨k, hk, fun i l => ?_⟩` and prove the remaining obligations. Establish `e : (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l = (Dt i l - inc D (Z i l : D.host.E)) + (Zi - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l`. Simplify using `only [Matrix.sub_apply, hZi, Matrix.map_apply, hZm, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `add_mem (hZ i l) (hkc i l)`.
-/
theorem exists_k (hB2 : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫) (hB3 : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪)) (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (a : ℕ)
    (Dt Dp : Matrix (Fin a) (Fin a) (AE D)) (hDt : ∀ i l, Dt i l ∈ OhE D) (hDp : ∀ i l, Dp i l ∈ OhE D)
    (hc : ∀ i l, (Dp * Dt - 1) i l ∈ hatId D (D.host.conj • 𝔪)) :
    ∃ k ∈ intG D a, ∀ i l, (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈
      hatId D (D.host.conj • 𝔪) := by
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  choose Z hZ using fun i l => GlobalTheory.CongIdx.exists_rep hn (hDt i l)
  set Zm : Matrix (Fin a) (Fin a) (𝓞 D.host.E) := Matrix.of Z with hZm
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  set Zi : Matrix (Fin a) (Fin a) (AE D) := Zm.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) with hZi
  have hZiO : ∀ i l, Zi i l ∈ OhE D := fun i l => GlobalTheory.NormSum.VacMove.inc_int D _
  have hP : ∀ i l, (Dp * Zi - 1) i l ∈ hatId D (D.host.conj • 𝔪) := by
    intro i l
    have e : Dp * Zi - 1 = Dp * (Zi - Dt) + (Dp * Dt - 1) := by
      rw [Matrix.mul_sub]; abel
    rw [e, Matrix.add_apply]
    refine add_mem ?_ (hc i l)
    rw [Matrix.mul_apply]
    refine sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hDp _ _) ?_
    rw [Matrix.sub_apply, ← neg_sub]
    exact neg_mem (hZ m l)
  have hdet := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (mul_mem_OhE _ _ hDp hZiO) hP
  have hZdet : Zi.det = inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) := by
    have : Zi = φ.mapMatrix Zm := rfl
    rw [this, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, hZdet] at hdet
  obtain ⟨u, hu⟩ := GlobalTheory.CongIdx.exists_rep hn (det_mem_OhE Dp hDp)
  have key : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 =
        -(inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) * (Dp.det - inc D (u : D.host.E))) +
          (Dp.det * inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) - 1) := by
      push_cast; rw [map_mul]; ring
    rw [e]
    exact add_mem (neg_mem (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.NormSum.VacMove.inc_int D _) hu)) hdet
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ := hB3 D 𝔪 hcop _ _ key
  obtain ⟨k, hk, hkc⟩ := hB2 D _ a Zm f w hf hw hff hfs hfw h1f
  refine ⟨k, hk, fun i l => ?_⟩
  have e : (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l =
      (Dt i l - inc D (Z i l : D.host.E)) +
        (Zi - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l := by
    simp only [Matrix.sub_apply, hZi, Matrix.map_apply, hZm, Matrix.of_apply]; ring
  rw [e]
  exact add_mem (hZ i l) (hkc i l)

/- English proof (translation)
Introduce `D 𝔪 hm hcop o a d hd j hj`. Substitute `hd` using the available equality. Establish `hA` using `blockJ_upper D 𝔪 o (o + a) j hj`. Establish `hI` using `(mem_intG j).1 (GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o (o + a) hj)`. Use `set J : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := ((j : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJ`.

Use `set Ji : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := (((j⁻¹ : GA D (o + a)) : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJi`. Establish `hJO : ∀ i l, J i l ∈ OhE D` using `fun i l => (hI i l).1`. Establish `hJiO : ∀ i l, Ji i l ∈ OhE D` using `fun i l => by`. Use `(hI i l).2` as an intermediate fact. Simplify `this` using `[hJi]`.

Establish `hJJ : Ji * J = 1`. Rewrite using `[hJi, hJ, ← Units.val_mul]`. Simplify using the standard rewrite rules. Set `Dt : Matrix (Fin a) (Fin a) (AE D)` to `fun p l => J (Fin.natAdd o p) (Fin.natAdd o l)`. Set `Dp : Matrix (Fin a) (Fin a) (AE D)` to `fun p l => Ji (Fin.natAdd o p) (Fin.natAdd o l)`.

Establish `hc : ∀ p l, (Dp * Dt - 1) p l ∈ hatId D (D.host.conj • 𝔪)`. Introduce `p l`. Establish `e1` using `congrFun (congrFun hJJ (Fin.natAdd o p)) (Fin.natAdd o l)`. Rewrite `e1` using `[Matrix.mul_apply, Fin.sum_univ_add]`. Establish `e2 : (1 : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) (Fin.natAdd o p) (Fin.natAdd o l) = (1 : Matrix (Fin a) (Fin a) (AE D)) p l`.

Distinguish the cases in `h : p = l`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`. Establish `h' : Fin.natAdd o p ≠ Fin.natAdd o l` using `fun e => h (Fin.ext (by`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only [Fin.coe_natAdd] at this`. Use the proof step `omega))`. Rewrite using `[Matrix.one_apply_ne h', Matrix.one_apply_ne h]`. Rewrite `e1` using `[e2]`. Establish `e3 : (Dp * Dt - 1) p l = -∑ m : Fin o, Ji (Fin.natAdd o p) (Fin.castAdd a m) * J (Fin.castAdd a m) (Fin.natAdd o l)`.

Rewrite using `[Matrix.sub_apply, Matrix.mul_apply, ← e1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Use `neg_mem (sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hJiO _ _) (hA _ _ ?_ ?_))` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Take `⟨k, hk, hkc⟩` from `exists_k GlobalTheory.T.exists_integralUnitary_glue_idempotent (GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent GlobalTheory.T.exists_idempotent_limit_powers_integralAdeles) D 𝔪 hm hcop a Dt Dp (fun _ _ => hJO _ _) (fun _ _ => hJiO _ _) hc`. Use `⟨k, hk, fun i l => ?_⟩` and prove the remaining obligations. Use `set K := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK`. Establish `h1 : (J * (unitBlock D o a (o + a)).map (inc D)) i l = J i (Fin.natAdd o l)`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd o l)]`. Rewrite using `[Matrix.map_apply]`. Unfold `unitBlock`. Rewrite using `[Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, mul_one]`. Introduce `m _ hm`.

Establish `: ¬ (m.1 = o + l.1)` using `fun h => hm (Fin.ext (by simp only [Fin.coe_natAdd]; exact h))`. Rewrite using `[Matrix.map_apply]`. Unfold `unitBlock`. Rewrite using `[Matrix.of_apply, if_neg this, map_zero, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Matrix.sub_apply, h1]`. Use `Fin.addCases (fun i' => ?_) (fun p => ?_) i` and prove the remaining obligations. Establish `h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.castAdd a i') l = 0`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Establish `: ¬ ((Fin.castAdd a i' : Fin (o + a)).1 = o + m.1)` using `by simp only [Fin.coe_castAdd]; omega`. Rewrite using `[Matrix.map_apply]`. Unfold `unitBlock`. Rewrite using `[Matrix.of_apply, if_neg this, map_zero, zero_mul]`.

Rewrite using `[h2, sub_zero]`. Conclude with `hA _ _ (by simp) (by simp)`. Establish `h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.natAdd o p) l = K p l`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single p]`. Rewrite using `[Matrix.map_apply]`.

Unfold `unitBlock`. Rewrite using `[Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, one_mul]`. Introduce `m _ hm`. Establish `: ¬ ((Fin.natAdd o p : Fin (o + a)).1 = o + m.1)`. Simplify using `only [Fin.coe_natAdd]; intro h; exact hm (Fin.ext (by omega))`.

Rewrite using `[Matrix.map_apply]`. Unfold `unitBlock`. Rewrite using `[Matrix.of_apply, if_neg this, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[h2]`. Conclude with `hkc p l`.
-/
theorem blockJ_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (o a d : ℕ), o + a = d → ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∀ i l, (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D o a d).map (inc D) - (unitBlock D o a d).map (inc D) * (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 hm hcop o a d hd j hj
  subst hd
  have hA := blockJ_upper D 𝔪 o (o + a) j hj
  have hI := (mem_intG j).1 (GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o (o + a) hj)
  set J : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := ((j : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJ
  set Ji : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := (((j⁻¹ : GA D (o + a)) : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJi
  have hJO : ∀ i l, J i l ∈ OhE D := fun i l => (hI i l).1
  have hJiO : ∀ i l, Ji i l ∈ OhE D := fun i l => by
    have := (hI i l).2
    simpa [hJi] using this
  have hJJ : Ji * J = 1 := by
    rw [hJi, hJ, ← Units.val_mul]; simp
  let Dt : Matrix (Fin a) (Fin a) (AE D) := fun p l => J (Fin.natAdd o p) (Fin.natAdd o l)
  let Dp : Matrix (Fin a) (Fin a) (AE D) := fun p l => Ji (Fin.natAdd o p) (Fin.natAdd o l)
  have hc : ∀ p l, (Dp * Dt - 1) p l ∈ hatId D (D.host.conj • 𝔪) := by
    intro p l
    have e1 := congrFun (congrFun hJJ (Fin.natAdd o p)) (Fin.natAdd o l)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have e2 : (1 : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) (Fin.natAdd o p) (Fin.natAdd o l) =
        (1 : Matrix (Fin a) (Fin a) (AE D)) p l := by
      by_cases h : p = l
      · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h' : Fin.natAdd o p ≠ Fin.natAdd o l := fun e => h (Fin.ext (by
          have := congrArg Fin.val e; simp only [Fin.coe_natAdd] at this; omega))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h]
    rw [e2] at e1
    have e3 : (Dp * Dt - 1) p l = -∑ m : Fin o, Ji (Fin.natAdd o p) (Fin.castAdd a m) * J (Fin.castAdd a m) (Fin.natAdd o l) := by
      rw [Matrix.sub_apply, Matrix.mul_apply, ← e1]; ring
    rw [e3]
    refine neg_mem (sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hJiO _ _) (hA _ _ ?_ ?_))
    · simp
    · simp
  obtain ⟨k, hk, hkc⟩ := exists_k GlobalTheory.T.exists_integralUnitary_glue_idempotent (GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent GlobalTheory.T.exists_idempotent_limit_powers_integralAdeles) D 𝔪 hm hcop a Dt Dp (fun _ _ => hJO _ _) (fun _ _ => hJiO _ _) hc
  refine ⟨k, hk, fun i l => ?_⟩
  set K := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  have h1 : (J * (unitBlock D o a (o + a)).map (inc D)) i l = J i (Fin.natAdd o l) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd o l)]
    · rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, mul_one]
    · intro m _ hm
      have : ¬ (m.1 = o + l.1) := fun h => hm (Fin.ext (by simp only [Fin.coe_natAdd]; exact h))
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.sub_apply, h1]
  refine Fin.addCases (fun i' => ?_) (fun p => ?_) i
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.castAdd a i') l = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have : ¬ ((Fin.castAdd a i' : Fin (o + a)).1 = o + m.1) := by simp only [Fin.coe_castAdd]; omega
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
    rw [h2, sub_zero]
    exact hA _ _ (by simp) (by simp)
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.natAdd o p) l = K p l := by
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, one_mul]
      · intro m _ hm
        have : ¬ ((Fin.natAdd o p : Fin (o + a)).1 = o + m.1) := by
          simp only [Fin.coe_natAdd]; intro h; exact hm (Fin.ext (by omega))
        rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2]
    exact hkc p l

end GlobalTheory.BotPairSmall.BlockK
