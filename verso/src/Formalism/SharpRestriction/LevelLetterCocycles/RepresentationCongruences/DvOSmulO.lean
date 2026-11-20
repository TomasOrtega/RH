import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ProdTwoLevelsEqConst
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.MemPairXIff

open scoped TensorProduct

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

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

/- English proof (translation)
Unfold `dvO dv`. Simplify using `only [map_mul, mul_smul, Finset.smul_sum]`.
-/
theorem dvO_smulO (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (r : O) (x : Fin d → O) :
    dvO W T e b (fun k => r * x k) = algebraMap O LL r • dvO W T e b x := by
  unfold dvO dv
  simp only [map_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Unfold `dvO dv`. Simplify using `only [map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : ℕ} (t : Fin I → O)
    (c : Fin I → Fin d → O) :
    dvO W T e b (fun k => ∑ i, t i * c i k) = ∑ i, algebraMap O LL (t i) • dvO W T e b (c i) := by
  unfold dvO dv
  simp only [map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Unfold `IsDist PhiData.p`. Simplify using `only [Function.iterate_one]`. Establish `hp1 : 1 ≤ PD.p` using `Nat.pos_of_ne_zero (fun h => Br.P.hl0 (by rw [h, Nat.cast_zero]))`. Establish `hC : (PowerSeries.C (PD.p : O) : O⟦X⟧) = (PD.p : O⟦X⟧)` using `map_natCast _ _`. Establish `h0` using `Br.P.hφ0`.

Rewrite `h0` using `[hC, map_sub, map_natCast]`. Establish `hφX : Br.P.φ X = Br.P.u * (X - (PD.p : O⟦X⟧)) * X ^ (PD.p - 1) + (PD.p : O⟦X⟧)`. Rewrite using `[← h0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : ((PD.p : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0`.

Establish `h1 : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O)]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).mpr Br.P.hl`. Rewrite using `[← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), h1, map_zero]`. Establish `hm : (Br.P.φ X).map (IsLocalRing.residue O) = (Br.P.u.map (IsLocalRing.residue O)) * X ^ PD.p`.

Rewrite using `[hφX, map_add, map_mul, map_mul, map_pow, map_sub, PowerSeries.map_X, map_natCast, hp0, sub_zero, add_zero, mul_assoc, ← pow_succ', Nat.sub_add_cancel hp1]`. Establish `hu0 : Br.P.u.map (IsLocalRing.residue O) ≠ 0` using `(Br.P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero`. Rewrite using `[map_mul, map_pow, map_pow, PowerSeries.map_X, hm]`. Conclude with `mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ (mul_ne_zero hu0 (pow_ne_zero _ PowerSeries.X_ne_zero)))`.
-/
theorem isDist_XP (i j : ℕ) : IsDist ((X : PowerSeries O) ^ i * Br.P.p 1 ^ j) := by
  unfold IsDist PhiData.p
  simp only [Function.iterate_one]
  have hp1 : 1 ≤ PD.p := Nat.pos_of_ne_zero (fun h => Br.P.hl0 (by rw [h, Nat.cast_zero]))
  have hC : (PowerSeries.C (PD.p : O) : O⟦X⟧) = (PD.p : O⟦X⟧) := map_natCast _ _
  have h0 := Br.P.hφ0
  rw [hC, map_sub, map_natCast] at h0
  have hφX : Br.P.φ X = Br.P.u * (X - (PD.p : O⟦X⟧)) * X ^ (PD.p - 1) + (PD.p : O⟦X⟧) := by
    rw [← h0]
    ring
  have hp0 : ((PD.p : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    have h1 : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
      rw [← map_natCast (IsLocalRing.residue O)]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr Br.P.hl
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), h1, map_zero]
  have hm : (Br.P.φ X).map (IsLocalRing.residue O) = (Br.P.u.map (IsLocalRing.residue O)) * X ^ PD.p := by
    rw [hφX, map_add, map_mul, map_mul, map_pow, map_sub, PowerSeries.map_X, map_natCast, hp0, sub_zero,
      add_zero, mul_assoc, ← pow_succ', Nat.sub_add_cancel hp1]
  have hu0 : Br.P.u.map (IsLocalRing.residue O) ≠ 0 :=
    (Br.P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero
  rw [map_mul, map_pow, map_pow, PowerSeries.map_X, hm]
  exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
    (pow_ne_zero _ (mul_ne_zero hu0 (pow_ne_zero _ PowerSeries.X_ne_zero)))

/- English proof (translation)
Use `Fact.mk PD.hp` as an intermediate fact. Take `⟨hfr, κ, I, g, c₀, α, hmon, hsum⟩` from `hf`. Establish `hXu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst X))` using `Br.qA_eq ▸ hq`. Establish `hPu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst (Br.P.p 1)))` using `(ps_cst Br 1) ▸ hp`. Establish `hcu : ∀ i j : ℕ, IsUnit (algebraMap (LetA O n) W.EE (Br.cst (X ^ i * Br.P.p 1 ^ j)))`.

Introduce `i j`. Rewrite using `[Br.cst_mul, Br.cst_pow, Br.cst_pow, map_mul, map_pow, map_pow]`. Conclude with `(hXu.pow i).mul (hPu.pow j)`. Set `good : Fin I → Prop` to `fun i => dvO W T 2 b (c₀ i) ≠ 0`. Establish `hbad : ∀ i, ¬ good i → c₀ i = 0` using `fun i hi => hli _ (not_not.1 hi)`.

Establish `hα0 : ∀ i, good i → -(m₀ : ℤ) ≤ α i 0`. Introduce `i hi`. Assume the negation of the conclusion as `hc`. Conclude with `hi (hTop0 _ (-(α i 0)) (by omega) ((hmon i).2 0 (by norm_num)))`. Establish `hα1 : ∀ i, good i → -(m₁ : ℤ) ≤ α i 1`.

Introduce `i hi`. Assume the negation of the conclusion as `hc`. Conclude with `hi (hTop1 _ (-(α i 1)) (by omega) ((hmon i).2 1 (by norm_num)))`. Establish `hI : ∀ i, InFr W a (Br.cst (X ^ (α i 0).toNat * Br.P.p 1 ^ (α i 1).toNat)) (Br.cst (X ^ (-(α i 0)).toNat * Br.P.p 1 ^ (-(α i 1)).toNat)) (g i)`. Introduce `i`.

Establish `h` using `(hmon i).1`. Unfold `InId at h`. Rewrite `h` using `[prod_two_levels_eq_const Br, prod_two_levels_eq_const Br]`. Then use the resulting hypothesis. Use `choose U hU using fun i => inFr_ea Br a (hI i)`. Set `Gi : Fin I → PowerSeries O` to `fun i => if good i then X ^ (m₀ + α i 0).toNat * (Br.P.p 1 ^ (m₁ + α i 1).toNat * U i) else 0`.

Establish `hG : ∀ i k, algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * (g i * algebraMap O W.EE (c₀ i k)) = ea Br a (C (c₀ i k) * Gi i)`. Introduce `i k`. Distinguish the cases in `hi : good i`. Rewrite using `[ea_C_mul, ← mul_assoc, mul_comm (algebraMap O W.EE (c₀ i k))]`. Use `congr 1`.

Use `(hcu (-(α i 0)).toNat (-(α i 1)).toNat).mul_left_cancel ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE _) (algebraMap (LetA O n) W.EE _), mul_assoc, hU i, cst_mul_ea, cst_mul_ea]`. Use `congr 1`. Simplify using `only [Gi, if_pos hi]`. Establish `e0` using `toNat_split m₀ (α i 0) (hα0 i hi)`.

Establish `e1` using `toNat_split m₁ (α i 1) (hα1 i hi)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hbad i hi]`. Simplify using `[Gi, if_neg hi, ea_zero]`. Set `V : Fin d → PowerSeries O` to `fun k => ∑ i, C (c₀ i k) * Gi i`.

Establish `hV : ∀ k, lE W κ * (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) = ea Br a (V k)`. Introduce `k`. Establish `hs` using `hsum k`. Simplify using `only at hs`. Simplify using `only [V]`.

Rewrite using `[mul_left_comm, hs, Finset.mul_sum, ea_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hG i k`. Establish `hΛ : ∀ k, ∃ U' : PowerSeries O, algebraMap (LetA O n) W.EE (Br.cst (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁))) * (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) = ea Br a U'`. Introduce `k`. Take `⟨u, hu, hfu⟩` from `hfr k`.

Take `⟨U', hU'⟩` from `letE_mul_AΔ Br a hu`. Use `⟨U', ?_⟩` and prove the remaining obligations. Establish `eX : X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) = X ^ h₀ * Br.P.p 1 ^ h₁`. Rewrite using `[show X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) = X ^ (h₀ - m₀ + m₀) * Br.P.p 1 ^ (h₁ - m₁ + m₁) by ring, Nat.sub_add_cancel hm₀, Nat.sub_add_cancel hm₁]`. Rewrite using `[← mul_assoc, ← map_mul, ← Br.cst_mul, eX, hfu, mul_one, hU']`.

Both sides reduce to the same expression. Use `choose U' hU' using hΛ`. Establish `hZV : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k = C (((PD.p : ℕ) : O) ^ κ) * U' k`. Introduce `k`. Apply `ea_inj Br a` to reduce the goal to its premises.

Rewrite using `[← cst_mul_ea, ← hV k, ea_C_mul, ← hU' k]`. Simplify using `only [lE, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hl0 : ((PD.p : ℕ) : O) ≠ 0` using `Br.P.hl0`.

Take `⟨w₀, hw₀⟩` from `l_eq_unit_mul_pow hϖ hl0`. Establish `hCl : C (((PD.p : ℕ) : O) ^ κ) = C ((w₀ : O) ^ κ) * C ϖ ^ (eO (O` using `O) PD.p * κ) := by`. Rewrite using `[hw₀, mul_pow, ← pow_mul, map_mul, map_pow, map_pow]`. Establish `hZnd : ¬ C ϖ ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁))` using `ContD.not_dvd_of_isDist hϖ (isDist_XP Br _ _)`. Establish `hdvd : ∀ k, C (((PD.p : ℕ) : O) ^ κ) ∣ V k`.

Introduce `k`. Establish `h1 : C ϖ ^ (eO (O` using `O) PD.p * κ) ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k := by`. Rewrite using `[hZV k, hCl]; exact ⟨C ((w₀ : O) ^ κ) * U' k, by ring⟩`. Establish `h2` using `ContD.pow_dvd_of_dvd_mul hϖ hZnd _ _ h1`. Rewrite using `[hCl]`.

Conclude with `(IsUnit.mul_left_dvd ((w₀.isUnit.pow κ).map C)).2 h2`. Use `choose Gs hGs using hdvd`. Establish `hCne : C (((PD.p : ℕ) : O) ^ κ) ≠ (0 : PowerSeries O)`. Introduce `h`. Establish `h2 : ((PD.p : ℕ) : O) ^ κ = 0` using `by simpa using congrArg (coeff 0) h`.

Conclude with `pow_ne_zero κ hl0 h2`. Establish `hZG : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * Gs k = U' k`. Introduce `k`. Apply `mul_left_cancel₀ hCne` to reduce the goal to its premises. Rewrite using `[← hZV k, hGs k]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨Gs, fun k => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Apply `(hcu (h₀ - m₀) (h₁ - m₁)).mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hU' k, cst_mul_ea, hZG k]`. Establish `hco : (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) = fun k => ∑ i, coeff j (Gi i) * c₀ i k`.

Use function extensionality and compare the values at `k`. Establish `h3` using `congrArg (coeff j) (hGs k)`. Rewrite `h3` using `[coeff_C_mul]`. Rewrite using `[← h3]`. Simplify using `only [V, map_sum, coeff_C_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hmem : dvO W T 2 b (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) ∈ FilS W T a 0 bs`. Rewrite using `[hco, dvO_lin]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : coeff j (Gi i) = 0`.

Rewrite using `[h0, map_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hi : good i` using `fun hz => h0 (by simp only [Gi]; rw [if_neg (fun h => h hz)]; exact map_zero _)`. Establish `hle : (m₀ + α i 0).toNat ≤ j`.

Assume the negation of the conclusion as `hlt`. Apply `h0` to reduce the goal to its premises. Simplify using `only [Gi, if_pos hi]`. Rewrite using `[coeff_X_pow_mul', if_neg hlt]`. Establish `hα : (η : ℤ) + 1 ≤ -(α i 0)`.

Establish `h4` using `hα0 i hi`. Establish `h5` using `Int.toNat_of_nonneg (show 0 ≤ (m₀ : ℤ) + α i 0 by omega)`. Establish `h6 : (((m₀ + α i 0).toNat : ℕ) : ℤ) ≤ j` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers. Conclude with `hGap _ _ hα ((hmon i).2 0 (by norm_num))`.

Rewrite `hmem` using `[dvO_smulO]`. Use `(Submodule.smul_mem_iff _ ?_).1 hmem` and prove the remaining obligations. Rewrite using `[map_pow, map_natCast]`. Use `pow_ne_zero _ fun h => hl0 (hinj ?_)` and prove the remaining obligations. Rewrite using `[map_natCast, h, map_zero]`.
-/
theorem coef_fil (hinj : Function.Injective (algebraMap O LL)) {T : LocLat G Qp LL O} {d : ℕ}
    (b : Fin d → W.DD T) (a : ZMod n)
    (h₀ h₁ m₀ m₁ η : ℕ) (hm₀ : m₀ ≤ h₀) (hm₁ : m₁ ≤ h₁) (bs : ℤ)
    (hq : IsUnit (algebraMap (LetA O n) W.EE (qA W))) (hp : IsUnit (algebraMap (LetA O n) W.EE (ps W 1)))
    (hli : ∀ c₀ : Fin d → O, dvO W T 2 b c₀ = 0 → c₀ = 0)
    (hTop0 : ∀ (c₀ : Fin d → O) (u : ℤ), (m₀ : ℤ) < u → dvO W T 2 b c₀ ∈ FilS W T a 0 u → dvO W T 2 b c₀ = 0)
    (hTop1 : ∀ (c₀ : Fin d → O) (u : ℤ), (m₁ : ℤ) < u → dvO W T 2 b c₀ ∈ FilS W T a 1 u → dvO W T 2 b c₀ = 0)
    (hGap : ∀ (c₀ : Fin d → O) (u : ℤ), (η : ℤ) + 1 ≤ u → dvO W T 2 b c₀ ∈ FilS W T a 0 u →
      dvO W T 2 b c₀ ∈ FilS W T a 0 bs)
    (f : Fin d → W.EE) (hf : InNL W T a 2 (Br.cst (X ^ h₀ * Br.P.p 1 ^ h₁)) b f) :
    ∃ Gs : Fin d → PowerSeries O,
      (∀ k, algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k = ea Br a (Gs k)) ∧
      ∀ j < m₀ - η, dvO W T 2 b (fun k => coeff j (Gs k)) ∈ FilS W T a 0 bs := by
  classical
  have := Fact.mk PD.hp
  obtain ⟨hfr, κ, I, g, c₀, α, hmon, hsum⟩ := hf
  have hXu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst X)) := Br.qA_eq ▸ hq
  have hPu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst (Br.P.p 1))) := (ps_cst Br 1) ▸ hp
  have hcu : ∀ i j : ℕ, IsUnit (algebraMap (LetA O n) W.EE (Br.cst (X ^ i * Br.P.p 1 ^ j))) := by
    intro i j; rw [Br.cst_mul, Br.cst_pow, Br.cst_pow, map_mul, map_pow, map_pow]
    exact (hXu.pow i).mul (hPu.pow j)
  let good : Fin I → Prop := fun i => dvO W T 2 b (c₀ i) ≠ 0
  have hbad : ∀ i, ¬ good i → c₀ i = 0 := fun i hi => hli _ (not_not.1 hi)
  have hα0 : ∀ i, good i → -(m₀ : ℤ) ≤ α i 0 := by
    intro i hi
    by_contra hc
    exact hi (hTop0 _ (-(α i 0)) (by omega) ((hmon i).2 0 (by norm_num)))
  have hα1 : ∀ i, good i → -(m₁ : ℤ) ≤ α i 1 := by
    intro i hi
    by_contra hc
    exact hi (hTop1 _ (-(α i 1)) (by omega) ((hmon i).2 1 (by norm_num)))
  have hI : ∀ i, InFr W a (Br.cst (X ^ (α i 0).toNat * Br.P.p 1 ^ (α i 1).toNat))
      (Br.cst (X ^ (-(α i 0)).toNat * Br.P.p 1 ^ (-(α i 1)).toNat)) (g i) := by
    intro i
    have h := (hmon i).1
    unfold InId at h
    rwa [prod_two_levels_eq_const Br, prod_two_levels_eq_const Br] at h
  choose U hU using fun i => inFr_ea Br a (hI i)
  let Gi : Fin I → PowerSeries O := fun i =>
    if good i then X ^ (m₀ + α i 0).toNat * (Br.P.p 1 ^ (m₁ + α i 1).toNat * U i) else 0
  have hG : ∀ i k, algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) *
      (g i * algebraMap O W.EE (c₀ i k)) = ea Br a (C (c₀ i k) * Gi i) := by
    intro i k
    by_cases hi : good i
    · rw [ea_C_mul, ← mul_assoc, mul_comm (algebraMap O W.EE (c₀ i k))]
      congr 1
      refine (hcu (-(α i 0)).toNat (-(α i 1)).toNat).mul_left_cancel ?_
      rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE _) (algebraMap (LetA O n) W.EE _), mul_assoc,
        hU i, cst_mul_ea, cst_mul_ea]
      congr 1
      simp only [Gi, if_pos hi]
      have e0 := toNat_split m₀ (α i 0) (hα0 i hi)
      have e1 := toNat_split m₁ (α i 1) (hα1 i hi)
      calc X ^ m₀ * Br.P.p 1 ^ m₁ * (X ^ (α i 0).toNat * Br.P.p 1 ^ (α i 1).toNat * U i)
          = X ^ (m₀ + (α i 0).toNat) * Br.P.p 1 ^ (m₁ + (α i 1).toNat) * U i := by ring
        _ = X ^ ((-(α i 0)).toNat + (m₀ + α i 0).toNat) *
              Br.P.p 1 ^ ((-(α i 1)).toNat + (m₁ + α i 1).toNat) * U i := by rw [e0, e1]
        _ = _ := by ring
    · rw [hbad i hi]
      simp [Gi, if_neg hi, ea_zero]
  let V : Fin d → PowerSeries O := fun k => ∑ i, C (c₀ i k) * Gi i
  have hV : ∀ k, lE W κ * (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) =
      ea Br a (V k) := by
    intro k
    have hs := hsum k
    simp only at hs
    simp only [V]
    rw [mul_left_comm, hs, Finset.mul_sum, ea_sum]
    exact Finset.sum_congr rfl fun i _ => hG i k
  have hΛ : ∀ k, ∃ U' : PowerSeries O,
      algebraMap (LetA O n) W.EE (Br.cst (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁))) *
        (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) = ea Br a U' := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hfr k
    obtain ⟨U', hU'⟩ := letE_mul_AΔ Br a hu
    refine ⟨U', ?_⟩
    have eX : X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) = X ^ h₀ * Br.P.p 1 ^ h₁ := by
      rw [show X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) =
        X ^ (h₀ - m₀ + m₀) * Br.P.p 1 ^ (h₁ - m₁ + m₁) by ring, Nat.sub_add_cancel hm₀, Nat.sub_add_cancel hm₁]
    rw [← mul_assoc, ← map_mul, ← Br.cst_mul, eX, hfu, mul_one, hU']
    rfl
  choose U' hU' using hΛ
  have hZV : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k = C (((PD.p : ℕ) : O) ^ κ) * U' k := by
    intro k
    apply ea_inj Br a
    rw [← cst_mul_ea, ← hV k, ea_C_mul, ← hU' k]
    simp only [lE, map_pow, map_natCast]
    ring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := Br.P.hl0
  obtain ⟨w₀, hw₀⟩ := l_eq_unit_mul_pow hϖ hl0
  have hCl : C (((PD.p : ℕ) : O) ^ κ) = C ((w₀ : O) ^ κ) * C ϖ ^ (eO (O := O) PD.p * κ) := by
    rw [hw₀, mul_pow, ← pow_mul, map_mul, map_pow, map_pow]
  have hZnd : ¬ C ϖ ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) :=
    ContD.not_dvd_of_isDist hϖ (isDist_XP Br _ _)
  have hdvd : ∀ k, C (((PD.p : ℕ) : O) ^ κ) ∣ V k := by
    intro k
    have h1 : C ϖ ^ (eO (O := O) PD.p * κ) ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k := by
      rw [hZV k, hCl]; exact ⟨C ((w₀ : O) ^ κ) * U' k, by ring⟩
    have h2 := ContD.pow_dvd_of_dvd_mul hϖ hZnd _ _ h1
    rw [hCl]
    exact (IsUnit.mul_left_dvd ((w₀.isUnit.pow κ).map C)).2 h2
  choose Gs hGs using hdvd
  have hCne : C (((PD.p : ℕ) : O) ^ κ) ≠ (0 : PowerSeries O) := by
    intro h
    have h2 : ((PD.p : ℕ) : O) ^ κ = 0 := by simpa using congrArg (coeff 0) h
    exact pow_ne_zero κ hl0 h2
  have hZG : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * Gs k = U' k := by
    intro k
    apply mul_left_cancel₀ hCne
    rw [← hZV k, hGs k]; ring
  refine ⟨Gs, fun k => ?_, fun j hj => ?_⟩
  · apply (hcu (h₀ - m₀) (h₁ - m₁)).mul_left_cancel
    rw [hU' k, cst_mul_ea, hZG k]
  · have hco : (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) = fun k => ∑ i, coeff j (Gi i) * c₀ i k := by
      funext k
      have h3 := congrArg (coeff j) (hGs k)
      rw [coeff_C_mul] at h3
      rw [← h3]
      simp only [V, map_sum, coeff_C_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hmem : dvO W T 2 b (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) ∈ FilS W T a 0 bs := by
      rw [hco, dvO_lin]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases h0 : coeff j (Gi i) = 0
      · rw [h0, map_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hi : good i := fun hz => h0 (by simp only [Gi]; rw [if_neg (fun h => h hz)]; exact map_zero _)
        have hle : (m₀ + α i 0).toNat ≤ j := by
          by_contra hlt
          apply h0
          simp only [Gi, if_pos hi]
          rw [coeff_X_pow_mul', if_neg hlt]
        have hα : (η : ℤ) + 1 ≤ -(α i 0) := by
          have h4 := hα0 i hi
          have h5 := Int.toNat_of_nonneg (show 0 ≤ (m₀ : ℤ) + α i 0 by omega)
          have h6 : (((m₀ + α i 0).toNat : ℕ) : ℤ) ≤ j := by exact_mod_cast hle
          omega
        exact hGap _ _ hα ((hmon i).2 0 (by norm_num))
    rw [dvO_smulO] at hmem
    refine (Submodule.smul_mem_iff _ ?_).1 hmem
    rw [map_pow, map_natCast]
    refine pow_ne_zero _ fun h => hl0 (hinj ?_)
    rw [map_natCast, h, map_zero]

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
