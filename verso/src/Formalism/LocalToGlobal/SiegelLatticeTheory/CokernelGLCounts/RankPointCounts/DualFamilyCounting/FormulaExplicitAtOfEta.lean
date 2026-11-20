import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalFormIntegralOnLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AbsNormSmallFinite
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensJordanL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TotallyPositiveAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanDecompositionExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.AtD

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EtaLocAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : PlF D, (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

def DensProdValAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (c : ℕ), c ≤ 2 * (D.R.rS + 1) →
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp])
                (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then -1 else 1) D.R.r (2 * (D.R.rS + 1)) c =
        alphaStd D.host.E p.asIdeal D.R.r / alphaStd D.host.E p.asIdeal (D.R.k - 1 - c)

def DensAllAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
          (∀ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = alphaStd D.host.E p.asIdeal D.R.r /
            alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal)) ∧
          Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)) ∧
        (¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0)

def FormulaExplicitAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ Z : MatZ D,
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
          nu (Tn u') F0 what₂ Z = cExpl D F0 what₂ * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) *
            ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p

/- English proof (translation)
Introduce `δ M _ p c hc`. Take `⟨hK, hF, -⟩` from `field_dictionary_holds D`. Establish `hm` using `Formalism.L2.SG.Pf.NcArithG.rm_eq D`. Establish `hk5 : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Establish `hq` using `PI.UnitaryGroupMassFormula.CntFormula.residue_field_card D p`. Establish `hmax : p.asIdeal.IsMaximal` using `p.isMaximal`. Establish `hpos` using `alphaStd_pos hK hF hmax (D.R.k - 1 - c)`. Rewrite using `[eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]`. Use `congr 1`.

Unfold `Formalism.L2.SG.DensExact.densProd`. Rewrite using `[hq, hη p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast]`.
-/
theorem densProdValAt_of (D : Formalism.BasicNotions.D7) (hη : EtaLocAt D) : DensProdValAt D := by
  intro δ M _ p c hc
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq := PI.UnitaryGroupMassFormula.CntFormula.residue_field_card D p
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  have hpos := alphaStd_pos hK hF hmax (D.R.k - 1 - c)
  rw [eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]
  congr 1
  unfold Formalism.L2.SG.DensExact.densProd
  rw [hq, hη p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_neg, zpow_natCast]

/- English proof (translation)
Introduce `δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p`. Establish `h1` using `local_self_dual_holds`. Establish `h2` using `DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds`. Take `⟨A, a, hAO, hAdet, hG, hc⟩` from `h2 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p`. Establish `hSD` using `h1 D δ M hA L p`.

Take `⟨-, -, hUr, -⟩` from `perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP`. Establish `hm` using `Formalism.L2.SG.Pf.NcArithG.rm_eq D`. Establish `hk5 : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p)`.

Rewrite using `[L.rank p, Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1)`. Use `Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal` as an intermediate fact. Rewrite `this` using `[hUr, hm]`.

Conclude with `this`. Unfold `densP`. Rewrite using `[hG, local_density_corank (D.s.atP p).Fp (D.s.atP p).Ep (M p) (D.s.atP p).lf (D.s.atP p).char0 (L.V p) (L.H p) (lattice₂ L p (VS D).L0) hSD (ϖ p) (hϖ p) _ A a hAO hAdet hcard, L.rank p, Fintype.card_sum, Fintype.card_fin, hc, show D.R.rS + 1 + (D.R.rS + 1) = 2 * (D.R.rS + 1) by r …`. Conclude with `h5 δ M hA p _ hcle`.
-/
theorem densValAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          densP L δ ϖ (Tn u) (Tn u') Z p =
            alphaStd D.host.E p.asIdeal D.R.r /
              alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  have h1 := local_self_dual_holds
  have h2 := DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds
  obtain ⟨A, a, hAO, hAdet, hG, hc⟩ := h2 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  have hSD := h1 D δ M hA L p
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [L.rank p, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
    have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
    rw [hUr, hm] at this
    exact this
  unfold densP
  rw [hG, local_density_corank (D.s.atP p).Fp (D.s.atP p).Ep (M p) (D.s.atP p).lf (D.s.atP p).char0 (L.V p)
    (L.H p) (lattice₂ L p (VS D).L0) hSD (ϖ p) (hϖ p) _ A a hAO hAdet hcard, L.rank p, Fintype.card_sum,
    Fintype.card_fin, hc, show D.R.rS + 1 + (D.R.rS + 1) = 2 * (D.R.rS + 1) by ring]
  exact h5 δ M hA p _ hcle

/- English proof (translation)
Introduce `δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI`. Establish `hval` using `densValAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI`. Take `⟨-, -, hUr, -⟩` from `perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP`. Establish `hm` using `Formalism.L2.SG.Pf.NcArithG.rm_eq D`. Establish `hk5 : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`.

Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hs : Summable (fun p : PlF D => densP L δ ϖ (Tn u) (Tn u') Z p - 1)`. Use `Summable.of_norm_bounded_eventually ((PI.UnitaryGroupMassFormula.CntFormula.prime_zeta_two D.host.F).mul_left 6) ?_` and prove the remaining obligations. Use `filter_upwards [(absNorm_small_finite D).compl_mem_cofinite] with p hp`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp`.

Establish `hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1)`. Use `Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal` as an intermediate fact. Rewrite `this` using `[hUr, hm]`. Conclude with `this`. Take `⟨-, hup, hlow⟩` from `Formalism.L2.SG.Pf.DensLoc.ratio_bounds (K := D.host.E) p.asIdeal (by linarith) (j := D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) (n := D.R.r) (s := 2) (by omega) (by omega) (by norm_num)`.

Establish `hlow'` using `hlow hp`. Rewrite using `[hval p, Real.norm_eq_abs]`. Use `set x : ℝ := ((Ideal.absNorm p.asIdeal : ℝ))⁻¹ with hx`. Establish `hx0 : 0 ≤ x` using `inv_nonneg.2 (by linarith)`. Establish `hx3 : x ≤ 1 / 3` using `by rw [hx, one_div]; exact inv_anti₀ (by norm_num) hp`.

Establish `hx2 : x ^ 2 ≤ 1 / 9` using `by nlinarith`. Establish `hx2n : 0 ≤ x ^ 2` using `sq_nonneg x`. Establish `h2n : (0 : ℝ) ≤ 2 * x ^ 2` using `by positivity`. Establish `h3n : (0 : ℝ) ≤ 3 * x ^ 2` using `by positivity`. Establish `e1` using `Real.abs_exp_sub_one_le (x := 2 * x ^ 2) (by rw [abs_of_nonneg h2n]; linarith)`.

Establish `e2` using `Real.abs_exp_sub_one_le (x := -(3 * x ^ 2)) (by rw [abs_neg, abs_of_nonneg h3n]; linarith)`. Rewrite `e1` using `[abs_of_nonneg h2n]`. Rewrite `e2` using `[abs_neg, abs_of_nonneg h3n]`. Establish `hq : 6 * (1 / ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)) = 6 * x ^ 2` using `by rw [hx, inv_pow, one_div]`. Rewrite using `[hq, abs_le]`.

Prove the components needed by the constructor for the conclusion. Use `(abs_le.mp e2).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(abs_le.mp e1).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Real.multipliable_one_add_of_summable hs` as an intermediate fact. Simplify using `using this`.
-/
theorem densMultIntAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z) := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  have hval := densValAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : Summable (fun p : PlF D => densP L δ ϖ (Tn u) (Tn u') Z p - 1) := by
    refine Summable.of_norm_bounded_eventually ((PI.UnitaryGroupMassFormula.CntFormula.prime_zeta_two D.host.F).mul_left 6) ?_
    filter_upwards [(absNorm_small_finite D).compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
    have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
      have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
      rw [hUr, hm] at this
      exact this
    obtain ⟨-, hup, hlow⟩ := Formalism.L2.SG.Pf.DensLoc.ratio_bounds (K := D.host.E) p.asIdeal (by linarith)
      (j := D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) (n := D.R.r) (s := 2)
      (by omega) (by omega) (by norm_num)
    have hlow' := hlow hp
    rw [hval p, Real.norm_eq_abs]
    set x : ℝ := ((Ideal.absNorm p.asIdeal : ℝ))⁻¹ with hx
    have hx0 : 0 ≤ x := inv_nonneg.2 (by linarith)
    have hx3 : x ≤ 1 / 3 := by rw [hx, one_div]; exact inv_anti₀ (by norm_num) hp
    have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
    have hx2n : 0 ≤ x ^ 2 := sq_nonneg x
    have h2n : (0 : ℝ) ≤ 2 * x ^ 2 := by positivity
    have h3n : (0 : ℝ) ≤ 3 * x ^ 2 := by positivity
    have e1 := Real.abs_exp_sub_one_le (x := 2 * x ^ 2) (by rw [abs_of_nonneg h2n]; linarith)
    have e2 := Real.abs_exp_sub_one_le (x := -(3 * x ^ 2)) (by rw [abs_neg, abs_of_nonneg h3n]; linarith)
    rw [abs_of_nonneg h2n] at e1
    rw [abs_neg, abs_of_nonneg h3n] at e2
    have hq : 6 * (1 / ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)) = 6 * x ^ 2 := by rw [hx, inv_pow, one_div]
    rw [hq, abs_le]
    constructor
    · have := (abs_le.mp e2).1
      linarith
    · have := (abs_le.mp e1).2
      linarith
  have := Real.multipliable_one_add_of_summable hs
  simpa using this

/- English proof (translation)
Introduce `δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP`. Establish `h5` using `densProdValAt_of D hη`. Conclude with `⟨fun hI => ⟨fun p => densValAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p, densMultIntAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩, DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE D δ M hA L …`.
-/
theorem densAllAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocAt D) : DensAllAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  have h5 := densProdValAt_of D hη
  exact ⟨fun hI => ⟨fun p => densValAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p,
      densMultIntAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩,
    DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE
      D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP⟩

end Formalism.L2.SG.Pf.Cnt.AtD

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.Pf.Cnt.AtD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
Introduce `δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hP`. Establish `h0` using `Formalism.L2.SG.Pf.Cnt.field_dictionary_holds`. Establish `h1` using `Formalism.L2.SG.Pf.Cnt.rational_pair_holds`. Establish `h2` using `Formalism.L2.SG.Pf.Cnt.perpendicular_definition_holds`. Establish `h3` using `Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds`.

Establish `h4` using `Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds`. Establish `h6` using `PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan`. Establish `g7` using `Formalism.L2.SG.Pf.Cnt.glueExists_holds`. Establish `g9` using `Formalism.L2.SG.Pf.Cnt.gluing_mass_holds`. Take `⟨hK, hF, hN⟩` from `h0 D`.

Take `⟨F', hz, hZ⟩` from `h1 D u u' hT F0 what₂ hR Z hP`. Take `⟨hC, hPD, hUr, hWr⟩` from `h2 D u u' hT F0 what₂ hR Z F' hz hZ hP`. Take `⟨hLat, -⟩` from `h3 D u u' hT F0 what₂ hR Z F' hz hZ hP`. Establish `e4` using `h4 D u u' hT F0 what₂ hR Z F' hz hZ hP`. Take `⟨h5i, h5n⟩` from `h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP`.

Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hnu0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0 → Formalism.L2.SG.CntLocal.nu (Tn u') F0 what₂ Z = 0`. Introduce `h0`. Unfold `Formalism.L2.SG.CntLocal.nu`. Rewrite using `[show (∑ Λ ∈ what₂, wRow D F0 Λ) = Formalism.MainNotions.S.Cnt.massRows D F0 what₂ from rfl, h0, div_zero]`.

Distinguish the cases in `hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')`. Establish `hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal → cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 F'))`. Introduce `𝔭 _`. Use `cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭` as an intermediate fact. Rewrite using `[hWr]`.

Use linear arithmetic over natural numbers and integers. Establish `hne` using `g7 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 F') hLat hI hcJ`. Establish `hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 F'))) (cMass D.host.E D.host.F (D.R.k - 1))`. Rewrite using `[hWr]`. Conclude with `(cMass_spec hK hF (D.R.k - 1) (by omega)).2`.

Take `⟨s, hs1, hs2, hs3, hsum⟩` from `g9 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD (MMof D F0 F') hLat hI hne _ hMC`. Establish `e4'` using `e4 s ⟨hs1, hs2, hs3⟩`. Rewrite `e4'` using `[hsum, hWr]`. Take `⟨hd, hmult⟩` from `h5i hI`. Establish `h6'` using `h6 D u u' hT F0 what₂ hR Z F' hz hZ hP hI`.

Establish `hg : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} => alphaStd D.host.E 𝔭.1 D.R.r / alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) (∏' p, densP L δ ϖ (Tn u) (Tn u') Z p)`. Use `(plEquiv (F := D.host.F)).hasProd_iff.mp ?_` and prove the remaining obligations. Establish `hh` using `hmult.hasProd`. Use `hh using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Conclude with `(hd p).symm`. Establish `hl : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} => ∏ i ∈ Finset.Icc D.R.k D.R.r, (1 - etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i)` using `hasProd_prod fun i hi => hasProd_lF hK hF i (by simp only [Finset.mem_Icc] at hi; omega)`. Establish `hrk : D.R.k - 1 ≤ D.R.r` using `by show D.R.k - 1 ≤ D.R.k + D.R.m - 1`. Use linear arithmetic over natural numbers and integers. Establish `hT1 : (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal}, alphaStd D.host.E 𝔭.1 (D.R.k - 1) / alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) = (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) * ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p`.

Use `HasProd.tprod_eq ?_` and prove the remaining obligations. Use `hl.mul hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `𝔭`. Rewrite using `[alpha_split hK hF 𝔭.2 (by omega) hrk]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e4'` using `[hT1, h6']`. Distinguish the cases in `hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0`. Rewrite using `[hnu0 hm0]`. Unfold `cExpl`. Rewrite using `[hm0, div_zero, zero_mul, zero_mul]`.

Establish `e1 : (|(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))) ^ (D.R.k - 1) = |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ))`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e4'` using `[mul_pow, e1]`. Unfold `cExpl`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e4'`. Establish `hE` using `glueSet_eq_empty (U := UPair D F0 F') hI`.

Establish `e4'` using `e4 ∅ (isGlueReps_empty hE)`. Rewrite `e4'` using `[Finset.sum_empty]`. Take `⟨p, hp⟩` from `h5n hI`. Establish `hz0 : ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p = 0` using `(hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).tprod_eq`. Rewrite using `[hz0, mul_zero]`.

Distinguish the cases in `hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0`. Conclude with `hnu0 hm0`. Conclude with `(mul_eq_zero.mp e4').resolve_right hm0`.
-/
theorem formulaExplicitAt_of (D : Formalism.BasicNotions.D7) (h5 : DensAllAt D) : FormulaExplicitAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hP
  have h0 := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds
  have h1 := Formalism.L2.SG.Pf.Cnt.rational_pair_holds
  have h2 := Formalism.L2.SG.Pf.Cnt.perpendicular_definition_holds
  have h3 := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds
  have h4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds
  have h6 := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan
  have g7 := Formalism.L2.SG.Pf.Cnt.glueExists_holds
  have g9 := Formalism.L2.SG.Pf.Cnt.gluing_mass_holds
  obtain ⟨hK, hF, hN⟩ := h0 D
  obtain ⟨F', hz, hZ⟩ := h1 D u u' hT F0 what₂ hR Z hP
  obtain ⟨hC, hPD, hUr, hWr⟩ := h2 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨hLat, -⟩ := h3 D u u' hT F0 what₂ hR Z F' hz hZ hP
  have e4 := h4 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨h5i, h5n⟩ := h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hnu0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0 → Formalism.L2.SG.CntLocal.nu (Tn u') F0 what₂ Z = 0 := by
    intro h0
    unfold Formalism.L2.SG.CntLocal.nu
    rw [show (∑ Λ ∈ what₂, wRow D F0 Λ) = Formalism.MainNotions.S.Cnt.massRows D F0 what₂ from rfl, h0, div_zero]
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')
  ·
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭 <
          finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭
      rw [hWr]
      omega
    have hne := g7 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 F') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 F')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, hsum⟩ := g9 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 F') hC hPD (MMof D F0 F') hLat hI hne _ hMC
    have e4' := e4 s ⟨hs1, hs2, hs3⟩
    rw [hsum, hWr] at e4'
    obtain ⟨hd, hmult⟩ := h5i hI
    have h6' := h6 D u u' hT F0 what₂ hR Z F' hz hZ hP hI

    have hg : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        alphaStd D.host.E 𝔭.1 D.R.r /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1))
        (∏' p, densP L δ ϖ (Tn u) (Tn u') Z p) := by
      refine (plEquiv (F := D.host.F)).hasProd_iff.mp ?_
      have hh := hmult.hasProd
      convert hh using 1
      funext p
      exact (hd p).symm
    have hl : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        ∏ i ∈ Finset.Icc D.R.k D.R.r,
          (1 - etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹)
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) :=
      hasProd_prod fun i hi => hasProd_lF hK hF i (by simp only [Finset.mem_Icc] at hi; omega)
    have hrk : D.R.k - 1 ≤ D.R.r := by
      show D.R.k - 1 ≤ D.R.k + D.R.m - 1
      omega
    have hT1 : (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
        alphaStd D.host.E 𝔭.1 (D.R.k - 1) /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) =
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) *
          ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p := by
      refine HasProd.tprod_eq ?_
      convert hl.mul hg using 1
      funext 𝔭
      rw [alpha_split hK hF 𝔭.2 (by omega) hrk]
      ring
    rw [hT1, h6'] at e4'
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · rw [hnu0 hm0]
      unfold cExpl
      rw [hm0, div_zero, zero_mul, zero_mul]
    · have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))) ^ (D.R.k - 1) =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [mul_pow, e1] at e4'
      unfold cExpl
      field_simp
      linear_combination e4'
  ·
    have hE := glueSet_eq_empty (U := UPair D F0 F') hI
    have e4' := e4 ∅ (isGlueReps_empty hE)
    rw [Finset.sum_empty] at e4'
    obtain ⟨p, hp⟩ := h5n hI
    have hz0 : ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p = 0 :=
      (hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).tprod_eq
    rw [hz0, mul_zero]
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · exact hnu0 hm0
    · exact (mul_eq_zero.mp e4').resolve_right hm0

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
The claim follows from `formulaExplicitAt_of D (densAllAt_of D hF hη)`.
-/
theorem formulaExplicitAt_of_eta (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocAt D) : FormulaExplicitAt D :=
  formulaExplicitAt_of D (densAllAt_of D hF hη)

end Formalism.L2.SG.Pf
