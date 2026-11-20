import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UlocOfTrivDisc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ULocDualHformOne
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitLocLastRow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]`.
-/
theorem sigR_tmul (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (y : v.adicCompletion F) :
    Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] y) = σ e ⊗ₜ[F] y := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Use `show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) = σ e ⊗ₜ[F] 1`. Conclude with `sigR_tmul σ v e 1`.
-/
theorem sigR_inclE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ e) := by
  show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) = σ e ⊗ₜ[F] 1
  exact sigR_tmul σ v e 1

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e y => rw [sigR_tmul, sigR_tmul, hσ]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (a : E ⊗[F] v.adicCompletion F) : Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.sigR σ (v.adicCompletion F) a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul e y => rw [sigR_tmul, sigR_tmul, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Establish `h : Formalism.BasicNotions.intV E v ≤ (Formalism.BasicNotions.intV E v).comap (Formalism.UG.sigR σ (v.adicCompletion F))` using `by show Subring.closure _ ≤ _`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Use `show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) ∈ Formalism.BasicNotions.intV E v`. Rewrite using `[sigR_tmul]`.

Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Conclude with `⟨⟨σ e, GlobalTheory.uLocDual_intOE_map (σ : E →+* E) he⟩, rfl⟩`. Use `show Formalism.UG.sigR σ (v.adicCompletion F) (1 ⊗ₜ[F] y) ∈ Formalism.BasicNotions.intV E v`. Rewrite using `[sigR_tmul, map_one]`.

Apply `Subring.subset_closure` to reduce the goal to its premises. Use `right`. Conclude with `⟨⟨y, hy⟩, rfl⟩`. Conclude with `h ha`.
-/
theorem sigR_mem_intV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.BasicNotions.intV E v) : Formalism.UG.sigR σ (v.adicCompletion F) a ∈ Formalism.BasicNotions.intV E v := by
  have h : Formalism.BasicNotions.intV E v ≤ (Formalism.BasicNotions.intV E v).comap (Formalism.UG.sigR σ (v.adicCompletion F)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ e, GlobalTheory.uLocDual_intOE_map (σ : E →+* E) he⟩, rfl⟩
    · show Formalism.UG.sigR σ (v.adicCompletion F) (1 ⊗ₜ[F] y) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul, map_one]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, rfl⟩
  exact h ha

/- English proof (translation)
The claim follows from `Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _ ⟨r, rfl⟩`.
-/
theorem inclE_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 E) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E v :=
  Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _ ⟨r, rfl⟩

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem one_int (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (a b : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ Formalism.BasicNotions.intV E v := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Establish `key` using `Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0)`. Take `⟨h1, h2⟩` from `(key y).1 hy`. Establish `hPinv : Formalism.UG.inclE (F` using `F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by`. Rewrite using `[← map_mul, inv_mul_cancel₀ hp0, map_one]`. Establish `hyint : ∀ j, y j ∈ Formalism.BasicNotions.intV E v`.

Introduce `j`. Distinguish the cases in `hj : j = Formalism.L2.Col.lastIdx n`. Rewrite using `[hj]`. Establish `e : y (Formalism.L2.Col.lastIdx n) = Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (p : E) * (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n)) := by`. Rewrite using `[← mul_assoc, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E)), hPinv, one_mul]`.

Rewrite using `[e]`. Conclude with `mul_mem (inclE_int v p) h2`. Conclude with `h1 j hj`. Use `(key _).2 ⟨fun i _ => ?_, ?_⟩` and prove the remaining obligations. Use `show ∑ j, N i j * y j ∈ Formalism.BasicNotions.intV E v`.

Conclude with `sum_mem fun j _ => mul_mem (hN i j) (hyint j)`. Use `choose c hc hcl using hlast`. Establish `e : (N *ᵥ y) (Formalism.L2.Col.lastIdx n) = ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) (Formalism.L2.Col.lastIdx n) + Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (p : E) * ∑ j, c j * y j := by show ∑ j, N _ j * y j = ∑ j, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) _ j * y j + _`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[show N (Formalism.L2.Col.lastIdx n) j = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j + Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c j by rw [← hcl j]; ring]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Matrix.one_mulVec, mul_add, ← mul_assoc, hPinv, one_mul]`. Conclude with `add_mem h2 (sum_mem fun j _ => mul_mem (hc j) (hyint j))`.
-/
theorem mulVec_mem_dLat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} [NeZero n] (p : 𝓞 E) (hp0 : (p : E) ≠ 0)
    (N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (hN : ∀ i j, N i j ∈ Formalism.BasicNotions.intV E v)
    (hlast : ∀ j, ∃ c ∈ Formalism.BasicNotions.intV E v, N (Formalism.L2.Col.lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c)
    (y : Fin n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹))) :
    N *ᵥ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹)) := by
  have key := Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0)
  obtain ⟨h1, h2⟩ := (key y).1 hy
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hyint : ∀ j, y j ∈ Formalism.BasicNotions.intV E v := by
    intro j
    by_cases hj : j = Formalism.L2.Col.lastIdx n
    · rw [hj]
      have e : y (Formalism.L2.Col.lastIdx n) = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
          (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E)), hPinv, one_mul]
      rw [e]
      exact mul_mem (inclE_int v p) h2
    · exact h1 j hj
  refine (key _).2 ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, N i j * y j ∈ Formalism.BasicNotions.intV E v
    exact sum_mem fun j _ => mul_mem (hN i j) (hyint j)
  · choose c hc hcl using hlast
    have e : (N *ᵥ y) (Formalism.L2.Col.lastIdx n) = ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) (Formalism.L2.Col.lastIdx n) +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * ∑ j, c j * y j := by
      show ∑ j, N _ j * y j = ∑ j, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) _ j * y j + _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show N (Formalism.L2.Col.lastIdx n) j = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c j by rw [← hcl j]; ring]
      ring
    rw [e, Matrix.one_mulVec, mul_add, ← mul_assoc, hPinv, one_mul]
    exact add_mem h2 (sum_mem fun j _ => mul_mem (hc j) (hyint j))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n _ J hJ T f bad S p q hq hpq hcop hT hL v hv x hU hint hlast`. Substitute `hJ` using the available equality. Establish `hTE : (T : E) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hp0 : (p : E) ≠ 0` using `left_ne_zero_of_mul (hpq ▸ hTE)`. Establish `hq0 : (q : E) ≠ 0` using `right_ne_zero_of_mul (hpq ▸ hTE)`.

Establish `hPinv : Formalism.UG.inclE (F` using `F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by`. Rewrite using `[← map_mul, inv_mul_cancel₀ hp0, map_one]`. Establish `h0 : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) * (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F` using `F) (v.adicCompletion F)) * (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := hU`. Rewrite `h0` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Establish `hMi : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0, Matrix.one_mul]`. Use `_ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Establish `hMient : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b = Formalism.UG.sigR σ (v.adicCompletion F) ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a)`. Introduce `a b`.

Rewrite using `[hMi]`. Both sides reduce to the same expression. Establish `hMiint : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ Formalism.BasicNotions.intV E v`. Introduce `a b`. Rewrite using `[hMient]`.

Conclude with `sigR_mem_intV σ v (hint b a)`. Use `choose c hc hcl using hlast`. Establish `hmat : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1 = -(((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion …`. Rewrite using `[Matrix.sub_mul, Units.mul_inv, Matrix.one_mul]`. Normalize the expressions using the abelian group laws.

Establish `hMilast : ∀ i, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i = Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (p : E) * (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by`. Introduce `i`. Establish `h1` using `congrFun (congrFun hmat (Formalism.L2.Col.lastIdx n)) i`. Rewrite `h1` using `[Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply]`. Rewrite using `[h1, mul_neg, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, hcl k, mul_assoc]`. Establish `hMilastI : ∀ i, ∃ e ∈ Formalism.BasicNotions.intV E v, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i = …` using `F) (v.adicCompletion F) (p : E) * e := fun i => ⟨_, neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)), hMilast i⟩`. Establish `hs1 : ∀ a b, Formalism.UG.sigR σ (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a`.

Introduce `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[Matrix.one_apply_eq, map_one]`. Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab), map_zero]`.

Establish `hcol : ∀ i, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) = Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (q : E) * Formalism.UG.sigR σ (v.adicCompletion F) (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by`. Introduce `i`. Establish `h` using `congrArg (Formalism.UG.sigR σ (v.adicCompletion F)) (hMilast i)`. Rewrite `h` using `[map_sub, map_mul, hMient, sigR_sigR σ hσ v, sigR_inclE, ← hq, hs1]`. Conclude with `h`.

Establish `h1 : x ∈ Formalism.UG.levelVL σ (1 : Matrix (Fin n) (Fin n) E) v S.Lb`. Rewrite using `[hL]`. Use `Subgroup.mem_inf.2 ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩` and prove the remaining obligations. Conclude with `mulVec_mem_dLat v p hp0 _ hint (fun j => ⟨c j, hc j, hcl j⟩) y hy`. Use `mulVec_mem_dLat v p hp0 _ hMiint hMilastI _ hy` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `h2 : ∀ y ∈ Formalism.UG.latS (F` using `F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)), (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) …`. Introduce `y hy`. Rewrite `hy` using `[hL, GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq]`. Rewrite using `[hL]`.

Take `⟨hy1, hy2⟩` from `(Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v (q : E) hq0 y).1 hy`. Rewrite using `[show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *ᵥ y by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]`. Use `(Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0) _).2 ⟨fun i _ => ?_, ?_⟩` and prove the remaining obligations. Use `show ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) i j * y j ∈ Formalism.BasicNotions.intV E v`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = Formalism.L2.Col.lastIdx n`. Rewrite using `[hj, Matrix.sub_apply, hcol i, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E)), mul_assoc]`. Conclude with `mul_mem (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)))) hy2`. Conclude with `mul_mem (sub_mem (hint i j) (one_int v i j)) (hy1 j hj)`. Use `show Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) j * y j ∈ Formalism.BasicNotions.intV E v`.

Rewrite using `[Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = Formalism.L2.Col.lastIdx n`. Rewrite using `[hj]`. Take `⟨a, b, hab⟩` from `hcop`.

Establish `hE : (a : E) * (p : E) + (b : E) * (q : E) = 1`. Conclude with `congrArg (fun r : 𝓞 E => (r : E)) hab` after adjusting the coercions. Establish `hab' : Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (a : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) + Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) = 1 := by`. Establish `h` using `congrArg (Formalism.UG.inclE (F := F) (v.adicCompletion F)) hE`. Rewrite `h` using `[map_add, map_mul, map_mul, map_one]`. Then use the resulting hypothesis.

Establish `hDc` using `hcl (Formalism.L2.Col.lastIdx n)`. Establish `hDd` using `hcol (Formalism.L2.Col.lastIdx n)`. Rewrite `hDc`, `hDd` using `[← Matrix.sub_apply]`. Establish `e : Formalism.UG.inclE (F` using `F) (v.adicCompletion F) ((p : E)⁻¹) * (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) = (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.sigR σ (v.a …`. Take the linear combination `(Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n) - Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDc + (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hPinv + (Formali …`.

Rewrite using `[e]`. Conclude with `mul_mem (add_mem (mul_mem (inclE_int v a) (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k _))))) (mul_mem (inclE_int v b) (hc _))) hy2`. Rewrite using `[Matrix.sub_apply, hcl j, ← mul_assoc, ← mul_assoc, hPinv, one_mul]`. Conclude with `mul_mem (hc j) (hy1 j hj)`. Conclude with `GlobalTheory.uloc_of_triv_disc σ S v hv x h1 h2`.
-/
theorem mem_Uloc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ hσ n _ J hJ T f bad S p q hq hpq hcop hT hL v hv x hU hint hlast
  subst hJ
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := left_ne_zero_of_mul (hpq ▸ hTE)
  have hq0 : (q : E) ≠ 0 := right_ne_zero_of_mul (hpq ▸ hTE)
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have h0 : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := hU
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h0
  have hMi : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    calc ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
        = (Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
          (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) *
          ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
          rw [h0, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hMient : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
      Formalism.UG.sigR σ (v.adicCompletion F) ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a) := by
    intro a b; rw [hMi]; rfl
  have hMiint : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈
      Formalism.BasicNotions.intV E v := by
    intro a b; rw [hMient]; exact sigR_mem_intV σ v (hint b a)
  choose c hc hcl using hlast
  have hmat : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1 =
      -(((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) := by
    rw [Matrix.sub_mul, Units.mul_inv, Matrix.one_mul]; abel
  have hMilast : ∀ i, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h1 := congrFun (congrFun hmat (Formalism.L2.Col.lastIdx n)) i
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply] at h1
    rw [h1, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.sub_apply, hcl k, mul_assoc]
  have hMilastI : ∀ i, ∃ e ∈ Formalism.BasicNotions.intV E v,
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * e :=
    fun i => ⟨_, neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)), hMilast i⟩
  have hs1 : ∀ a b, Formalism.UG.sigR σ (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a := by
    intro a b
    by_cases hab : a = b
    · subst hab; rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab), map_zero]
  have hcol : ∀ i, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * Formalism.UG.sigR σ (v.adicCompletion F)
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h := congrArg (Formalism.UG.sigR σ (v.adicCompletion F)) (hMilast i)
    rw [map_sub, map_mul, hMient, sigR_sigR σ hσ v, sigR_inclE, ← hq, hs1] at h
    exact h

  have h1 : x ∈ Formalism.UG.levelVL σ (1 : Matrix (Fin n) (Fin n) E) v S.Lb := by
    rw [hL]
    refine Subgroup.mem_inf.2 ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact mulVec_mem_dLat v p hp0 _ hint (fun j => ⟨c j, hc j, hcl j⟩) y hy
    · have := mulVec_mem_dLat v p hp0 _ hMiint hMilastI _ hy
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

  have h2 : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v)
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) S.Lb := by
    intro y hy
    rw [hL, GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq] at hy
    rw [hL]
    obtain ⟨hy1, hy2⟩ := (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v (q : E) hq0 y).1 hy
    rw [show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
      ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *ᵥ y by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    refine (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0) _).2 ⟨fun i _ => ?_, ?_⟩
    · show ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) i j * y j ∈ Formalism.BasicNotions.intV E v
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj, Matrix.sub_apply, hcol i, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E)), mul_assoc]
        exact mul_mem (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)))) hy2
      · exact mul_mem (sub_mem (hint i j) (one_int v i j)) (hy1 j hj)
    · show Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
        ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) j * y j ∈ Formalism.BasicNotions.intV E v
      rw [Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj]
        obtain ⟨a, b, hab⟩ := hcop
        have hE : (a : E) * (p : E) + (b : E) * (q : E) = 1 := by
          exact_mod_cast congrArg (fun r : 𝓞 E => (r : E)) hab
        have hab' : Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) +
            Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) = 1 := by
          have h := congrArg (Formalism.UG.inclE (F := F) (v.adicCompletion F)) hE
          rwa [map_add, map_mul, map_mul, map_one] at h
        have hDc := hcl (Formalism.L2.Col.lastIdx n)
        have hDd := hcol (Formalism.L2.Col.lastIdx n)
        rw [← Matrix.sub_apply] at hDc hDd
        have e : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
            (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) (Formalism.L2.Col.lastIdx n) *
              y (Formalism.L2.Col.lastIdx n)) =
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.sigR σ (v.adicCompletion F)
              (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k
                (Formalism.L2.Col.lastIdx n)) +
             Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * c (Formalism.L2.Col.lastIdx n)) *
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * y (Formalism.L2.Col.lastIdx n)) := by
          linear_combination (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n) -
              Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDc +
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hPinv +
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDd -
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hab'
        rw [e]
        exact mul_mem (add_mem (mul_mem (inclE_int v a)
          (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k _)))))
          (mul_mem (inclE_int v b) (hc _))) hy2
      · rw [Matrix.sub_apply, hcl j, ← mul_assoc, ← mul_assoc, hPinv, one_mul]
        exact mul_mem (hc j) (hy1 j hj)
  exact GlobalTheory.uloc_of_triv_disc σ S v hv x h1 h2

end GlobalTheory.UnitLocLastRow
