import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
import GroundTheory.AutomorphicForms.FourierWhittaker
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.WhitCols

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem avg_eq_setIntegral {ι : Type} [Fintype ι] (Φ : (ι → Ad E) → ℂ) (hΦ : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = ∫ x in vecDomain E ι, Φ x ∂vecMeasure E ι := by
  have hF : IsAddFundamentalDomain (ratV E ι) (vecDomain E ι) (vecMeasure E ι) := isAddFundamentalDomain_vecDomain
  obtain ⟨-, -, -, h⟩ := GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι)
    (vecMeasure E ι) (vecDomain E ι) inferInstance hF Φ hΦ
  rw [h, vecMeasure_vecDomain]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagonal_eq_ratGL (n : ℕ) (γ : GL (Fin n) E) : AdelicGLn.diagonal E n γ = ratGL E n γ := rfl

def colIx {a k : ℕ} (hk : k < a) : Fin k ≃ UnipotentBlockColumnIndex a k k where
  toFun i := ⟨(⟨i.1, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  invFun t := ⟨t.1.1.1, t.2.1⟩
  left_inv i := rfl
  right_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only at h1 h2 h3 ⊢
      omega

def colHom {a k : ℕ} (hk : k < a) : (Fin k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun x := fun t => x ((colIx hk).symm t)
  invFun y := fun i => y (colIx hk i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem colHom_mem_iff {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    colHom hk x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (Fin k) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c (colIx hk i), funext fun i => ?_⟩
    have := congrFun hc (colIx hk i)
    simpa [colHom] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((colIx hk).symm t), rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem blkU_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    (blkU (colHom hk x) : GL (Fin a) (Ad E)) = colGL k x := by
  refine Units.ext ?_
  ext i j
  rw [blkU_apply]
  simp only [colGL, coe_uGL, uMat_apply, colX_apply, Matrix.one_apply, colHom, colIx]
  split_ifs <;> first | rfl | simp_all
  all_goals (exfalso; simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at *; omega)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dot_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    dot (eLast a k) (colHom hk x) = pair (lastVec k) x := by
  rw [dot, pair, ← (colIx hk).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [colHom, eLast, lastVec, colIx, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases h : (i : ℕ) + 1 = k <;> simp [h]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem colT_eq_stepCoeff {a k : ℕ} (hk : k < a) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ (ξ : Fin k → E) g, F (AdelicGLn.diagonal E a (colGL k ξ) * g) = F g) (g : GA E a) :
    colT (GlobalTheory.StdCharConductor.psi E) k F g = stepCoeff k F g := by
  have hψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hl' : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, F (ratGL E a (blkU c) * g) = F g := by
    intro c g
    have e : ratGL E a (blkU c) = AdelicGLn.diagonal E a (colGL k (fun i => c (colIx hk i))) := by
      rw [ratGL_blkU, diagonal_colGL, ← blkU_colHom hk]
      congr 1
      funext t
      simp [colHom]
    rw [e, hl]
  have hP := per_coef hψ (eLast a k) hc hl' g
  have hP' : Per (ratV E (Fin k)) (fun x => (fun y : UnipotentBlockColumnIndex a k k → Ad E =>
      GlobalTheory.StdCharConductor.psi E (-dot (eLast a k) y) * F (blkU y * g)) (colHom hk x)) := by
    refine ⟨hP.1.comp (colHom hk).continuous_toFun, fun γ hγ x => ?_⟩
    simp only [map_add]
    exact hP.2 _ ((colHom_mem_iff hk γ).2 hγ) _
  unfold colT coefF
  rw [← avg_equiv (Fin k → Ad E) (UnipotentBlockColumnIndex a k k → Ad E) (ratV E (Fin k)) (ratV E (UnipotentBlockColumnIndex a k k)) (isCoLat_ratV E _)
    (isCoLat_ratV E _) (colHom hk) (colHom_mem_iff hk) _ hP, avg_eq_setIntegral _ hP']
  unfold stepCoeff vecCoeff
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [blkU_colHom, dot_colHom, GlobalTheory.StdCharConductor.psi_apply]
  ring

def IsUU {j : ℕ} (h : Matrix (Fin j) (Fin j) E) : Prop :=
  ∀ i l : Fin j, l ≤ i → h i l = (1 : Matrix (Fin j) (Fin j) E) i l

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Apply function extensionality and compare values at an arbitrary argument. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem IsUU.isLastRowUnit {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) : IsLastRowUnit h := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · funext c; exact c.elim0
  · funext c
    have hc : c ≤ (⟨j - 1, by omega⟩ : Fin j) := by rw [Fin.le_def]; show (c : ℕ) ≤ j - 1; omega
    rw [vecMul_lastVec _ _ hj, hh _ _ hc, Matrix.one_apply]
    simp only [lastVec, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField E] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. It suffices to derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem isUU_blockMat {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) :
    IsUU (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  intro i l hli
  rw [blockMat_apply]
  split_ifs with ha hb
  · rw [hh _ _ (by rw [Fin.le_def] at hli ⊢; exact hli), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
  · exfalso; rw [Fin.le_def] at hli; omega
  all_goals simp_all [Matrix.one_apply]

omit [NumberField E] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isUU_colX {j : ℕ} (ξ : Fin j → E) : IsUU (uMat (colX (n := j + 1) j ξ)) := by
  intro i l hli
  rw [uMat_apply, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.lt_def, Fin.le_def] at *; omega)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem partialCoeff_uu {n : ℕ} {f : GA E n → ℂ}
    (hf : ∀ γ ∈ mirU E n 0, ∀ g, f (ratGL E n γ * g) = f g) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) E), IsUU (h : Matrix (Fin j) (Fin j) E) → ∀ g,
      partialCoeff f j (AdelicGLn.diagonal E n (blockGL hj h) * g) = partialCoeff f j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h hh g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this]
    exact hf h (mem_mirU.2 fun i k _ hk => hh i k hk) g
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt f hjn]
    have hB : ∀ g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (blockGL hjn.le h) * g) =
        partialCoeff f (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_blockMat hh) g
    have hC : ∀ (ξ : Fin j → E) g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (colGL j ξ) * g) =
        partialCoeff f (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_colX _) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hh.isLastRowUnit]
    rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem colT_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) {k : ℕ} (hk : k < m + 1) :
    colT (GlobalTheory.StdCharConductor.psi E) k (partialCoeff f (k + 1)) = partialCoeff f k := by
  funext g
  rw [partialCoeff_of_lt f hk]
  refine colT_eq_stepCoeff hk (continuous_partialCoeff hc _) (fun ξ g => ?_) g
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_uu hf _ (k + 1) rfl hk _ (isUU_colX _) g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whit_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) :
    ∀ i, i ≤ m → GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) i (partialCoeff f (i + 1)) = partialCoeff f 1
  | 0, _ => rfl
  | i + 1, hi => by
    rw [GlobalTheory.CuspGeneric.whit_succ, colT_partialCoeff hc hf (by omega : i + 1 < m + 1),
      whit_partialCoeff hc hf i (by omega)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem whit_eq_colWhit : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  intro E _ _ m f hc hf g
  rw [GlobalTheory.JSW.whit, whittaker_eq_partialCoeff hc (Nat.succ_pos m), ← whit_partialCoeff hc hf m le_rfl,
    partialCoeff_self]

end GlobalTheory.WhitCols
