import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Take `⟨y, rfl⟩` from `exists_unitary_preimage ε hg`. Use `⟨Formalism.MainNotions.S.umat y⁻¹, unitary_matrix_mem_set ε _, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.MainNotions.S.umat]`. Simplify using `[Formalism.MainNotions.S.umat]`.
-/
theorem ujset_right_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ g' ∈ UJset ε, g * g' = 1 ∧ g' * g = 1 := by
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  refine ⟨Formalism.MainNotions.S.umat y⁻¹, unitary_matrix_mem_set ε _, ?_, ?_⟩
  · simp [Formalism.MainNotions.S.umat]
  · simp [Formalism.MainNotions.S.umat]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Introduce `g hg u hu`. Take `⟨g', hg', h1, -⟩` from `ujset_right_inv hg`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `v hv`. Establish `hv' : σ g (σ g' v) = v`.

Rewrite using `[← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg g' hg', h1, hσ.1.1]`. Both sides reduce to the same expression. Rewrite using `[← hv', inner_map_map_of_isURep hσ hg]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hu _ (hC g' hg' v hv)`.
-/
theorem orth_stable (hσ : IsURepOn (UJset ε) σ) (C : Submodule ℂ H)
    (hC : ∀ g ∈ UJset ε, ∀ x ∈ C, σ g x ∈ C) : ∀ g ∈ UJset ε, ∀ u ∈ Cᗮ, σ g u ∈ Cᗮ := by
  intro g hg u hu
  obtain ⟨g', hg', h1, -⟩ := ujset_right_inv hg
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hv' : σ g (σ g' v) = v := by
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg g' hg', h1, hσ.1.1]; rfl
  rw [← hv', inner_map_map_of_isURep hσ hg]
  exact (Submodule.mem_orthogonal _ _).1 hu _ (hC g' hg' v hv)

/- English proof (translation)
Introduce `g hg v`. Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero (orth_stable hσ C hC g hg _ (Cᗮ.starProjection_apply_mem v)) ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[← map_sub]`. Establish `hm : v - Cᗮ.starProjection v ∈ C`.

Use `Cᗮ.sub_starProjection_mem_orthogonal v` as an intermediate fact. Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Conclude with `(Submodule.mem_orthogonal _ _).1 hw _ (hC g hg _ hm)`.
-/
theorem proj_comm (hσ : IsURepOn (UJset ε) σ) (C : Submodule ℂ H) [C.HasOrthogonalProjection]
    (hC : ∀ g ∈ UJset ε, ∀ x ∈ C, σ g x ∈ C) : ∀ g ∈ UJset ε, ∀ v : H,
      Cᗮ.starProjection (σ g v) = σ g (Cᗮ.starProjection v) := by
  intro g hg v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (orth_stable hσ C hC g hg _ (Cᗮ.starProjection_apply_mem v)) ?_
  intro w hw
  rw [← map_sub]
  have hm : v - Cᗮ.starProjection v ∈ C := by
    have := Cᗮ.sub_starProjection_mem_orthogonal v
    rwa [Submodule.orthogonal_orthogonal] at this
  exact (Submodule.mem_orthogonal _ _).1 hw _ (hC g hg _ hm)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Rewrite `hv`, the goal using `[mem_smD_iff]`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg, hF, hEq⟩` from `hv g₀ hg₀`. Use `⟨U, fun g => P (F g), hU, hg, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hgU hgJ => ?_⟩` and prove the remaining obligations. Use `show σ g (P v) = P (F g)`.

Rewrite using `[← hEq g hgU hgJ]`. Conclude with `(hP g hgJ v).symm`.
-/
theorem smooth_of_comm (P : H →L[ℂ] H) (hP : ∀ g ∈ UJset ε, ∀ v : H, P (σ g v) = σ g (P v)) {v : H}
    (hv : v ∈ smD ε σ) : P v ∈ smD ε σ := by
  rw [mem_smD_iff] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hEq⟩ := hv g₀ hg₀
  refine ⟨U, fun g => P (F g), hU, hg, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hgU hgJ => ?_⟩
  show σ g (P v) = P (F g)
  rw [← hEq g hgU hgJ]
  exact (hP g hgJ v).symm

/- English proof (translation)
Establish `hf` using `(isDerivedOn_smE hσ).deriv X hX v`. Establish `heq : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (P v)) = fun t : ℝ => P (σ (NormedSpace.exp ((t : ℂ) • X)) v)`. Use function extensionality and compare the values at `fun t => (hP _ (exp_smul_mem_UJset hX t) v).symm`. Unfold `dS`. Rewrite using `[heq, hf.deriv]`.

Conclude with `((P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf).deriv`.
-/
theorem dS_comm (hσ : IsURepOn (UJset ε) σ) (P : H →L[ℂ] H)
    (hP : ∀ g ∈ UJset ε, ∀ v : H, P (σ g v) = σ g (P v)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : smD ε σ) : dS σ X (P v) = P (dS σ X v) := by
  have hf := (isDerivedOn_smE hσ).deriv X hX v
  have heq : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (P v)) =
      fun t : ℝ => P (σ (NormedSpace.exp ((t : ℂ) • X)) v) :=
    funext fun t => (hP _ (exp_smul_mem_UJset hX t) v).symm
  unfold dS
  rw [heq, hf.deriv]
  exact ((P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf).deriv

/- English proof (translation)
Rewrite using `[smE_apply hσ, smE_apply hσ, map_add, map_smul]`. Use `congr 1`. Conclude with `dS_comm hσ P hP (SmDerA.inG_cpart1 ε _) v`. Use `congr 1`. Conclude with `dS_comm hσ P hP (SmDerA.inG_cpart2 ε _) v`.
-/
theorem smE_comm (hσ : IsURepOn (UJset ε) σ) (P : H →L[ℂ] H)
    (hP : ∀ g ∈ UJset ε, ∀ v : H, P (σ g v) = σ g (P v)) (v : smD ε σ) (hPv : P v ∈ smD ε σ)
    (a b : Fin n) : ((smE ε σ a b ⟨P v, hPv⟩ : smD ε σ) : H) = P ((smE ε σ a b v : smD ε σ) : H) := by
  rw [smE_apply hσ, smE_apply hσ, map_add, map_smul]
  congr 1
  · exact dS_comm hσ P hP (SmDerA.inG_cpart1 ε _) v
  · congr 1
    exact dS_comm hσ P hP (SmDerA.inG_cpart2 ε _) v

section Generic

variable {n : ℕ} {ε : Fin n → Bool}

def projSm (P : L2 ε →L[ℂ] L2 ε) (hP : ∀ g ∈ UJset ε, ∀ v : L2 ε, P (rreg ε g v) = rreg ε g (P v)) :
    smD ε (rreg ε) →ₗ[ℂ] smD ε (rreg ε) :=
  LinearMap.codRestrict (smD ε (rreg ε)) (P.toLinearMap ∘ₗ (smD ε (rreg ε)).subtype)
    (fun v => smooth_of_comm P hP v.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projSm_coe (P : L2 ε →L[ℂ] L2 ε) (hP : ∀ g ∈ UJset ε, ∀ v : L2 ε, P (rreg ε g v) = rreg ε g (P v))
    (v : smD ε (rreg ε)) : ((projSm P hP v : smD ε (rreg ε)) : L2 ε) = P v := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[projSm_coe]`. Conclude with `(smE_comm (rreg_isURepOn ε) P hP v _ a b).symm`.
-/
theorem projSm_comm (P : L2 ε →L[ℂ] L2 ε) (hP : ∀ g ∈ UJset ε, ∀ v : L2 ε, P (rreg ε g v) = rreg ε g (P v))
    (a b : Fin n) (v : smD ε (rreg ε)) :
    projSm P hP (smE ε (rreg ε) a b v) = smE ε (rreg ε) a b (projSm P hP v) := by
  apply Subtype.ext
  rw [projSm_coe]
  exact (smE_comm (rreg_isURepOn ε) P hP v _ a b).symm

/- English proof (translation)
Establish `hR` using `rreg_isURepOn ε`. Establish `hDR` using `isDerivedOn_smE hR`. Use `set C := closGen (smE ε (rreg ε)) W with hCdef`. Establish `hCc : IsClosed (C : Set (L2 ε))` using `Submodule.isClosed_topologicalClosure _`. Establish `: CompleteSpace C` using `hCc.completeSpace_coe`.

Establish `hCst : ∀ g ∈ UJset ε, ∀ x ∈ C, rreg ε g x ∈ C` using `closure_genSub_stable hR hDR hW.1 hW.2.1 hcas`. Establish `hPc` using `proj_comm hR C hCst`. Use `set ψ := projSm (Cᗮ.starProjection) hPc ∘ₗ φ with hψ`. Establish `hψi : ∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y)`. Introduce `a b y hy`.

Simplify using `only [hψ, LinearMap.comp_apply, hφ a b y hy, projSm_comm]`. Establish `hWC : ∀ w ∈ W, ((w : smD ε (rreg ε)) : L2 ε) ∈ C`. Introduce `w hw`. Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Conclude with `Submodule.mem_map_of_mem ((le_sInf fun _ hT => hT.1 : W ≤ genSub (smE ε (rreg ε)) W) hw)`.

Establish `hψys : ψ ys = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hψ, LinearMap.comp_apply, projSm_coe, ZeroMemClass.coe_zero]`. Rewrite using `[Submodule.starProjection_apply_eq_zero_iff]`. Conclude with `Submodule.le_orthogonal_orthogonal C (hWC _ hys)`.

Establish `hzero : ∀ x' ∈ X, ψ x' = 0`. Introduce `x' hx'`. Assume the negation of the conclusion as `hne`. Take `⟨W₂, hW₂X, hW₂, -⟩` from `hK3 ψ hψi x' hx' hne`. Take `⟨w₂, hw₂, hw₂0, hw₂K⟩` from `hW₂.2.2.2`.

Take `⟨c, hc⟩` from `hline ψ hψi w₂ (hW₂X hw₂) hw₂K`. Rewrite `hc` using `[hψys, smul_zero]`. Conclude with `hw₂0 hc`. Introduce `x' hx'`. Establish `h0` using `congrArg (fun v : smD ε (rreg ε) => (v : L2 ε)) (hzero x' hx')`.

Simplify using `only [hψ, LinearMap.comp_apply, projSm_coe, ZeroMemClass.coe_zero] at h0`. Rewrite `h0` using `[Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]`. Conclude with `h0`.
-/
theorem image_le_closGen {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (A : Fin n → Fin n → Module.End ℂ Y)
    (G X : Submodule ℂ Y) (lam' : Fin n → ℝ) (φ : Y →ₗ[ℂ] smD ε (rreg ε))
    (hφ : ∀ a b, ∀ y ∈ G, φ (A a b y) = smE ε (rreg ε) a b (φ y))
    (hK3 : ∀ ψ : Y →ₗ[ℂ] smD ε (rreg ε), (∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y)) →
      ∀ x ∈ X, ψ x ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (ys : Y) (hline : ∀ ψ : Y →ₗ[ℂ] smD ε (rreg ε), (∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y)) →
      ∀ w ∈ X.map ψ, IsKHWVec ε (smE ε (rreg ε)) (lowK ε lam') w → ∃ c : ℂ, w = c • ψ ys)
    (W : Submodule ℂ (smD ε (rreg ε))) (hW : IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W)
    (hcas : ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v) (hys : φ ys ∈ W) :
    ∀ x' ∈ X, ((φ x' : smD ε (rreg ε)) : L2 ε) ∈ closGen (smE ε (rreg ε)) W := by
  classical
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  set C := closGen (smE ε (rreg ε)) W with hCdef
  have hCc : IsClosed (C : Set (L2 ε)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace C := hCc.completeSpace_coe
  have hCst : ∀ g ∈ UJset ε, ∀ x ∈ C, rreg ε g x ∈ C :=
    closure_genSub_stable hR hDR hW.1 hW.2.1 hcas
  have hPc := proj_comm hR C hCst
  set ψ := projSm (Cᗮ.starProjection) hPc ∘ₗ φ with hψ
  have hψi : ∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y) := by
    intro a b y hy
    simp only [hψ, LinearMap.comp_apply, hφ a b y hy, projSm_comm]
  have hWC : ∀ w ∈ W, ((w : smD ε (rreg ε)) : L2 ε) ∈ C := by
    intro w hw
    apply Submodule.le_topologicalClosure
    exact Submodule.mem_map_of_mem ((le_sInf fun _ hT => hT.1 : W ≤ genSub (smE ε (rreg ε)) W) hw)
  have hψys : ψ ys = 0 := by
    apply Subtype.ext
    simp only [hψ, LinearMap.comp_apply, projSm_coe, ZeroMemClass.coe_zero]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal C (hWC _ hys)
  have hzero : ∀ x' ∈ X, ψ x' = 0 := by
    intro x' hx'
    by_contra hne
    obtain ⟨W₂, hW₂X, hW₂, -⟩ := hK3 ψ hψi x' hx' hne
    obtain ⟨w₂, hw₂, hw₂0, hw₂K⟩ := hW₂.2.2.2
    obtain ⟨c, hc⟩ := hline ψ hψi w₂ (hW₂X hw₂) hw₂K
    rw [hψys, smul_zero] at hc
    exact hw₂0 hc
  intro x' hx'
  have h0 := congrArg (fun v : smD ε (rreg ε) => (v : L2 ε)) (hzero x' hx')
  simp only [hψ, LinearMap.comp_apply, projSm_coe, ZeroMemClass.coe_zero] at h0
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0
  exact h0

/- English proof (translation)
Establish `hR` using `rreg_isURepOn ε`. Establish `hDR` using `isDerivedOn_smE hR`. Establish `hφx : φ x ≠ 0`. Introduce `h0`. Conclude with `hxZ (hZφ x hx 0 Z.zero_mem (by rw [h0, map_zero]))`.

Take `⟨W, hWX, hW, hcas⟩` from `hK3 φ hφ x hx hφx`. Take `⟨ys, hysX, hline⟩` from `hline`. Establish `hys : φ ys ∈ W`. Take `⟨w, hw, hw0, hwK⟩` from `hW.2.2.2`. Take `⟨c, hc⟩` from `hline φ hφ w (hWX hw) hwK`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; rw [zero_smul] at hc; exact hw0 hc`. Establish `: φ ys = c⁻¹ • w` using `by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[this]`. Conclude with `W.smul_mem _ hw`. Establish `hWK` using `kStable_of_isKStableSub hR hDR W hW.1 hW.2.1`.

Establish `hclos` using `image_le_closGen A G X lam' φ hφ hK3 ys hline W hW hcas hys`. Establish `hgen : φ x ∈ genSub (smE ε (rreg ε)) W`. Take `⟨S, hSX, hSf, hSk, hxS⟩` from `hkfin x hx`. Use `set S' : Submodule ℂ (smD ε (rreg ε)) := S.map φ`. Establish `hS'k : IsKStableSub ε (smE ε (rreg ε)) S'`.

Introduce and unpack `a b hab _ ⟨s, hs, rfl⟩`. Rewrite using `[← hφ a b s (hXG (hSX hs))]`. Conclude with `Submodule.mem_map_of_mem (hSk a b hab s hs)`. Establish `hS'K` using `kStable_of_isKStableSub hR hDR S' inferInstance hS'k`. Use `set SH : Submodule ℂ (L2 ε) := S'.map (smD ε (rreg ε)).subtype`.

Establish `hle` using `data_kfin_le hgap hR hDR hW hcas hWK SH (by rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact hclos s (hSX hs)) inferInstance (by`. Introduce and unpack `k hk _ ⟨v, hv, rfl⟩`. Take `⟨w, hw, hweq⟩` from `hS'K k hk v hv`. Rewrite using `[Submodule.subtype_apply, ← hweq]`. Conclude with `Submodule.mem_map_of_mem hw)`.

Take `⟨w, hw, hweq⟩` from `Submodule.mem_map.1 (hle (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hxS)))`. Rewrite using `[← Subtype.ext hweq]` and apply the resulting hypothesis. Use `set N0 : Submodule ℂ (smD ε (rreg ε)) := Z.map φ`. Establish `hN0 : ∀ a b, ∀ v ∈ N0, smE ε (rreg ε) a b v ∈ N0`. Introduce and unpack `a b _ ⟨z, hz, rfl⟩`.

Rewrite using `[← hφ a b z (hXG (hZX hz))]`. Conclude with `Submodule.mem_map_of_mem (hZA a b z hz)`. Establish `hWN0 : W ⊓ N0 = ⊥`. Establish `hk : IsKStableSub ε (smE ε (rreg ε)) (W ⊓ N0)` using `fun a b hab v hv => ⟨hW.2.1 a b hab v hv.1, hN0 a b v hv.2⟩`. Break down `hW.2.2.1 _ inf_le_left hk with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `hWle : W ≤ N0` using `by rw [← h]; exact inf_le_right`. Establish `hgle : genSub (smE ε (rreg ε)) W ≤ N0` using `sInf_le ⟨hWle, hN0⟩`. Take `⟨z, hz, hzeq⟩` from `Submodule.mem_map.1 (hgle hgen)`.

Conclude with `hxZ (hZφ x hx z hz hzeq.symm)`. Use `set Y0 : Submodule ℂ Y := X ⊓ W.comap φ`. Use `set K0 : Submodule ℂ Y0 := (LinearMap.ker φ).comap Y0.subtype`. Take `⟨Q, hQ⟩` from `Submodule.exists_isCompl K0`. Use `⟨Q.map Y0.subtype, W, ?_, ?_, ?_, hW, hcas, hWK⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨q, -, rfl⟩`. Conclude with `(Submodule.mem_inf.1 q.2).1`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Take `⟨y₀, hy₀, rfl⟩` from `Submodule.mem_map.1 (hWX hv)`. Establish `hmem : (⟨y₀, Submodule.mem_inf.2 ⟨hy₀, hv⟩⟩ : Y0) ∈ K0 ⊔ Q` using `by rw [hQ.sup_eq_top]; trivial`. Take `⟨k, hk, q, hq, hqk⟩` from `Submodule.mem_sup.1 hmem`. Use `⟨q, Submodule.mem_map_of_mem hq, ?_⟩` and prove the remaining obligations. Establish `hk0 : φ (k : Y) = 0` using `hk`.

Use `congrArg (fun t : Y0 => φ (t : Y)) hqk` as an intermediate fact. Simplify using `only [Submodule.coe_add, map_add, hk0, zero_add] at this`. Conclude with `this.symm`. Introduce and unpack `⟨_, ⟨q, -, rfl⟩, rfl⟩`. Conclude with `(Submodule.mem_inf.1 q.2).2`.

Introduce and unpack `_ ⟨q, hq, rfl⟩ hz`. Establish `h1 : φ (q : Y) ∈ W ⊓ N0` using `⟨(Submodule.mem_inf.1 q.2).2, Submodule.mem_map_of_mem hz⟩`. Rewrite `h1` using `[hWN0, Submodule.mem_bot]`. Establish `hqK : q ∈ K0` using `h1`. Establish `: q ∈ K0 ⊓ Q` using `⟨hqK, hq⟩`.

Rewrite `this` using `[hQ.inf_eq_bot, Submodule.mem_bot]`. Simplify using `[this]`.
-/
theorem quot_generic {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (A : Fin n → Fin n → Module.End ℂ Y)
    (G X Z : Submodule ℂ Y) (lam' : Fin n → ℝ) (hgap : StdGap ε lam') (φ : Y →ₗ[ℂ] smD ε (rreg ε))
    (hXG : X ≤ G)
    (hφ : ∀ a b, ∀ y ∈ G, φ (A a b y) = smE ε (rreg ε) a b (φ y))
    (hK3 : ∀ ψ : Y →ₗ[ℂ] smD ε (rreg ε), (∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y)) →
      ∀ x ∈ X, ψ x ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (hline : ∃ ys ∈ X, ∀ ψ : Y →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ (A a b y) = smE ε (rreg ε) a b (ψ y)) →
      ∀ w ∈ X.map ψ, IsKHWVec ε (smE ε (rreg ε)) (lowK ε lam') w → ∃ c : ℂ, w = c • ψ ys)
    (hkfin : ∀ x ∈ X, ∃ S : Submodule ℂ Y, S ≤ X ∧ FiniteDimensional ℂ S ∧ IsKStableSub ε A S ∧ x ∈ S)
    (hZX : Z ≤ X) (hZA : ∀ a b, ∀ y ∈ Z, A a b y ∈ Z) (hZφ : ∀ y ∈ X, ∀ y' ∈ Z, φ y = φ y' → y ∈ Z)
    {x : Y} (hx : x ∈ X) (hxZ : x ∉ Z) :
    ∃ (Y' : Submodule ℂ Y) (W : Submodule ℂ (smD ε (rreg ε))), Y' ≤ X ∧
      (∀ v, v ∈ W ↔ ∃ y ∈ Y', v = φ y) ∧ (∀ y ∈ Y', y ∈ Z → y = 0) ∧
      IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W ∧
      (∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v) ∧
      ∀ k' ∈ Kset ε, ∀ v ∈ W, ∃ v'' ∈ W, (v'' : L2 ε) = rreg ε k' (v : L2 ε) := by
  classical
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR

  have hφx : φ x ≠ 0 := by
    intro h0
    exact hxZ (hZφ x hx 0 Z.zero_mem (by rw [h0, map_zero]))
  obtain ⟨W, hWX, hW, hcas⟩ := hK3 φ hφ x hx hφx
  obtain ⟨ys, hysX, hline⟩ := hline
  have hys : φ ys ∈ W := by
    obtain ⟨w, hw, hw0, hwK⟩ := hW.2.2.2
    obtain ⟨c, hc⟩ := hline φ hφ w (hWX hw) hwK
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hw0 hc
    have : φ ys = c⁻¹ • w := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]; exact W.smul_mem _ hw
  have hWK := kStable_of_isKStableSub hR hDR W hW.1 hW.2.1
  have hclos := image_le_closGen A G X lam' φ hφ hK3 ys hline W hW hcas hys

  have hgen : φ x ∈ genSub (smE ε (rreg ε)) W := by
    obtain ⟨S, hSX, hSf, hSk, hxS⟩ := hkfin x hx
    set S' : Submodule ℂ (smD ε (rreg ε)) := S.map φ
    have hS'k : IsKStableSub ε (smE ε (rreg ε)) S' := by
      rintro a b hab _ ⟨s, hs, rfl⟩
      rw [← hφ a b s (hXG (hSX hs))]
      exact Submodule.mem_map_of_mem (hSk a b hab s hs)
    have hS'K := kStable_of_isKStableSub hR hDR S' inferInstance hS'k
    set SH : Submodule ℂ (L2 ε) := S'.map (smD ε (rreg ε)).subtype
    have hle := data_kfin_le hgap hR hDR hW hcas hWK SH
      (by rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact hclos s (hSX hs)) inferInstance
      (by
        rintro k hk _ ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hweq⟩ := hS'K k hk v hv
        rw [Submodule.subtype_apply, ← hweq]
        exact Submodule.mem_map_of_mem hw)
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.1 (hle (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hxS)))
    rwa [← Subtype.ext hweq]

  set N0 : Submodule ℂ (smD ε (rreg ε)) := Z.map φ
  have hN0 : ∀ a b, ∀ v ∈ N0, smE ε (rreg ε) a b v ∈ N0 := by
    rintro a b _ ⟨z, hz, rfl⟩
    rw [← hφ a b z (hXG (hZX hz))]
    exact Submodule.mem_map_of_mem (hZA a b z hz)
  have hWN0 : W ⊓ N0 = ⊥ := by
    have hk : IsKStableSub ε (smE ε (rreg ε)) (W ⊓ N0) := fun a b hab v hv =>
      ⟨hW.2.1 a b hab v hv.1, hN0 a b v hv.2⟩
    rcases hW.2.2.1 _ inf_le_left hk with h | h
    · exact h
    · exfalso
      have hWle : W ≤ N0 := by rw [← h]; exact inf_le_right
      have hgle : genSub (smE ε (rreg ε)) W ≤ N0 := sInf_le ⟨hWle, hN0⟩
      obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1 (hgle hgen)
      exact hxZ (hZφ x hx z hz hzeq.symm)

  set Y0 : Submodule ℂ Y := X ⊓ W.comap φ
  set K0 : Submodule ℂ Y0 := (LinearMap.ker φ).comap Y0.subtype
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl K0
  refine ⟨Q.map Y0.subtype, W, ?_, ?_, ?_, hW, hcas, hWK⟩
  · rintro _ ⟨q, -, rfl⟩; exact (Submodule.mem_inf.1 q.2).1
  · intro v
    constructor
    · intro hv
      obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 (hWX hv)
      have hmem : (⟨y₀, Submodule.mem_inf.2 ⟨hy₀, hv⟩⟩ : Y0) ∈ K0 ⊔ Q := by rw [hQ.sup_eq_top]; trivial
      obtain ⟨k, hk, q, hq, hqk⟩ := Submodule.mem_sup.1 hmem
      refine ⟨q, Submodule.mem_map_of_mem hq, ?_⟩
      have hk0 : φ (k : Y) = 0 := hk
      have := congrArg (fun t : Y0 => φ (t : Y)) hqk
      simp only [Submodule.coe_add, map_add, hk0, zero_add] at this
      exact this.symm
    · rintro ⟨_, ⟨q, -, rfl⟩, rfl⟩
      exact (Submodule.mem_inf.1 q.2).2
  · rintro _ ⟨q, hq, rfl⟩ hz
    have h1 : φ (q : Y) ∈ W ⊓ N0 := ⟨(Submodule.mem_inf.1 q.2).2, Submodule.mem_map_of_mem hz⟩
    rw [hWN0, Submodule.mem_bot] at h1
    have hqK : q ∈ K0 := h1
    have : q ∈ K0 ⊓ Q := ⟨hqK, hq⟩
    rw [hQ.inf_eq_bot, Submodule.mem_bot] at this
    simp [this]

end Generic

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
