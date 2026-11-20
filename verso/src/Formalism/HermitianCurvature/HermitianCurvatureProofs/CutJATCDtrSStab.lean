import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

namespace DT

variable {k r : ℕ}

/- English proof (translation)
Unfold `eP`. Rewrite using `[kap_prWv_mulVec hz' hg, Qx2.herm_uh hg.1, Matrix.mulVec_sub, Matrix.mulVec_smul]`.
-/
theorem eP_uw {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : B.Mat k r} (hg : g ∈ UWset k r z')
    (ν v : Fin (2 * r + k + 1) → ℂ) : eP k r z' (g *ᵥ ν) (g *ᵥ v) = g *ᵥ eP k r z' ν v := by
  unfold eP
  rw [kap_prWv_mulVec hz' hg, Qx2.herm_uh hg.1, Matrix.mulVec_sub, Matrix.mulVec_smul]

/- English proof (translation)
Use `⟨v - SSn.wbP k r v, -(herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)), herm (Hpk k r) (SSn.prWv k r z' v) ν, ?_, ?_⟩` and prove the remaining obligations. Introduce `i h1 h2`. Simplify using `[SSn.wbP, h1, h2]`. Establish `hP : SSn.prWv k r z' v = SSn.wbP k r v + (herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)) • z'` using `rfl`. Unfold `eP`.

Generalize the expression as in `herm (Hpk k r) (SSn.prWv k r z' v) ν = β`. Rewrite using `[hP, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem decomp (z' ν v : Fin (2 * r + k + 1) → ℂ) :
    ∃ (o : Fin (2 * r + k + 1) → ℂ) (α β : ℂ), (∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) ∧
      v = eP k r z' ν v + o + α • z' + β • ν := by
  refine ⟨v - SSn.wbP k r v, -(herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)),
    herm (Hpk k r) (SSn.prWv k r z' v) ν, ?_, ?_⟩
  · intro i h1 h2
    simp [SSn.wbP, h1, h2]
  · have hP : SSn.prWv k r z' v =
        SSn.wbP k r v + (herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)) • z' := rfl
    unfold eP
    generalize herm (Hpk k r) (SSn.prWv k r z' v) ν = β
    rw [hP, neg_smul]
    abel

/- English proof (translation)
Establish `hcol : ∀ j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g *ᵥ Pi.single j 1 = Pi.single j 1`. Introduce `j hj`. Break down `hj with hj | hj` into its components or cases. Establish `h1` using `(hg ⟨j.val, hj⟩).1`. Establish `e : eI k r ⟨j.val, hj⟩ = j` using `Fin.ext rfl`.

Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hlt : 2 * r + k - j.val < r` using `by omega`. Establish `h1` using `(hg ⟨2 * r + k - j.val, hlt⟩).2`. Establish `e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j` using `Fin.ext (by simp only [esI]; omega)`.

Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hent : ∀ i j : Fin (2 * r + k + 1), (g *ᵥ Pi.single j 1) i = g i j`. Introduce `i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`.

Rewrite using `[ho j hj.1 hj.2, mul_zero] split_ifs with hji`. Rewrite using `[← hji, ho j hj.1 hj.2]`. Both sides reduce to the same expression. Rewrite using `[← hent i j, hcol j (by omega), Pi.single_apply] split_ifs with hij hji hji`. Rewrite using `[one_mul, hij]`.

Conclude with `absurd hij.symm hji`. Conclude with `absurd hji.symm hij`. Rewrite using `[zero_mul]`. Use `_ = o i := by simp`.
-/
theorem fixOut {g : B.Mat k r}
    (hg : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    {o : Fin (2 * r + k + 1) → ℂ} (ho : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) :
    g *ᵥ o = o := by
  have hcol : ∀ j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) →
      g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j hj
    rcases hj with hj | hj
    · have h1 := (hg ⟨j.val, hj⟩).1
      have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
      rw [e] at h1
      exact h1
    · have hlt : 2 * r + k - j.val < r := by omega
      have h1 := (hg ⟨2 * r + k - j.val, hlt⟩).2
      have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := Fin.ext (by simp only [esI]; omega)
      rw [e] at h1
      exact h1
  have hent : ∀ i j : Fin (2 * r + k + 1), (g *ᵥ Pi.single j 1) i = g i j := by
    intro i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ j, g i j * o j = ∑ j, (if j = i then o i else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
        · rw [ho j hj.1 hj.2, mul_zero]
          split_ifs with hji
          · rw [← hji, ho j hj.1 hj.2]
          · rfl
        · rw [← hent i j, hcol j (by omega), Pi.single_apply]
          split_ifs with hij hji hji
          · rw [one_mul, hij]
          · exact absurd hij.symm hji
          · exact absurd hji.symm hij
          · rw [zero_mul]
    _ = o i := by simp

/- English proof (translation)
Establish `hai : a⁻¹ * a = 1` using `NFRadRedS.uw_inv_mul ha`. Establish `hhi : h⁻¹ * h = 1` using `NFRadRedS.uw_inv_mul hh`. Establish `hh'i : h'⁻¹ * h' = 1` using `NFRadRedS.uw_inv_mul hh'`. Establish `hμ₂i : μ₂⁻¹ * μ₂ = 1` using `FrameEntries.inv_mul_uh hμ₂.1`. Establish `hμ₂m : μ₂ * μ₂⁻¹ = 1` using `FrameEntries.mul_inv_uh hμ₂.1`.

Establish `hμ₁m : μ₁ * μ₁⁻¹ = 1` using `FrameEntries.mul_inv_uh hμ₁.1`. Establish `hi' : h'⁻¹ ∈ UWset k r z'` using `LieBracketMultiplication.uw_inv hh'`. Establish `A0 : a *ᵥ (μ₂ *ᵥ z') = μ₂ *ᵥ z'`. Establish `h1 : (a * μ₂ * b) *ᵥ z' = μ₂ *ᵥ z'` using `by rw [hab]`. Rewrite `h1` using `[← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec]`. Then use the resulting hypothesis.

Establish `A : a *ᵥ ν₂ = ν₂`. Rewrite using `[f2, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, A0, ha.2.2]`. Establish `B0 : b *ᵥ (μ₂⁻¹ *ᵥ z) = μ₂⁻¹ *ᵥ z`. Establish `h1 : b * μ₂⁻¹ = μ₂⁻¹ * a⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hai, Matrix.mul_one, hμ₂i, Matrix.one_mul]`. Use `_ = μ₂⁻¹ * a⁻¹ * (a * μ₂ * b) * μ₂⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = μ₂⁻¹ * a⁻¹ := by rw [hab, Matrix.mul_assoc, hμ₂m, Matrix.mul_one]`. Rewrite using `[Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, (LieBracketMultiplication.uw_inv ha).2.2]`. Establish `B : b *ᵥ ν₂' = ν₂'`.

Rewrite using `[f2', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, B0, hb.2.2]`. Establish `e2i : h'⁻¹ *ᵥ ν₂' = ν₁'`. Rewrite using `[← e2, Matrix.mulVec_mulVec, hh'i, Matrix.one_mulVec]`. Establish `C1 : ∀ v, h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) = μ₂ *ᵥ eP k r z' ν₂' v`. Introduce `v`.

Rewrite using `[← eP_uw hz' hi', e2i]`. Conclude with `e3 v`. Establish `Z0 : μ₁ *ᵥ z' = s₁⁻¹ • ν₁ - c₁ • z`. Rewrite using `[f1, smul_smul, inv_mul_cancel₀ hs₁, one_smul, add_sub_cancel_right]`. Establish `Z1 : h *ᵥ (μ₁ *ᵥ z') = s₁⁻¹ • ν₂ - c₁ • z`.

Rewrite using `[Z0, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, hh.2.2]`. Establish `Z2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ z')) = h *ᵥ (μ₁ *ᵥ z')`. Rewrite using `[Z1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, A, ha.2.2]`. Establish `V0 : μ₁ *ᵥ ν₁' = s₁' • (z + c₁' • (μ₁ *ᵥ z'))`. Rewrite using `[f1', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hμ₁m, Matrix.one_mulVec]`.

Establish `V1 : h *ᵥ (μ₁ *ᵥ ν₁') = s₁' • (z + c₁' • (h *ᵥ (μ₁ *ᵥ z')))`. Rewrite using `[V0, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh.2.2]`. Establish `V2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ ν₁')) = h *ᵥ (μ₁ *ᵥ ν₁')`. Rewrite using `[V1, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ha.2.2, Z2]`. Establish `key : ∀ v, a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ v)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ v))`.

Introduce `v`. Take `⟨o, α, β, ho, hv⟩` from `decomp z' ν₂' v`. Establish `E : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ eP k r z' ν₂' v)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v))`. Establish `h1 : b *ᵥ eP k r z' ν₂' v = eP k r z' ν₂' (b *ᵥ v)`. Rewrite using `[← eP_uw hz' hb, B]`.

Rewrite using `[h1, C1, C1, ← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hab]`. Establish `O : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ o)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ o))`. Rewrite using `[fixOut hb.2.1 ho, fixOut hi'.2.1 ho, fixOut (fun c => hμ₁.2 c (by simp)) ho, fixOut hh.2.1 ho, fixOut ha.2.1 ho]`. Establish `Zc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ z')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ z'))`. Rewrite using `[hb.2.2, hi'.2.2, Z2]`.

Establish `Vc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ ν₂')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ ν₂'))`. Rewrite using `[B, e2i, V2]`. Generalize the expression as in `eP k r z' ν₂' v = u at hv E`. Substitute `hv` using the available equality. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul]`.

Rewrite using `[E, O, Zc, Vc]`. Establish `M : a * (h * μ₁ * h'⁻¹) * b = h * μ₁ * h'⁻¹`. Establish `h1 : ∀ v, (a * (h * μ₁ * h'⁻¹) * b) *ᵥ v = (h * μ₁ * h'⁻¹) *ᵥ v`. Introduce `v`. Simplify using `only [← Matrix.mulVec_mulVec]`.

Conclude with `key v`. Conclude with `Matrix.toLin'.injective (LinearMap.ext fun v => by`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply]`. Conclude with `h1 v)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = h⁻¹ * (h * μ₁ * h'⁻¹) * h' := by rw [M]`. Use `_ = (h⁻¹ * h) * μ₁ * (h'⁻¹ * h') := by simp only [Matrix.mul_assoc]`. Use `_ = μ₁ := by rw [hhi, hh'i, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem core {z z' ν₁ ν₂ ν₁' ν₂' : Fin (2 * r + k + 1) → ℂ} {μ₁ μ₂ h h' a b : B.Mat k r}
    (hz' : inWb k r z') (hμ₁ : μ₁ ∈ Q.Glev k r (Fin.last r)) (hμ₂ : μ₂ ∈ Q.Glev k r (Fin.last r))
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z')
    (hab : a * μ₂ * b = μ₂) (e1 : h *ᵥ ν₁ = ν₂) (e2 : h' *ᵥ ν₁' = ν₂')
    (e3 : ∀ v, h *ᵥ (μ₁ *ᵥ eP k r z' ν₁' (h'⁻¹ *ᵥ v)) = μ₂ *ᵥ eP k r z' ν₂' v)
    {s₁ c₁ s₂ c₂ s₁' c₁' s₂' c₂' : ℂ} (hs₁ : s₁ ≠ 0)
    (f1 : ν₁ = s₁ • (μ₁ *ᵥ z' + c₁ • z)) (f2 : ν₂ = s₂ • (μ₂ *ᵥ z' + c₂ • z))
    (f1' : ν₁' = s₁' • (μ₁⁻¹ *ᵥ z + c₁' • z')) (f2' : ν₂' = s₂' • (μ₂⁻¹ *ᵥ z + c₂' • z')) :
    h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = μ₁ := by
  have hai : a⁻¹ * a = 1 := NFRadRedS.uw_inv_mul ha
  have hhi : h⁻¹ * h = 1 := NFRadRedS.uw_inv_mul hh
  have hh'i : h'⁻¹ * h' = 1 := NFRadRedS.uw_inv_mul hh'
  have hμ₂i : μ₂⁻¹ * μ₂ = 1 := FrameEntries.inv_mul_uh hμ₂.1
  have hμ₂m : μ₂ * μ₂⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₂.1
  have hμ₁m : μ₁ * μ₁⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₁.1
  have hi' : h'⁻¹ ∈ UWset k r z' := LieBracketMultiplication.uw_inv hh'
  have A0 : a *ᵥ (μ₂ *ᵥ z') = μ₂ *ᵥ z' := by
    have h1 : (a * μ₂ * b) *ᵥ z' = μ₂ *ᵥ z' := by rw [hab]
    rwa [← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec] at h1
  have A : a *ᵥ ν₂ = ν₂ := by
    rw [f2, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, A0, ha.2.2]
  have B0 : b *ᵥ (μ₂⁻¹ *ᵥ z) = μ₂⁻¹ *ᵥ z := by
    have h1 : b * μ₂⁻¹ = μ₂⁻¹ * a⁻¹ := by
      calc b * μ₂⁻¹ = μ₂⁻¹ * (a⁻¹ * a) * μ₂ * b * μ₂⁻¹ := by
            rw [hai, Matrix.mul_one, hμ₂i, Matrix.one_mul]
        _ = μ₂⁻¹ * a⁻¹ * (a * μ₂ * b) * μ₂⁻¹ := by simp only [Matrix.mul_assoc]
        _ = μ₂⁻¹ * a⁻¹ := by rw [hab, Matrix.mul_assoc, hμ₂m, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, (LieBracketMultiplication.uw_inv ha).2.2]
  have B : b *ᵥ ν₂' = ν₂' := by
    rw [f2', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, B0, hb.2.2]
  have e2i : h'⁻¹ *ᵥ ν₂' = ν₁' := by
    rw [← e2, Matrix.mulVec_mulVec, hh'i, Matrix.one_mulVec]
  have C1 : ∀ v, h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) = μ₂ *ᵥ eP k r z' ν₂' v := by
    intro v
    rw [← eP_uw hz' hi', e2i]
    exact e3 v
  have Z0 : μ₁ *ᵥ z' = s₁⁻¹ • ν₁ - c₁ • z := by
    rw [f1, smul_smul, inv_mul_cancel₀ hs₁, one_smul, add_sub_cancel_right]
  have Z1 : h *ᵥ (μ₁ *ᵥ z') = s₁⁻¹ • ν₂ - c₁ • z := by
    rw [Z0, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, hh.2.2]
  have Z2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ z')) = h *ᵥ (μ₁ *ᵥ z') := by
    rw [Z1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, A, ha.2.2]
  have V0 : μ₁ *ᵥ ν₁' = s₁' • (z + c₁' • (μ₁ *ᵥ z')) := by
    rw [f1', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hμ₁m,
      Matrix.one_mulVec]
  have V1 : h *ᵥ (μ₁ *ᵥ ν₁') = s₁' • (z + c₁' • (h *ᵥ (μ₁ *ᵥ z'))) := by
    rw [V0, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh.2.2]
  have V2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ ν₁')) = h *ᵥ (μ₁ *ᵥ ν₁') := by
    rw [V1, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ha.2.2, Z2]
  have key : ∀ v, a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ v)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ v)) := by
    intro v
    obtain ⟨o, α, β, ho, hv⟩ := decomp z' ν₂' v
    have E : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ eP k r z' ν₂' v)))) =
        h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) := by
      have h1 : b *ᵥ eP k r z' ν₂' v = eP k r z' ν₂' (b *ᵥ v) := by
        rw [← eP_uw hz' hb, B]
      rw [h1, C1, C1, ← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hab]
    have O : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ o)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ o)) := by
      rw [fixOut hb.2.1 ho, fixOut hi'.2.1 ho, fixOut (fun c => hμ₁.2 c (by simp)) ho, fixOut hh.2.1 ho,
        fixOut ha.2.1 ho]
    have Zc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ z')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ z')) := by
      rw [hb.2.2, hi'.2.2, Z2]
    have Vc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ ν₂')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ ν₂')) := by
      rw [B, e2i, V2]
    generalize eP k r z' ν₂' v = u at hv E
    subst hv
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [E, O, Zc, Vc]
  have M : a * (h * μ₁ * h'⁻¹) * b = h * μ₁ * h'⁻¹ := by
    have h1 : ∀ v, (a * (h * μ₁ * h'⁻¹) * b) *ᵥ v = (h * μ₁ * h'⁻¹) *ᵥ v := by
      intro v
      simp only [← Matrix.mulVec_mulVec]
      exact key v
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact h1 v)
  calc h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = h⁻¹ * (a * (h * μ₁ * h'⁻¹) * b) * h' := by
        simp only [Matrix.mul_assoc]
    _ = h⁻¹ * (h * μ₁ * h'⁻¹) * h' := by rw [M]
    _ = (h⁻¹ * h) * μ₁ * (h'⁻¹ * h') := by simp only [Matrix.mul_assoc]
    _ = μ₁ := by rw [hhi, hh'i, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_zero : herm (Hpk k r) 0 0 = 0 := by
  simp [herm]

/- English proof (translation)
Establish `hG` using `NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)`. Establish `hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z')` using `Qx8.inWb_mulVec hG hz'`. Establish `hb` using `(DU.base hz hz' hT hT' hsec hζ).2.1`. Establish `e : SSn.nu0 k r z z' μsec ζ = (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ) • SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')` using `rfl`. Use `⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ), herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z / (Tz k r z : ℂ), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Rewrite `hb` using `[e, h0, zero_smul, herm_zero_zero]`. Conclude with `zero_ne_one hb`. Rewrite using `[← DU.prWv_of hy]`. Conclude with `e`.
-/
theorem first_vector_normal_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, s ≠ 0 ∧ SSn.nu0 k r z z' μsec ζ = s • (NF.muZ k r μsec ζ *ᵥ z' + c • z) := by
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hb := (DU.base hz hz' hT hT' hsec hζ).2.1
  have e : SSn.nu0 k r z z' μsec ζ =
      (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ) • SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z') := rfl
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z / (Tz k r z : ℂ), ?_, ?_⟩
  · intro h0
    rw [e, h0, zero_smul, herm_zero_zero] at hb
    exact zero_ne_one hb
  · rw [← DU.prWv_of hy]
    exact e

/- English proof (translation)
Establish `hG` using `FrameEntries.glev_inv (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ))`. Establish `hy : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)` using `Qx8.inWb_mulVec hG hz`. Use `⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)) (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ), herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' / (Tz k r z' : ℂ), ?_⟩` and prove the remaining obligations. Rewrite using `[← DU.prWv_of hy]`. Both sides reduce to the same expression.
-/
theorem nu0'_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, SSn.nu0' k r z z' μsec ζ = s • ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z + c • z') := by
  have hG := FrameEntries.glev_inv (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ))
  have hy : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hG hz
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))
        (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' / (Tz k r z' : ℂ), ?_⟩
  rw [← DU.prWv_of hy]
  rfl

end DT

/- English proof (translation)
Introduce `k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3 p hp`. Take `⟨ha, hb, hab⟩` from `hp`. Use `⟨LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh) ha) hh, LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh') hb) hh', ?_⟩` and prove the remaining obligations. Take `⟨s₁, c₁, hs₁, f1⟩` from `DT.first_vector_normal_form hz hz' hT hT' hsec h₁`. Take `⟨s₂, c₂, -, f2⟩` from `DT.first_vector_normal_form hz hz' hT hT' hsec h₂`.

Take `⟨s₁', c₁', f1'⟩` from `DT.nu0'_form (z' := z') hz hsec h₁`. Take `⟨s₂', c₂', f2'⟩` from `DT.nu0'_form (z' := z') hz hsec h₂`. Establish `e3' : ∀ v, h *ᵥ (NF.muZ k r μsec ζ₁ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₁) (h'⁻¹ *ᵥ v)) = NF.muZ k r μsec ζ₂ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₂) v`. Introduce `v`. Establish `h3 : (h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹) *ᵥ v = SSn.io0 k r z z' μsec ζ₂ *ᵥ v` using `by rw [e3]`.

Rewrite `h3` using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, DT.ioMulVec, DT.ioMulVec]`. Conclude with `h3`. Conclude with `DT.core hz' (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₁)) (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₂)) hh hh' ha hb hab e1 e2 e3' hs₁ f1 f2 f1' f2'`.
-/
theorem datum_transit_stabilizer : DTStab := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3 p hp
  obtain ⟨ha, hb, hab⟩ := hp
  refine ⟨LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh) ha) hh, LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh') hb) hh', ?_⟩
  obtain ⟨s₁, c₁, hs₁, f1⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₁
  obtain ⟨s₂, c₂, -, f2⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₂
  obtain ⟨s₁', c₁', f1'⟩ := DT.nu0'_form (z' := z') hz hsec h₁
  obtain ⟨s₂', c₂', f2'⟩ := DT.nu0'_form (z' := z') hz hsec h₂
  have e3' : ∀ v, h *ᵥ (NF.muZ k r μsec ζ₁ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₁) (h'⁻¹ *ᵥ v)) =
      NF.muZ k r μsec ζ₂ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₂) v := by
    intro v
    have h3 : (h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹) *ᵥ v = SSn.io0 k r z z' μsec ζ₂ *ᵥ v := by rw [e3]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, DT.ioMulVec, DT.ioMulVec] at h3
    exact h3
  exact DT.core hz' (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₁)) (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₂))
    hh hh' ha hb hab e1 e2 e3' hs₁ f1 f2 f1' f2'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
