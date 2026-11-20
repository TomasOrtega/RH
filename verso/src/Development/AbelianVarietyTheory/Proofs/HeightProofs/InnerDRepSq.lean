import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def casOp (σ : Mx n → (H →L[ℂ] H)) {d e : ℕ} (X : Fin d → Mx n) (Y : Fin e → Mx n) (v : H) : H :=
  ∑ b, dRep σ (Y b) (dRep σ (Y b) v) - ∑ i, dRep σ (X i) (dRep σ (X i) v)

/- English proof (translation)
The claim follows from `dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv hZ) hZ`.
-/
theorem sm_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {v : H} (hv : Sm ε σ v) :
    Sm ε σ (dRep σ Z (dRep σ Z v)) :=
  dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv hZ) hZ

/- English proof (translation)
Establish `hv1` using `dRep_mem (isUnit_Jm ε) hσ hv hZ`. Establish `hb1` using `dRep_mem (isUnit_Jm ε) hσ hb hZ`. Rewrite using `[inner_dRep (isUnit_Jm ε) hσ hb hv1 hZ, inner_dRep (isUnit_Jm ε) hσ hb1 hv hZ, neg_neg]`.
-/
theorem inner_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {b v : H} (hb : Sm ε σ b)
    (hv : Sm ε σ v) : ⟪b, dRep σ Z (dRep σ Z v)⟫_ℂ = ⟪dRep σ Z (dRep σ Z b), v⟫_ℂ := by
  have hv1 := dRep_mem (isUnit_Jm ε) hσ hv hZ
  have hb1 := dRep_mem (isUnit_Jm ε) hσ hb hZ
  rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 hZ, inner_dRep (isUnit_Jm ε) hσ hb1 hv hZ, neg_neg]

variable {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}

/- English proof (translation)
The claim follows from `(smooth (Jm ε) σ).sub_mem ((smooth (Jm ε) σ).sum_mem fun b _ => sm_dRep_sq hσ (hY b) hv) ((smooth (Jm ε) σ).sum_mem fun i _ => sm_dRep_sq hσ (hX i) hv)`.
-/
theorem sm_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) : Sm ε σ (casOp σ X Y v) :=
  (smooth (Jm ε) σ).sub_mem ((smooth (Jm ε) σ).sum_mem fun b _ => sm_dRep_sq hσ (hY b) hv)
    ((smooth (Jm ε) σ).sum_mem fun i _ => sm_dRep_sq hσ (hX i) hv)

/- English proof (translation)
Simplify using `only [casOp, inner_sub_left, inner_sub_right, inner_sum, sum_inner, inner_dRep_sq hσ (hX _) hb hv, inner_dRep_sq hσ (hY _) hb hv]`.
-/
theorem inner_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {b v : H}
    (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, casOp σ X Y v⟫_ℂ = ⟪casOp σ X Y b, v⟫_ℂ := by
  simp only [casOp, inner_sub_left, inner_sub_right, inner_sum, sum_inner, inner_dRep_sq hσ (hX _) hb hv,
    inner_dRep_sq hσ (hY _) hb hv]

/- English proof (translation)
Establish `h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (x + y)) = dRep σ Z (dRep σ Z x) + dRep σ Z (dRep σ Z y)` using `fun Z hZ => Dw_add hσ (l := [Z, Z]) (by simp [hZ]) hx hy`. Simplify using `only [casOp, h _ (hX _), h _ (hY _), Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem casOp_add (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : casOp σ X Y (x + y) = casOp σ X Y x + casOp σ X Y y := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (x + y)) = dRep σ Z (dRep σ Z x) + dRep σ Z (dRep σ Z y) :=
    fun Z hZ => Dw_add hσ (l := [Z, Z]) (by simp [hZ]) hx hy
  simp only [casOp, h _ (hX _), h _ (hY _), Finset.sum_add_distrib]
  abel

/- English proof (translation)
Establish `h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (c • x)) = c • dRep σ Z (dRep σ Z x)` using `fun Z hZ => Dw_smul hσ (l := [Z, Z]) (by simp [hZ]) c hx`. Simplify using `only [casOp, h _ (hX _), h _ (hY _), ← Finset.smul_sum, smul_sub]`.
-/
theorem casOp_smul (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) (c : ℂ)
    {x : H} (hx : Sm ε σ x) : casOp σ X Y (c • x) = c • casOp σ X Y x := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (c • x)) = c • dRep σ Z (dRep σ Z x) :=
    fun Z hZ => Dw_smul hσ (l := [Z, Z]) (by simp [hZ]) c hx
  simp only [casOp, h _ (hX _), h _ (hY _), ← Finset.smul_sum, smul_sub]

end GlobalTheory.TypeSum.CasBasis

end
