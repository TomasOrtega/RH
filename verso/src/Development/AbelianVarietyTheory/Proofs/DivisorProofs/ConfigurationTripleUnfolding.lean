import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
noncomputable section

namespace GlobalTheory.MixVUnipPlane

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' hT k a hx hι`. Establish `hP` using `(GlobalTheory.ThK.Check.isPair_of_isTriple hT).1`. Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Establish `hstd : IsStd B.ψ` using `hP.base.std`. Establish `hH` using `hC.hH`.

Establish `hc : ∀ t : E, cA σ (inclR (F` using `F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl`. Establish `hact : ∀ w, actAB (cA σ) ((k, 1) : UA σ G.V.J × UA σ G.W.J) w = mat k * w`. Introduce `w`. Simplify using `[actAB, mat]`. Establish `hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) w w' = 0 → G.M.co.rho B.ψ w (G.M.co.rho B.ψ w' Φ) = G.M.co.rho B.ψ (w + w') Φ`.

Introduce `w w' Φ h0`. Simplify using `only [Darboux.rho]`. Establish `hlaw : ∀ (v v' : (Fin (b + 2) × Fin (b + 2 + a') → AF F) × (Fin (b + 2) × Fin (b + 2 + a') → AF F)) (φ : (Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ), schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ`. Introduce `v v' φ`. Use function extensionality and compare the values at `x`.

Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add]`. Use `congr 2`. Take the linear combination `(-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)`. Rewrite using `[hlaw, ← G.M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]`. Establish `hcol : ∀ m, ∑ i, ∑ j, H.ι i m * (G.V.J i j * σ (H.x j)) = 0`.

Introduce `m`. Establish `h` using `(hH.orth (Pi.single m 1)).1`. Simplify using `only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h`. Simplify `h` using `[Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul]`. Establish `hperp : ∀ (z : Matrix (Fin b) (Fin (b + 2 + a')) (AE F E)) (q : Fin (b + 2 + a') → AE F E), symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0`.

Introduce `z q`. Establish `hinner : ∀ j, ∑ i, ∑ l, (incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l) = 0`. Introduce `j`. Establish `e1 : ∀ i l, (incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l) = ∑ m, z m j * inclR (F` using `F) (AF F) (H.ι i m * (G.V.J i l * σ (H.x l))) := by`. Introduce `i l`.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [incM, incV, Matrix.map_apply, hc, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `[map_sum, Finset.mul_sum]`. Use `_ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]`. Establish `hTn : hTens (cA σ) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0`. Unfold `hTens`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `e2 : ∀ i l, ∑ r, (incM F H.ι * z) i j * incM F G.V.J i l * incM F G.W.J j r * cA σ (Matrix.vecMulVec (incV F H.x) q l r) = ((incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l)) * ∑ r, incM F G.W.J j r * cA σ (q r)`. Introduce `i l`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMulVec_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e2, ← Finset.sum_mul, hinner j, zero_mul]`. Simplify using `[symp, hTn]`.

Use `choose β hβ using fun j : Fin b => hι (Pi.single j 1)`. Establish `hgι : mat k * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β`. Use extensionality with `i j`. Establish `h` using `congrFun (hβ j) i`. Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one]`.

Simplify `h` using `[Matrix.vecMulVec_apply, mul_comm]`. Use `⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩` and prove the remaining obligations. Establish `hΨ` using `hs.pres (k, 1) Φ hΦ`. Rewrite using `[hs.impl (k, 1) _ Φ hΦ, hact]`. Establish `hw : mat k * (incM F H.ι * z * (incM F H'.ι)ᵀ) = incM F H.ι * (z * (incM F H'.ι)ᵀ) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (β ᵥ* z))`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc, hgι, Matrix.add_mul]`. Use `congr 1`. Rewrite using `[Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]`. Establish `hh` using `he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (β ᵥ* z))) _ hΨ)`. Rewrite using `[hw, ← hcomp _ _ _ (hperp _ _), ← Matrix.mul_assoc, hh, he.inv _ (Or.inr ⟨_, rfl⟩) _ hΨ]`.

Establish `hΨ` using `hs.pres (k, 1) Φ hΦ`. Rewrite using `[hs.impl (k, 1) _ Φ hΦ, hact]`. Break down `hu with ⟨y, rfl⟩ | ⟨z, rfl⟩` into its components or cases. Rewrite using `[Matrix.mul_vecMulVec]`. Conclude with `he.inv _ (Or.inl ⟨_, rfl⟩) _ hΨ`.

Rewrite using `[Matrix.mul_vecMulVec, hx]`. Use `he.inv _ (Or.inr ⟨a • z, ?_⟩) _ hΨ` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (k : UA σ G.V.J) (a : AE F E), mat k *ᵥ incV F H.x = a • incV F H.x →
    (∀ z : Fin b → AE F E, ∃ c : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + c • incV F H.x) →
    (∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      e (om (k, 1) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ)) = G₁.M.co.rho B.ψ z (e (om (k, 1) Φ))) ∧
    ∀ u ∈ isoA (F := F) H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (k, 1) (G.M.co.rho B.ψ u Φ)) = e (om (k, 1) Φ) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' hT k a hx hι
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hH := hC.hH
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have hact : ∀ w, actAB (cA σ) ((k, 1) : UA σ G.V.J × UA σ G.W.J) w = mat k * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) w w' = 0 →
      G.M.co.rho B.ψ w (G.M.co.rho B.ψ w' Φ) = G.M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin (b + 2) × Fin (b + 2 + a') → AF F) × (Fin (b + 2) × Fin (b + 2 + a') → AF F))
        (φ : (Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← G.M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]
  have hcol : ∀ m, ∑ i, ∑ j, H.ι i m * (G.V.J i j * σ (H.x j)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin b) (Fin (b + 2 + a')) (AE F E)) (q : Fin (b + 2 + a') → AE F E),
      symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ l, (incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l) = 0 := by
      intro j
      have e1 : ∀ i l, (incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (G.V.J i l * σ (H.x l))) := by
        intro i l
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ l, z m j * inclR (F := F) (AF F) (H.ι i m * (G.V.J i l * σ (H.x l))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ l, z m j * inclR (F := F) (AF F) (H.ι i m * (G.V.J i l * σ (H.x l))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ l, H.ι i m * (G.V.J i l * σ (H.x l))) := by
            simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hTn : hTens (cA σ) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i l, ∑ r, (incM F H.ι * z) i j * incM F G.V.J i l * incM F G.W.J j r *
          cA σ (Matrix.vecMulVec (incV F H.x) q l r) =
          ((incM F H.ι * z) i j * incM F G.V.J i l * cA σ (incV F H.x l)) * ∑ r, incM F G.W.J j r * cA σ (q r) := by
        intro i l
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hTn]
  choose β hβ using fun j : Fin b => hι (Pi.single j 1)
  have hgι : mat k * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (k, 1) Φ hΦ
    rw [hs.impl (k, 1) _ Φ hΦ, hact]
    have hw : mat k * (incM F H.ι * z * (incM F H'.ι)ᵀ) =
        incM F H.ι * (z * (incM F H'.ι)ᵀ) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (β ᵥ* z)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd
      (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (β ᵥ* z))) _ hΨ)
    rw [hw, ← hcomp _ _ _ (hperp _ _), ← Matrix.mul_assoc, hh, he.inv _ (Or.inr ⟨_, rfl⟩) _ hΨ]
  · have hΨ := hs.pres (k, 1) Φ hΦ
    rw [hs.impl (k, 1) _ Φ hΦ, hact]
    rcases hu with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Matrix.mul_vecMulVec]
      exact he.inv _ (Or.inl ⟨_, rfl⟩) _ hΨ
    · rw [Matrix.mul_vecMulVec, hx]
      refine he.inv _ (Or.inr ⟨a • z, ?_⟩) _ hΨ
      rw [Matrix.mulVec_smul]
      ext i j
      simp [Matrix.vecMulVec_apply]
      ring

end GlobalTheory.MixVUnipPlane
