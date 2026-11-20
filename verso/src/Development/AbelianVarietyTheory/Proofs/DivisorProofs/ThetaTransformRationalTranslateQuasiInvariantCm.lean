import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaQuasiRatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem cA_eq_cAF' (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : cA σ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_congr rfl fun k _ => Finset.sum_comm]`. Conclude with `Finset.sum_comm`.
-/
theorem sum_three_fintype_reverse_order {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

/- English proof (translation)
Establish `hB' : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l)`. Introduce `j l`. Establish `h1` using `congrFun (congrFun hB j) l`. Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[h1]`.

Use `show inclR (F := F) (AF F) (ξ₀ * JS⁻¹ j l) = _`. Conclude with `map_mul _ _ _`. Establish `hA' : ∀ i k, incM F JA i k = incAF F E (JT k i)`. Introduce `i k`. Substitute `hA` using the available equality.

Both sides reduce to the same expression. Unfold `symp hTens symplOF hOF`. Use `congr 1`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[sum_three_fintype_reverse_order]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hA', cA_eq_cAF']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem symp_eq_symplOF' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) (x y : WOF F E nS nT) :
    symp (cA σ) ξ (incM F JA) (incM F JB) x y = symplOF σ JS JT ξ₀ x y := by
  have hB' : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := F) (AF F) (ξ₀ * JS⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM F JA i k = incAF F E (JT k i) := by
    intro i k; subst hA; rfl
  unfold symp hTens symplOF hOF
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_three_fintype_reverse_order]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_cAF']
  calc ξ * (x i j * incAF F E (JT k i) * incM F JB j l * cAF σ (y k l))
      = x i j * incAF F E (JT k i) * (ξ * incM F JB j l) * cAF σ (y k l) := by ring
    _ = _ := by rw [hB']; ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w`. Take `⟨y, z, hyz⟩` from `hrat γ`. Establish `hγ : ratWF γ = incM F γ` using `rfl`. Establish `hform` using `co.form (incM F γ) w`. Rewrite `hform` using `[symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz]`.

Unfold `GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho`. Rewrite using `[map_add, hγ, hyz]`. Use `set u : (κ → AF F) × (κ → AF F) := (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu`. Use `set v := co.e w`. Establish `law` using `GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ`.

Establish `hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) * B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`. Establish `hsum : GlobalTheory.WeilM.schr B.ψ (u + v) Φ = B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr B.ψ u (GlobalTheory.WeilM.schr B.ψ v Φ)`. Rewrite using `[law, smul_smul, hinv, one_smul]`. Establish `h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2)`.

Apply `invOf_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]`. Evaluate the numerical expressions. Rewrite using `[hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1 y z, ← hu, symplOHF, hform, h2]`.
-/
theorem thetaTr_ratWF_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratWF γ = incM F γ := rfl
  have hform := co.form (incM F γ) w
  rw [symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add, hγ, hyz]
  set u : (κ → AF F) × (κ → AF F) :=
    (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu
  set v := co.e w
  have law := GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ
  have hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr B.ψ (u + v) Φ =
      B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr B.ψ u (GlobalTheory.WeilM.schr B.ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1 y z, ← hu,
    symplOHF, hform, h2]

end GlobalTheory.ThetaQuasiRatF
