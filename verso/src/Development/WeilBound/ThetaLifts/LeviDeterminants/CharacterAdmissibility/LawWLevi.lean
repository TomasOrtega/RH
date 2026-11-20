import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ExistsDoubledUnitaryBlock
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetConjMulVec
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.FrOfFrame
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine
import Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ax_of (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : Ax (adeleClass F) ψ :=
  { axB hψ with delta := axDelta_of lagLine hψ, imp := axImp_of hA hψ }

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem det_ne_of_sig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) {a : ℂ} (h : HasSig (a • J.map τ) r s) : J.det ≠ 0 :=
  fun h0 => GlobalTheory.det_ne_zero_of_hasSig h (by rw [det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])

variable {n d d₁ r s r' s' r₁ s₁ i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W}
  {M₁ : Model σ X W₁} {χX χW : Chr F E} {om : Rep σ X W} {om₁ : Rep σ X W₁} {e : Fn F n d →ₗ[ℂ] Fn F n d₁}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lawW_levi (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {t h₁ m} (hm : IsLevi H' t h₁ m) :
    ∀ Φ ∈ schA F (Fin n × Fin d),
      e (om (1, m) Φ) = ((χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (e Φ) := by
  have hB := hP.base
  have := hB.cm.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, j, hS, hj, hE, hrel, -⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  let T : GL Unit (AE F E) := ⟨diagonal fun _ => t.1, diagonal fun _ => (t⁻¹).1, by simp, by simp⟩
  have hT : GeneralLinearGroup.det T = t := Units.ext (by simp [T])
  have key := TB (ax_of hA hB.std) hS hj hE hF hrel hP.weil.1 hP₁.weil.1
    (parabolic_character_trivial_on_diagonal F E σ hB.cm d₁ W₁.J (-1) (fun i j => by simp [hP₁.skew.skew])
      (det_ne_of_sig _ (hP₁.skew.sig (Classical.arbitrary _)))) m h₁ T hm.2.2 (by
      ext i k
      exact (congrFun hm.1 i).trans (by simp [T, mul_comm]))
  rw [hT, fac, Fintype.card_fin] at key
  rw [absE_eq]
  exact key

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem lawW_left (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (g : UA σ X.J) :
    ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = om₁ (g, 1) (e Φ) := by
  have hB := hP.base
  have := hB.cm.1
  obtain ⟨S, j, hS, hj, hE, hrel, hy⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  obtain ⟨d', hd', hW⟩ := hP.weil.2.1
  obtain ⟨d₁', hd₁', hW₁⟩ := hP₁.weil.2.1
  have hd : ∀ u, d'.e u = M.co.e uᵀ := fun u => hd' uᵀ
  have hd₁ : ∀ u, d₁'.e u = M₁.co.e uᵀ := fun u => hd₁' uᵀ
  refine TA' (ι := incM F H'.ι) (x := incV F H'.x) (y := incV F H'.y) (ax_of hA hB.std) axInt hS hj hE (by simp [hH.rank])
    (fun u z => ?_) (fun b => ?_) (fun b hb => ?_) (fun u => ?_) hW hW₁
    (parabolic_character_trivial_on_diagonal F E σ hB.cm n X.J 1 (fun i j => by simp [hP.herm.herm])
      (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hP.herm).ne_zero) g
  · rw [hd, hd₁, hrel]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun i => a i (), ?_⟩
      rw [← transpose_transpose u, ha, mul_col, transpose_add, transpose_vecMulVec, ← transpose_mul, transpose_transpose]
    · rintro ⟨b, rfl⟩
      refine ⟨replicateCol Unit b, ?_⟩
      rw [mul_col, transpose_add, transpose_vecMulVec, transpose_mul]
      rfl
  · rw [hd, transpose_vecMulVec]
    exact hy b
  · have h1 : ρ *ᵥ incV F H'.y = fun i => (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (AE F E)) i (.inr ()) :=
      funext fun i => congrFun (congrFun hF.rz i) (.inr ())
    have h2 := congrArg (ρ * ·) hb
    simp only [mul_vecMulVec, h1, Matrix.mul_zero] at h2
    funext k
    simpa [vecMulVec_apply] using congrFun (congrFun h2 (.inr ())) k
  · refine ⟨π * u, (ρ * u) (.inl ()), (ρ * u) (.inr ()), ?_⟩
    conv_lhs => rw [← Matrix.one_mul u, ← hF.one, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [add_assoc]
    congr 1
    ext i k
    simp [mul_apply (M := fromCols _ _), vecMulVec_apply]

end PositivityTheory.ThKF0.Chr
