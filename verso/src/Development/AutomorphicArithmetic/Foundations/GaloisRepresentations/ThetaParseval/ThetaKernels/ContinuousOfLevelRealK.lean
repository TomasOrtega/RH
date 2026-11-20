import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.WeilContF
end
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
open scoped Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
attribute [local instance] finiteFE modTop topRing
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm`. Use `haveI := finiteFE (F := F) (E := E)`. Use `haveI := modTop (F := F) (E := E)`. Use `haveI := topRing (F := F) (E := E)`. Use `haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup`.

Take `⟨U, hUo, hUf⟩` from `hU`. Set `φ` to `(Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL`. Set `L : (Fin _ → ℝ) →+ WOF F E nS nT` to `(realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom`. Establish `hLc : Continuous L` using `(continuous_realCh nS nT).comp φ.symm.continuous`. Establish `hL0 : ∀ t, (L t).map (finPartF F E) = 0` using `fun t => by`.

Use function extensionality and compare the values at `i j`. Conclude with `realCh_fin nS nT _ i j`. Establish `hLφ : ∀ v, L (φ v) = realCh F E nS nT v` using `fun v => by show realCh F E nS nT (φ.symm (φ v)) = _`. Rewrite using `[φ.symm_apply_apply]`. Use `continuous_iff_continuousAt.2 fun w => ?_` and prove the remaining obligations.

Set `a : WOF F E nS nT → WOF F E nS nT` to `fun w' => w + eInf F • (w' - w)`. Set `u : WOF F E nS nT → WOF F E nS nT` to `fun w' => w' - a w'`. Establish `hsmc : Continuous fun y : WOF F E nS nT => eInf F • y` using `continuous_const_smul _`. Establish `ha : Continuous a` using `continuous_const.add (hsmc.comp (continuous_sub_right w))`. Establish `hu : Continuous u` using `continuous_id.sub ha`.

Establish `huw : u w = 0` using `by show w - (w + eInf F • (w - w)) = 0`. Rewrite using `[sub_self, smul_zero, add_zero, sub_self]`. Establish `hinf : ∀ w', (u w').map (infPartF F E) = 0`. Introduce `w'`. Establish `e : u w' = (w' - w) - eInf F • (w' - w)` using `sub_add_eq_sub_sub _ _ _`.

Use function extensionality and compare the values at `i j`. Use `show infPartF F E (u w' i j) = 0`. Rewrite using `[e]`. Conclude with `infPartF_sub_eInf_smul _`. Establish `hga : Continuous fun w' => g (a w')`.

Establish `h1` using `(hsm _ L hLc hL0 w).continuous.comp (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))`. Use `h1.congr fun w' => ?_` and prove the remaining obligations. Use `show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))`. Rewrite using `[hLφ, realCh_realCo]`. Establish `hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w')` using `(hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga`.

Establish `hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U` using `hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))`. Use `hg.continuousAt.congr (hev.mono fun w' hw' => ?_)` and prove the remaining obligations. Establish `e` using `congrFun (hUf _ hw' (hinf w')) (a w')`. Establish `e2 : a w' + u w' = w'` using `add_sub_cancel _ _`. Use `show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'`.

Rewrite using `[← e]`. Use `show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _`. Rewrite using `[e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`.
-/
theorem continuous_of_level_real_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup
  obtain ⟨U, hUo, hUf⟩ := hU
  let φ := (Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL
  let L : (Fin _ → ℝ) →+ WOF F E nS nT := (realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom
  have hLc : Continuous L := (continuous_realCh nS nT).comp φ.symm.continuous
  have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => by
    funext i j
    exact realCh_fin nS nT _ i j
  have hLφ : ∀ v, L (φ v) = realCh F E nS nT v := fun v => by
    show realCh F E nS nT (φ.symm (φ v)) = _
    rw [φ.symm_apply_apply]
  refine continuous_iff_continuousAt.2 fun w => ?_
  let a : WOF F E nS nT → WOF F E nS nT := fun w' => w + eInf F • (w' - w)
  let u : WOF F E nS nT → WOF F E nS nT := fun w' => w' - a w'
  have hsmc : Continuous fun y : WOF F E nS nT => eInf F • y := continuous_const_smul _
  have ha : Continuous a := continuous_const.add (hsmc.comp (continuous_sub_right w))
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + eInf F • (w - w)) = 0
    rw [sub_self, smul_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPartF F E) = 0 := by
    intro w'
    have e : u w' = (w' - w) - eInf F • (w' - w) := sub_add_eq_sub_sub _ _ _
    funext i j
    show infPartF F E (u w' i j) = 0
    rw [e]
    exact infPartF_sub_eInf_smul _
  have hga : Continuous fun w' => g (a w') := by
    have h1 := (hsm _ L hLc hL0 w).continuous.comp
      (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))
    refine h1.congr fun w' => ?_
    show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))
    rw [hLφ, realCh_realCo]
  have hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') :=
    (hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hUf _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'
  rw [← e]
  show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
end GlobalTheory.WeilContF
end
end
