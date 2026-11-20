import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOff

noncomputable def evAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem map_conj_eq_one {R S : Type} [CommRing R] [CommRing S] {m k : ℕ} (f : R →+* S) (b : Matrix (Fin m) (Fin k) R)
    (b' : Matrix (Fin k) (Fin m) R) (K : Matrix (Fin k) (Fin k) R) (hb : b * b' = 1) (hK : K.map f = 1) :
    (b * K * b').map f = 1 := by
  rw [Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, hb, Matrix.map_one _ (map_zero f) (map_one f)]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem evAt_swapCast_symm (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (x : ReciprocityTheory.Aut.AL D.host.E) :
    evAt D v ((swapCast hF).symm x) =
      (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E (v.adicCompletion (maximalRealSubfield D.host.E)))
        (ReciprocityTheory.Aut.compAt D.host.E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingEquiv.map_zero, RingHom.map_zero, RingHom.map_zero, _root_.map_zero]
  | tmul e a => rfl
  | add x y hx hy => rw [RingEquiv.map_add, RingHom.map_add, RingHom.map_add, _root_.map_add, hx, hy]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem map_evAt_eq_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {n : ℕ}
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (κ : Formalism.AUTREP.GAf D.host.E n) (hA : ReciprocityTheory.Aut.TrivOutside A κ) (hv : v ∉ A) :
    ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (evAt D v) = 1 := by
  have h1 := hA v hv
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.map_apply] at h2
  rw [Matrix.map_apply, Matrix.map_apply, evAt_swapCast_symm, h2]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem stdFrame_stab_red : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β ∧ ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (PP : Formalism.L2.DIV.Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn β PP (finE V (P.ψ κ)) = 1 := by
  intro D V n hF P β Λ hP hB κ hκ
  have hSt : finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hκ)
  refine ⟨hSt, fun A v PP hA hPP hv => ?_⟩
  have hu : PP.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPP
  refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt ?_
  rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, hu]
  obtain ⟨⟨b, b', hbb, -, hmat⟩, -⟩ := hP
  have hF1 : (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (evAt D v) = 1 := by
    rw [hmat κ]
    exact map_conj_eq_one _ _ _ _ hbb (map_evAt_eq_one D hF A v κ hA hv)
  intro i j
  have h3 := congrFun (congrFun hF1 i) j
  change evAt D v (finPart D ((Formalism.L2.Theta.mt V (P.ψ κ) - 1) i j)) = 0
  rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub]
  change evAt D v (finMat D.sp.cm.sig V.gram (P.ψ κ) i j) - _ = 0
  rw [Matrix.map_apply] at h3
  rw [h3, sub_eq_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

end GlobalTheory.FrameOff
