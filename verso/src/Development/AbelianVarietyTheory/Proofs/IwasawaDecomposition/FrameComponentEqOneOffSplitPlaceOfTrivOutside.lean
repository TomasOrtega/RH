import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrameOffPlace

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).symm ((1 : E) ⊗ₜ[F1] a) = a ⊗ₜ[F1] (1 : E)`. Apply `(GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[e, Algebra.TensorProduct.comm_tmul, hι, map_one, one_mul, GlobalTheory.AdeleBaseChange.adMap_apply]`.
-/
theorem swap_one_tmul_apply {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (ι : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1 →+* FiniteAdeleRing (𝓞 E) E)
    (hι : ∀ x a, ι (x ⊗ₜ[F1] a) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (a : FiniteAdeleRing (𝓞 F2) F2) (Q : HeightOneSpectrum (𝓞 E)) :
    ι (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.Mem.R3.swapCast h).symm ((1 : E) ⊗ₜ[F2] a))) Q =
      GlobalTheory.AdeleBaseChange.locMap F2 Q (a (Q.under (𝓞 F2))) := by
  subst h
  have e : (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).symm ((1 : E) ⊗ₜ[F1] a) = a ⊗ₜ[F1] (1 : E) := by
    apply (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [e, Algebra.TensorProduct.comm_tmul, hι, map_one, one_mul, GlobalTheory.AdeleBaseChange.adMap_apply]

end GlobalTheory.FrameOffPlace

namespace GlobalTheory.FrameOffPlace

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V n hF P β hP s κ hκ Q hQ a b`. Take `⟨⟨β0, β0', h1, -, hβ⟩, -⟩` from `hP`. Set `v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))` to `Q.under _`. Establish `hvs : v ∉ ({s.v} : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))))`. Introduce `h`.

Conclude with `hQ (congrArg HeightOneSpectrum.asIdeal (Set.mem_singleton_iff.1 h))`. Set `f : ReciprocityTheory.Aut.AL D.host.E →+* Q.adicCompletion D.host.E` to `(GlobalTheory.StdFrames.cpt Q).comp ((Formalism.IndefR.Lev.swapAE D).comp (GlobalTheory.Mem.R3.swapCast hF).symm.toRingHom)`. Establish `hf0 : ∀ c : ReciprocityTheory.Aut.AFplus D.host.E, ReciprocityTheory.Aut.evalAt D.host.E v c = 0 → f ((1 : D.host.E) ⊗ₜ c) = 0`. Introduce `c hc`. Establish `e` using `swap_one_tmul_apply hF (GlobalTheory.StdFrames.toAd D) (GlobalTheory.StdFrames.toAd_spec D) c Q`.

Establish `e' : f ((1 : D.host.E) ⊗ₜ c) = GlobalTheory.AdeleBaseChange.locMap _ Q (c (Q.under _))` using `e`. Rewrite using `[e']`. Express the relevant statement in the definitionally equal form `GlobalTheory.AdeleBaseChange.locMap _ Q (ReciprocityTheory.Aut.evalAt D.host.E v c) = 0`. Rewrite using `[hc, map_zero]`. Establish `hsurj : Function.Surjective (ReciprocityTheory.Aut.evalAt D.host.E v)` using `fun c => ⟨⟨Pi.single v c, (Filter.eventually_cofinite_ne v).mono fun w hw => by`.

Rewrite using `[Pi.single_eq_of_ne hw]; exact zero_mem _⟩, by`. Express the relevant statement in the definitionally equal form `Pi.single v c v = c`. Rewrite using `[Pi.single_eq_same]⟩`. Establish `hker : ∀ y y' : ReciprocityTheory.Aut.AL D.host.E, ReciprocityTheory.Aut.compAt D.host.E v y = ReciprocityTheory.Aut.compAt D.host.E v y' → f y = f y'`. Introduce `y y' h`.

Establish `hm : y - y' ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield D.host.E) D.host.E) (ReciprocityTheory.Aut.evalAt D.host.E v))`. Rewrite using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `h`. Rewrite `hm` using `[Algebra.TensorProduct.lTensor_ker _ hsurj]`. Establish `hle : RingHom.ker (ReciprocityTheory.Aut.evalAt D.host.E v) ≤ (RingHom.ker f).comap (Algebra.TensorProduct.includeRight : ReciprocityTheory.Aut.AFplus D.host.E →ₐ[maximalRealSubfield D.host.E] ReciprocityTheory.Aut.AL D.host.E)`.

Introduce `c hc`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Conclude with `hf0 c hc`. Establish `h2` using `Ideal.map_le_iff_le_comap.2 hle hm`. Rewrite `h2` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `h2`. Establish `hK : (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f = 1`. Establish `e` using `hκ v hvs`. Use extensionality with `i j`. Establish `e2` using `congrFun (congrFun e i) j`.

Rewrite `e2`, the goal using `[Matrix.map_apply]`. Rewrite `e2`, the goal using `[Matrix.one_apply]`. Use `split_ifs at e2 ⊢`. Rewrite using `[hker _ 1 (e2.trans (map_one _).symm), map_one]`. Rewrite using `[hker _ 0 (e2.trans (map_zero _).symm), map_zero]`.

Set `g : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* Q.adicCompletion D.host.E` to `(GlobalTheory.StdFrames.cpt Q).comp (Formalism.IndefR.Lev.swapAE D)`. Establish `hmain : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) = 1`. Establish `e1 : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map (Formalism.IndefR.Lev.swapAE D)` using `rfl`. Establish `e2 : ∀ {k l : Type} (M : Matrix k l (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)), (M.map (Formalism.IndefR.Lev.swapAE D)).map (GlobalTheory.StdFrames.cpt Q) = M.map g` using `fun M => rfl`. Establish `e3 : ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.Mem.R3.swapCast hF).symm).map g = (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f` using `rfl`.

Rewrite using `[e1, e2, hβ κ, Matrix.map_mul, Matrix.map_mul, e3, hK, Matrix.mul_one, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero g) (map_one g)]`. Establish `e : (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q) = (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).map (GlobalTheory.StdFrames.cpt Q)`. Establish `hinv : (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * β.val.map (GlobalTheory.StdFrames.cpt Q) = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]`. Use `_ = 1 := by rw [hmain, Matrix.mul_one, hinv]`. Use `_ = _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm`. Conclude with `congrFun (congrFun e a) b`.
-/
theorem cpt_conj_finE_eq_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  classical
  intro D V n hF P β hP s κ hκ Q hQ a b
  obtain ⟨⟨β0, β0', h1, -, hβ⟩, -⟩ := hP
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := Q.under _
  have hvs : v ∉ ({s.v} : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) := by
    intro h
    exact hQ (congrArg HeightOneSpectrum.asIdeal (Set.mem_singleton_iff.1 h))
  let f : ReciprocityTheory.Aut.AL D.host.E →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp ((Formalism.IndefR.Lev.swapAE D).comp (GlobalTheory.Mem.R3.swapCast hF).symm.toRingHom)
  have hf0 : ∀ c : ReciprocityTheory.Aut.AFplus D.host.E, ReciprocityTheory.Aut.evalAt D.host.E v c = 0 →
      f ((1 : D.host.E) ⊗ₜ c) = 0 := by
    intro c hc
    have e := swap_one_tmul_apply hF (GlobalTheory.StdFrames.toAd D) (GlobalTheory.StdFrames.toAd_spec D) c Q
    have e' : f ((1 : D.host.E) ⊗ₜ c) = GlobalTheory.AdeleBaseChange.locMap _ Q (c (Q.under _)) := e
    rw [e']
    change GlobalTheory.AdeleBaseChange.locMap _ Q (ReciprocityTheory.Aut.evalAt D.host.E v c) = 0
    rw [hc, map_zero]
  have hsurj : Function.Surjective (ReciprocityTheory.Aut.evalAt D.host.E v) := fun c =>
    ⟨⟨Pi.single v c, (Filter.eventually_cofinite_ne v).mono fun w hw => by
      rw [Pi.single_eq_of_ne hw]; exact zero_mem _⟩, by
      change Pi.single v c v = c
      rw [Pi.single_eq_same]⟩
  have hker : ∀ y y' : ReciprocityTheory.Aut.AL D.host.E,
      ReciprocityTheory.Aut.compAt D.host.E v y = ReciprocityTheory.Aut.compAt D.host.E v y' → f y = f y' := by
    intro y y' h
    have hm : y - y' ∈ RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield D.host.E) D.host.E) (ReciprocityTheory.Aut.evalAt D.host.E v)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h
    rw [Algebra.TensorProduct.lTensor_ker _ hsurj] at hm
    have hle : RingHom.ker (ReciprocityTheory.Aut.evalAt D.host.E v) ≤ (RingHom.ker f).comap
        (Algebra.TensorProduct.includeRight : ReciprocityTheory.Aut.AFplus D.host.E →ₐ[maximalRealSubfield D.host.E] ReciprocityTheory.Aut.AL D.host.E) := by
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hf0 c hc
    have h2 := Ideal.map_le_iff_le_comap.2 hle hm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hK : (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f = 1 := by
    have e := hκ v hvs
    ext i j
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at e2 ⊢
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · rw [hker _ 1 (e2.trans (map_one _).symm), map_one]
    · rw [hker _ 0 (e2.trans (map_zero _).symm), map_zero]
  let g : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp (Formalism.IndefR.Lev.swapAE D)
  have hmain : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
    have e1 : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map (Formalism.IndefR.Lev.swapAE D) := rfl
    have e2 : ∀ {k l : Type} (M : Matrix k l (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
        (M.map (Formalism.IndefR.Lev.swapAE D)).map (GlobalTheory.StdFrames.cpt Q) = M.map g := fun M => rfl
    have e3 : ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.Mem.R3.swapCast hF).symm).map g =
        (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f := rfl
    rw [e1, e2, hβ κ, Matrix.map_mul, Matrix.map_mul, e3, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero g) (map_one g)]
  have e : (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).map (GlobalTheory.StdFrames.cpt Q) := by
    have hinv : (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * β.val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    calc (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q)
        = (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) *
            β.val.map (GlobalTheory.StdFrames.cpt Q) := by
          rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      _ = 1 := by rw [hmain, Matrix.mul_one, hinv]
      _ = _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  exact congrFun (congrFun e a) b

end GlobalTheory.FrameOffPlace
