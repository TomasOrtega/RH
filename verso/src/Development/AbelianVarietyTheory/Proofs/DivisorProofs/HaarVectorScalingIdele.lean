import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i u hu`. Conclude with `congrFun (h u hu) i`. Introduce `h u hu`. Use function extensionality and compare the values at `i`.

Conclude with `h i u hu`.
-/
theorem at_vec_iff {m : ℕ} {v : Pl F} {w : Fin m → AE F E} :
    At (evFin F v) w ↔ ∀ i, At (evFin F v) (w i) := by
  constructor
  · intro h i u hu
    exact congrFun (h u hu) i
  · intro h u hu
    funext i
    exact h i u hu

/- English proof (translation)
Use `at_evFin_iff.2 ⟨fun w => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.AutFunCompare.map_tensNU_zero (evInf F w) _ _ (fun _ => rfl) y`. Conclude with `GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F w) _ _ (evalV_singleFin_ne hw) y`.
-/
theorem at_liftFin (v : Pl F) (y : Fv F v ⊗[F] E) :
    At (evFin F v) (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) y) := by
  refine at_evFin_iff.2 ⟨fun w => ?_, fun w hw => ?_⟩
  · exact GlobalTheory.AutFunCompare.map_tensNU_zero (evInf F w) _ _ (fun _ => rfl) y
  · exact GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F w) _ _ (evalV_singleFin_ne hw) y

/- English proof (translation)
The claim follows from `GlobalTheory.AutFunCompare.map_tensNU_self (evFin F v) _ _ (evalV_singleFin_self v) y`.
-/
theorem compFin_liftFin (v : Pl F) (y : Fv F v ⊗[F] E) :
    compFin F E v (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) y) = y :=
  GlobalTheory.AutFunCompare.map_tensNU_self (evFin F v) _ _ (evalV_singleFin_self v) y

/- English proof (translation)
Take `⟨h1, h2⟩` from `at_evFin_iff.1 hz`. Take `⟨g1, g2⟩` from `at_evFin_iff.1 (at_liftFin v (compFin F E v z))`. Use `GlobalTheory.Doubling.adele_ext (fun w => (g1 w).trans (h1 w).symm) fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Conclude with `compFin_liftFin w _`. Conclude with `(g2 w hw).trans (h2 w hw).symm`.
-/
theorem liftFin_compFin {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) :
    tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (compFin F E v z) = z := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hz
  obtain ⟨g1, g2⟩ := at_evFin_iff.1 (at_liftFin v (compFin F E v z))
  refine GlobalTheory.Doubling.adele_ext (fun w => (g1 w).trans (h1 w).symm) fun w => ?_
  by_cases hw : w = v
  · subst hw
    exact compFin_liftFin w _
  · exact (g2 w hw).trans (h2 w hw).symm

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v)) ((RestrictedProduct.continuous_eval v).comp continuous_snd)`.
-/
theorem continuous_compFinV (v : Pl F) : Continuous (compFin F E v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd)

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `GlobalTheory.AutFunCompare.continuous_tensNU _ _ (continuous_const.prodMk (continuous_singleFin v))`.
-/
theorem continuous_liftFinV (v : Pl F) :
    Continuous (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU _ _ (continuous_const.prodMk (continuous_singleFin v))

variable (F E) in

def vecAtEquiv (m : ℕ) (v : Pl F) : vecAt F E m (evFin F v) ≃ₜ+ (Fin m → Fv F v ⊗[F] E) where
  toFun w i := compFin F E v (w.1 i)
  invFun y := ⟨fun i => tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (y i),
    at_vec_iff.2 fun i => at_liftFin v (y i)⟩
  left_inv w := Subtype.ext (funext fun i => liftFin_compFin (at_vec_iff.1 w.2 i))
  right_inv y := funext fun i => compFin_liftFin v (y i)
  map_add' a b := funext fun i => map_add _ _ _
  continuous_toFun :=
    continuous_pi fun i => (continuous_compFinV v).comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun :=
    (continuous_pi fun i => (continuous_liftFinV v).comp (continuous_apply i)).subtype_mk _

def vecAtSmulCE {m : ℕ} {v : Pl F} (s : (AE F E)ˣ) : vecAt F E m (evFin F v) ≃ₜ+ vecAt F E m (evFin F v) where
  toFun := vecAtSmul (s : AE F E)
  invFun := vecAtSmul ((s⁻¹ : (AE F E)ˣ) : AE F E)
  left_inv w := Subtype.ext (show ((s⁻¹ : (AE F E)ˣ) : AE F E) • (s : AE F E) • w.1 = w.1 by
    rw [smul_smul, Units.inv_mul, one_smul])
  right_inv w := Subtype.ext (show (s : AE F E) • ((s⁻¹ : (AE F E)ˣ) : AE F E) • w.1 = w.1 by
    rw [smul_smul, Units.mul_inv, one_smul])
  map_add' := map_add _
  continuous_toFun := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
    exact ((continuous_const_smul (s : AE F E)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
    exact ((continuous_const_smul ((s⁻¹ : (AE F E)ˣ) : AE F E)).comp continuous_subtype_val).subtype_mk _

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ m v t ht ν hν`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`.

Take `⟨e0⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology`. Use `haveI : T2Space (AE F E) := e0.isEmbedding.t2Space`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v`.

Use `haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v`. Use `haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v`. Use `haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `set e1 := vecAtEquiv F E m v`.

Use `haveI : LocallyCompactSpace (vecAt F E m (evFin F v)) := e1.toHomeomorph.isClosedEmbedding.locallyCompactSpace`. Use `haveI := hν`. Use `haveI : SecondCountableTopology (vecAt F E m (evFin F v)) := e1.toHomeomorph.isEmbedding.secondCountableTopology`. Use `haveI : BorelSpace (vecAt F E m (evFin F v)) := inferInstance`. Use `haveI : T2Space (vecAt F E m (evFin F v)) := inferInstance`.

Use `haveI : ν.Regular := inferInstance`. Use `set s : (AE F E)ˣ := GlobalTheory.Doubling.conjUnit σ t⁻¹ with hs`. Establish `hf : ⇑(vecAtSmul (m` using `m) (ev := evFin F v) (cA σ (t⁻¹ : (AE F E)ˣ).1)) = ⇑(vecAtSmulCE (m := m) (v := v) s) := by`. Use function extensionality and compare the values at `w`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show cA σ (t⁻¹ : (AE F E)ˣ).1 • w.1 = (s : AE F E) • w.1`. Rewrite using `[cA_eq_sigR]`. Both sides reduce to the same expression. Rewrite using `[hf]`. Establish `h1` using `addEquivAddHaarChar_smul_map ν (vecAtSmulCE (m := m) (v := v) s)`.

Rewrite `h1` using `[← GlobalTheory.ModuLR.addEquivAddHaarChar_transport e1]`. Use `set U0 : (Fv F v ⊗[F] E)ˣ := GlobalTheory.Doubling.unitFin F E v s with hU0`. Use `set Uc : (Fin m → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin m) (Fv F v ⊗[F] E)).toMonoidHom U0`. Establish `hg : (e1.symm.trans (vecAtSmulCE (m` using `m) (v := v) s)).trans e1 = GlobalTheory.ModuNorm.mulUnitCE Uc := by`. Use extensionality with `y i`.

Use `show compFin F E v ((s : AE F E) * tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (y i)) = (U0 : Fv F v ⊗[F] E) * y i`. Rewrite using `[map_mul, compFin_liftFin]`. Both sides reduce to the same expression. Establish `hc : distribHaarChar (Fin m → Fv F v ⊗[F] E) Uc = ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ ^ m`. Rewrite using `[GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin m => Fv F v ⊗[F] E) Uc]`.

Establish `hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin m => Fv F v ⊗[F] E) i).toMonoidHom Uc = U0` using `fun i => Units.ext rfl`. Simplify using `only [hU, GlobalTheory.LocTateInt.distribHaarChar_Ev, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite `h1` using `[hg, ← GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, hc]`. Establish `hn : ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ = (absE F E t)⁻¹`. Express the relevant statement in the definitionally equal form `GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v s) = _`.

Rewrite using `[GlobalTheory.Doubling.absEv_unitFin, hs, show Algebra.norm (AF F) (GlobalTheory.Doubling.conjUnit σ t⁻¹ : AE F E) = Algebra.norm (AF F) ((t⁻¹ : (AE F E)ˣ) : AE F E) from GlobalTheory.Doubling.norm_sigR σ _, ← GlobalTheory.Doubling.absEv_unitFin, map_inv, map_inv, ← absE_of_mem h …`. Rewrite `h1` using `[hn]`. Establish `h0 : absE F E t ≠ 0` using `fun h => by`. Use `congrArg (absE F E) (mul_inv_cancel t)` as an intermediate fact. Rewrite `this` using `[map_mul, h, zero_mul, map_one]`.

Conclude with `zero_ne_one this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, mul_inv_cancel₀ h0, one_pow, one_smul]`. Use `_ = absE F E t ^ m • ((absE F E t)⁻¹ ^ m • ν.map ⇑(vecAtSmulCE (m := m) (v := v) s)) := (smul_smul _ _ _).symm`. Use `_ = absE F E t ^ m • ν := by rw [h1]`.
-/
theorem map_vecAtSmul_cA_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (v : Pl F)
    (t : (AE F E)ˣ), t ∈ idelesAt E (evFin F v) → ∀ ν : Measure (vecAt F E m (evFin F v)), ν.IsAddHaarMeasure →
      ν.map (vecAtSmul (cA σ (t⁻¹ : (AE F E)ˣ).1)) = (absE F E t ^ m) • ν := by
  intro F E _ _ _ _ _ σ m v t ht ν hν
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI : T2Space (AE F E) := e0.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  set e1 := vecAtEquiv F E m v
  haveI : LocallyCompactSpace (vecAt F E m (evFin F v)) := e1.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (vecAt F E m (evFin F v)) := e1.toHomeomorph.isEmbedding.secondCountableTopology
  haveI : BorelSpace (vecAt F E m (evFin F v)) := inferInstance
  haveI : T2Space (vecAt F E m (evFin F v)) := inferInstance
  haveI : ν.Regular := inferInstance
  set s : (AE F E)ˣ := GlobalTheory.Doubling.conjUnit σ t⁻¹ with hs
  have hf : ⇑(vecAtSmul (m := m) (ev := evFin F v) (cA σ (t⁻¹ : (AE F E)ˣ).1)) =
      ⇑(vecAtSmulCE (m := m) (v := v) s) := by
    funext w
    apply Subtype.ext
    show cA σ (t⁻¹ : (AE F E)ˣ).1 • w.1 = (s : AE F E) • w.1
    rw [cA_eq_sigR]
    rfl
  rw [hf]
  have h1 := addEquivAddHaarChar_smul_map ν (vecAtSmulCE (m := m) (v := v) s)
  rw [← GlobalTheory.ModuLR.addEquivAddHaarChar_transport e1] at h1
  set U0 : (Fv F v ⊗[F] E)ˣ := GlobalTheory.Doubling.unitFin F E v s with hU0
  set Uc : (Fin m → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin m) (Fv F v ⊗[F] E)).toMonoidHom U0
  have hg : (e1.symm.trans (vecAtSmulCE (m := m) (v := v) s)).trans e1 = GlobalTheory.ModuNorm.mulUnitCE Uc := by
    ext y i
    show compFin F E v ((s : AE F E) * tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (y i)) =
      (U0 : Fv F v ⊗[F] E) * y i
    rw [map_mul, compFin_liftFin]
    rfl
  have hc : distribHaarChar (Fin m → Fv F v ⊗[F] E) Uc = ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ ^ m := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin m => Fv F v ⊗[F] E) Uc]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin m => Fv F v ⊗[F] E) i).toMonoidHom Uc = U0 :=
      fun i => Units.ext rfl
    simp only [hU, GlobalTheory.LocTateInt.distribHaarChar_Ev, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hg, ← GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, hc] at h1
  have hn : ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ = (absE F E t)⁻¹ := by
    change GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v s) = _
    rw [GlobalTheory.Doubling.absEv_unitFin, hs,
      show Algebra.norm (AF F) (GlobalTheory.Doubling.conjUnit σ t⁻¹ : AE F E) = Algebra.norm (AF F) ((t⁻¹ : (AE F E)ˣ) : AE F E)
        from GlobalTheory.Doubling.norm_sigR σ _,
      ← GlobalTheory.Doubling.absEv_unitFin, map_inv, map_inv, ← absE_of_mem ht]
  rw [hn] at h1
  have h0 : absE F E t ≠ 0 := fun h => by
    have := congrArg (absE F E) (mul_inv_cancel t)
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc ν.map ⇑(vecAtSmulCE (m := m) (v := v) s)
      = (absE F E t ^ m * (absE F E t)⁻¹ ^ m) • ν.map ⇑(vecAtSmulCE (m := m) (v := v) s) := by
        rw [← mul_pow, mul_inv_cancel₀ h0, one_pow, one_smul]
    _ = absE F E t ^ m • ((absE F E t)⁻¹ ^ m • ν.map ⇑(vecAtSmulCE (m := m) (v := v) s)) := (smul_smul _ _ _).symm
    _ = absE F E t ^ m • ν := by rw [h1]

end GlobalTheory.ThK.LemF.QuotInv

end
