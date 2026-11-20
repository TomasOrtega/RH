import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.AdBridgeSteps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst) (hb : AdBridgeIso I)

def tf (x : I.Gf) : HA (Af I.F) I.cm.sig I.J := (splitA I.cm.sig I.J (toHA I hb (1, x))).2

def tfHom : I.Gf →* HA (Af I.F) I.cm.sig I.J :=
  (MonoidHom.snd _ _).comp ((splitA I.cm.sig I.J).comp
    ((toHA I hb : I.GA →* HAd I).comp (MonoidHom.inr _ _)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Bridge_tfHom_apply (x : I.Gf) : tfHom I hb x = tf I hb x := rfl

def swapE : I.E ⊗[I.F] Af I.F ≃ₐ[I.F] Af I.F ⊗[I.F] I.E := Algebra.TensorProduct.comm I.F I.E (Af I.F)

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `[tensMap, tauF, swapE, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add s u hs hu => rw [map_add, map_add, map_add, hs, hu]`.
-/
theorem Bridge_tens_eq (t : AF I.F ⊗[I.F] I.E) :
    tensMap (E := I.E) (sndA I.F) t = swapE I (tauF I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [tensMap, tauF, swapE, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add s u hs hu => rw [map_add, map_add, map_add, hs, hu]

variable {I} in

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem Bridge_HA_ext {R : Type} [CommRing R] [Algebra I.F R] (g h : HA R I.cm.sig I.J)
    (e : ((HA.mat R I.cm.sig I.J g : GL (Fin I.n) (R ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (R ⊗[I.F] I.E)) =
      ((HA.mat R I.cm.sig I.J h : GL (Fin I.n) (R ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (R ⊗[I.F] I.E))) :
    g = h := Subtype.ext (Units.ext e)

/- English proof (translation)
Establish `hB : I.fmat x = (hmat I (toHA I hb (1, x))).map (tauF I)` using `(hb.choose_spec (1, x)).2`. Establish `h1 : ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb x) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) = (hmat I (toHA I hb (1, x))).map (tensMap (E` using `I.E) (sndA I.F)) := rfl`. Rewrite using `[h1, hB, Matrix.map_map]`. Use extensionality with `i j`. Conclude with `Bridge_tens_eq I _`.
-/
theorem Bridge_mat (x : I.Gf) :
    ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb x) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (swapE I) := by
  have hB : I.fmat x = (hmat I (toHA I hb (1, x))).map (tauF I) := (hb.choose_spec (1, x)).2
  have h1 : ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb x) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
      (hmat I (toHA I hb (1, x))).map (tensMap (E := I.E) (sndA I.F)) := rfl
  rw [h1, hB, Matrix.map_map]
  ext i j
  exact Bridge_tens_eq I _

/- English proof (translation)
Introduce `x y hxy`. Establish `h1 : (I.fmat x).map (swapE I) = (I.fmat y).map (swapE I)`. Rewrite using `[← Bridge_mat I hb x, ← Bridge_mat I hb y, hxy]`. Establish `h2 : I.fmat x = I.fmat y`. Use extensionality with `i j`.

Conclude with `(swapE I).injective (congrFun (congrFun h1 i) j)`. Conclude with `Subtype.ext (Units.ext h2)`.
-/
theorem Bridge_tf_injective : Function.Injective (tf I hb) := by
  intro x y hxy
  have h1 : (I.fmat x).map (swapE I) = (I.fmat y).map (swapE I) := by
    rw [← Bridge_mat I hb x, ← Bridge_mat I hb y, hxy]
  have h2 : I.fmat x = I.fmat y := by
    ext i j
    exact (swapE I).injective (congrFun (congrFun h1 i) j)
  exact Subtype.ext (Units.ext h2)

/- English proof (translation)
Introduce `h`. Set `φ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F` to `(swapE I).symm.toAlgHom.toRingHom`. Establish `hσ : φ.comp (sigR (Af I.F) I.cm.sig) = (Formalism.UG.sigR I.cm.sig (Af I.F)).comp φ`. Use `RingHom.ext fun t => ?_` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a e => simp [φ, swapE, sigR, Formalism.UG.sigR]`. Consider the case `add s u hs hu => simp only [map_add] at hs hu ⊢`. Rewrite using `[hs, hu]`. Establish `hJ : (JR (Af I.F) I.J).map φ = I.J.map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := by`.

Use extensionality with `i j`. Simplify using `[φ, swapE, JR, inclR, Formalism.UG.inclE]`. Establish `hmem` using `Formalism.UG.P.bc_mem _ _ φ hσ (JR (Af I.F) I.J) (HA.mat (Af I.F) I.cm.sig I.J h) h.2`. Rewrite `hmem` using `[hJ]`. Set `x : I.Gf` to `⟨Formalism.UG.bc φ (HA.mat (Af I.F) I.cm.sig I.J h), hmem⟩`.

Use `⟨x, Bridge_HA_ext (tf I hb x) h ?_⟩` and prove the remaining obligations. Rewrite using `[Bridge_mat]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `swapE I (φ _) = _`. Use `first`.

Consider the case `exact (swapE I).apply_symm_apply _`. Consider the case `simp [φ]`.
-/
theorem Bridge_tf_surjective : Function.Surjective (tf I hb) := by
  intro h
  let φ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F := (swapE I).symm.toAlgHom.toRingHom
  have hσ : φ.comp (sigR (Af I.F) I.cm.sig) = (Formalism.UG.sigR I.cm.sig (Af I.F)).comp φ := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, swapE, sigR, Formalism.UG.sigR]
    | add s u hs hu => simp only [map_add] at hs hu ⊢; rw [hs, hu]
  have hJ : (JR (Af I.F) I.J).map φ = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    ext i j
    simp [φ, swapE, JR, inclR, Formalism.UG.inclE]
  have hmem := Formalism.UG.P.bc_mem _ _ φ hσ (JR (Af I.F) I.J) (HA.mat (Af I.F) I.cm.sig I.J h) h.2
  rw [hJ] at hmem
  let x : I.Gf := ⟨Formalism.UG.bc φ (HA.mat (Af I.F) I.cm.sig I.J h), hmem⟩
  refine ⟨x, Bridge_HA_ext (tf I hb x) h ?_⟩
  rw [Bridge_mat]
  ext i j
  change swapE I (φ _) = _
  first
    | exact (swapE I).apply_symm_apply _
    | simp [φ]

/- English proof (translation)
Establish `hF` using `adelic_compact_finite_places I (toHA I hb (1, x))`. Establish `hx : I.fmat x = ofHAFin I (toHA I hb (1, x))` using `(toHA_isBridge I hb (1, x)).2`. Establish `hK : x ∈ I.Kset ↔ ∀ y, y ∈ I.Lf ↔ ofHAFin I (toHA I hb (1, x)) *ᵥ y ∈ I.Lf`. Rewrite using `[← hx]`. Conclude with `Iff.rfl`.

Rewrite using `[hK, hF, Kf, Subgroup.mem_iInf]`. Conclude with `Iff.rfl`.
-/
theorem Bridge_mem_Kf_iff (x : I.Gf) :
    tf I hb x ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) ↔ x ∈ I.Kset := by
  have hF := adelic_compact_finite_places I (toHA I hb (1, x))
  have hx : I.fmat x = ofHAFin I (toHA I hb (1, x)) := (toHA_isBridge I hb (1, x)).2
  have hK : x ∈ I.Kset ↔ ∀ y, y ∈ I.Lf ↔ ofHAFin I (toHA I hb (1, x)) *ᵥ y ∈ I.Lf := by
    rw [← hx]; exact Iff.rfl
  rw [hK, hF, Kf, Subgroup.mem_iInf]
  exact Iff.rfl

end PI.MassDataKppVolLemmas
