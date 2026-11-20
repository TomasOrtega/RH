import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassClEqSum
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField IsDedekindDomain

namespace Formalism.L2.SG.RhoPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.PoincareInHH.PoincareSetting

section General

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA ↔ Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ`. Establish `key : Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = (Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A)).map φ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul, hσ]`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Introduce `h`. Conclude with `Matrix.map_injective φ.injective h`.
-/
theorem uj_map_iff {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A ≃+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) :
    g ∈ Formalism.UG.UJ σA JA ↔ Units.mapEquiv φ.mapMatrix.toMulEquiv g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  change Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA ↔
    Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have key : Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ =
      (Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul, hσ]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Matrix.map_injective φ.injective h

end General

section Comm

variable (I : Formalism.MainNotions.S.AutInst)

abbrev cE : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃ₐ[I.F] Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E :=
  Algebra.TensorProduct.comm I.F I.E (Formalism.MainNotions.S.Af I.F)

def psi0 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ≃* GL (Fin I.n) (Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E) :=
  Units.mapEquiv (cE I).toRingEquiv.mapMatrix.toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_psi0_eq_map_cE (g : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    ((psi0 I g : GL (Fin I.n) (Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).map (cE I) := rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`.
-/
theorem c_sig (t : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    cE I (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) t) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.S.Af I.F) I.cm.sig (cE I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Simplify using `[Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
theorem c_inclE (x : I.E) : cE I (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af I.F) x := by
  simp [Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Establish `h` using `uj_map_iff (cE I).toRingEquiv (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.S.Af I.F) I.cm.sig) (fun a => c_sig I a) (I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotio …`. Establish `hJ : (I.J.map (Formalism.UG.inclE (F` using `I.F) (Formalism.MainNotions.S.Af I.F))).map (cE I).toRingEquiv = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.S.Af I.F) I.J := by`. Use extensionality with `i j`. Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, c_inclE]`. Rewrite `h` using `[hJ]`.

Conclude with `h`.
-/
theorem mem_upts_iff (g : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) ↔ psi0 I g ∈ HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := by
  have h := uj_map_iff (cE I).toRingEquiv (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F))
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.S.Af I.F) I.cm.sig) (fun a => c_sig I a)
    (I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) g
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))).map (cE I).toRingEquiv =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.S.Af I.F) I.J := by
    ext i j
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, c_inclE]
  rw [hJ] at h
  exact h

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `(mem_upts_iff I g).1 hg`. Introduce `hx`.

Use `⟨(psi0 I).symm x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(mem_upts_iff I _).2 (by rw [MulEquiv.apply_symm_apply]; exact hx)`. Simplify using the standard rewrite rules.
-/
theorem upts_map : (Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F)).map (psi0 I).toMonoidHom =
    HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_upts_iff I g).1 hg
  · intro hx
    refine ⟨(psi0 I).symm x, ?_, ?_⟩
    · exact (mem_upts_iff I _).2 (by rw [MulEquiv.apply_symm_apply]; exact hx)
    · simp

def psiR : I.Gf ≃* ↥(HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J) :=
  (MulEquiv.subgroupMap (psi0 I) (Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F))).trans
    (MulEquiv.subgroupCongr (upts_map I))

def psi1 : I.Gf ≃* HA (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := psiR I

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adelic_action_matrix (x : I.Gf) : HA.mat _ _ _ (psi1 I x) = psi0 I x := rfl

end Comm

section KBridge

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[tauF_tmul]`. Use `first`.

Consider the case `rfl`. Consider the case `simp only [prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, cE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.snd_apply, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`.
-/
theorem prF_eq (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) : prF I t = cE I (tauF I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    first
    | rfl
    | simp only [prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, cE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.snd_apply, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Take `⟨e, he⟩` from `Formalism.L2.SG.Closed.AdBridgeIso_holds I`. Establish `hfin : I.fmat x = ofHAFin I (e (1, x))` using `(he (1, x)).2`. Establish `key` using `adelic_compact_finite_places I (e (1, x))`. Establish `hm : Formalism.UG.bc (prF I) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J (e (1, x))) = psi0 I x`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[coe_psi0_eq_map_cE]`. Use `show _ = (I.fmat x).map (cE I)`. Rewrite using `[hfin]`. Simplify using `only [ofHAFin, Matrix.map_map]`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.bc, prF_eq]`. Rewrite using `[← hm, ← key, ← hfin]`. Conclude with `Iff.rfl`.
-/
theorem kset_iff (x : I.Gf) : x ∈ I.Kset ↔
    ∀ v : HeightOneSpectrum (𝓞 I.F), compV v (psi0 I x) ∈ Kloc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨e, he⟩ := Formalism.L2.SG.Closed.AdBridgeIso_holds I
  have hfin : I.fmat x = ofHAFin I (e (1, x)) := (he (1, x)).2
  have key := adelic_compact_finite_places I (e (1, x))
  have hm : Formalism.UG.bc (prF I)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J (e (1, x))) = psi0 I x := by
    apply Units.ext
    rw [coe_psi0_eq_map_cE]
    show _ = (I.fmat x).map (cE I)
    rw [hfin]
    simp only [ofHAFin, Matrix.map_map]
    ext i j
    simp [Formalism.UG.bc, prF_eq]
  rw [← hm, ← key, ← hfin]
  exact Iff.rfl

end KBridge

section OnX

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, Formalism.L2.SG.HidaSetting.incl, c_inclE]`.
-/
theorem ratV_eq (y : Fin X.B.I.n → X.B.I.E) :
    ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y = fun i => cE X.B.I (incl X.B.I y i) := by
  funext i
  simp [ratV, Formalism.L2.SG.HidaSetting.incl, c_inclE]

/- English proof (translation)
Rewrite using `[ratV_eq]`. Use function extensionality and compare the values at `i`. Simplify using `only [lin, Matrix.mulVecLin_apply, adelic_action_matrix, coe_psi0_eq_map_cE]`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem linear_adelic_action (x : X.B.I.Gf) (y : Fin X.B.I.n → X.B.I.E) :
    lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x) (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      fun i => cE X.B.I ((X.B.I.fmat x *ᵥ incl X.B.I y) i) := by
  rw [ratV_eq]
  funext i
  simp only [lin, Matrix.mulVecLin_apply, adelic_action_matrix, coe_psi0_eq_map_cE]
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Rewrite using `[linear_adelic_action, ratV_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i`. Conclude with `(cE X.B.I).injective (congrFun h i)`.

Introduce `h`. Rewrite using `[h]`.
-/
theorem linear_adelic_action_fixed_iff (x : X.B.I.Gf) (y : Fin X.B.I.n → X.B.I.E) :
    lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x) (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y ↔ X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y := by
  rw [linear_adelic_action, ratV_eq]
  constructor
  · intro h
    funext i
    exact (cE X.B.I).injective (congrFun h i)
  · intro h
    rw [h]

/- English proof (translation)
Proceed by induction on `b using Fin.addCases with`. Consider the case `left c`. Proceed by induction on `c using Fin.lastCases with`. Consider the case `last`. Simplify using `[tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]`.

Consider the case `cast d`. Simplify using `[tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]`. Consider the case `right c`. Simplify using `[tupH, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]`.
-/
theorem tupH_mem (b : Fin (D.R.rS + 1 + D.R.rS)) : tupH (frameOf X u) b ∈ fixSet X u := by
  induction b using Fin.addCases with
  | left c =>
    induction c using Fin.lastCases with
    | last =>
      simp [tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]
    | cast d =>
      simp [tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]
  | right c =>
    simp [tupH, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]

/- English proof (translation)
Simplify using `only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy`. Break down `hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl` into its components or cases. Conclude with `⟨Fin.castAdd _ (Fin.castSucc a), by`. Simplify using `[tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩`. Conclude with `⟨Fin.natAdd _ a, by`.

Simplify using `[tupH, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩`. Conclude with `⟨Fin.castAdd _ (Fin.last _), by`. Simplify using `[tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩`.
-/
theorem mem_tupH (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    ∃ b, tupH (frameOf X u) b = y := by
  simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl
  · exact ⟨Fin.castAdd _ (Fin.castSucc a), by
      simp [tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩
  · exact ⟨Fin.natAdd _ a, by
      simp [tupH, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩
  · exact ⟨Fin.castAdd _ (Fin.last _), by
      simp [tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩

/- English proof (translation)
Establish `hs : psi1 X.B.I x ∈ Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔ ∀ b, lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x) (ratV (F` using `X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b)) = ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b) := by first`. Consider the case `exact mem_stabT _ _ _ _ _`. Consider the case `exact mem_stabT _ _`. Consider the case `simp only [Hsub, mem_stabT]`. Rewrite using `[hs]`.

Simplify using `only [linear_adelic_action_fixed_iff]`. Express the relevant statement in the definitionally equal form `(∀ y ∈ fixSet X u, _) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hx b`. Conclude with `hx _ (tupH_mem X u b)`.

Introduce `hx y hy`. Take `⟨b, rfl⟩` from `mem_tupH X u y hy`. Conclude with `hx b`.
-/
theorem mem_hsub_iff (x : X.B.I.Gf) :
    x ∈ Hfin X u ↔ psi1 X.B.I x ∈ Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  have hs : psi1 X.B.I x ∈ Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      ∀ b, lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x)
          (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b)) =
        ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b) := by
    first
    | exact mem_stabT _ _ _ _ _
    | exact mem_stabT _ _
    | simp only [Hsub, mem_stabT]
  rw [hs]
  simp only [linear_adelic_action_fixed_iff]
  change (∀ y ∈ fixSet X u, _) ↔ _
  constructor
  · intro hx b
    exact hx _ (tupH_mem X u b)
  · intro hx y hy
    obtain ⟨b, rfl⟩ := mem_tupH X u y hy
    exact hx b

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_hsub_iff X u x).1 hx`. Introduce `hy`.

Use `⟨(psi1 X.B.I).symm y, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(mem_hsub_iff X u _).2 (by rw [MulEquiv.apply_symm_apply]; exact hy)`. Simplify using the standard rewrite rules.
-/
theorem hfin_map : (Hfin X u).map (psi1 X.B.I).toMonoidHom =
    Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_hsub_iff X u x).1 hx
  · intro hy
    refine ⟨(psi1 X.B.I).symm y, ?_, ?_⟩
    · exact (mem_hsub_iff X u _).2 (by rw [MulEquiv.apply_symm_apply]; exact hy)
    · simp

def psiH : Hfin X u ≃* ↥(Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (MulEquiv.subgroupMap (psi1 X.B.I) (Hfin X u)).trans (MulEquiv.subgroupCongr (hfin_map X u))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiH_val (h : Hfin X u) :
    ((psiH X u h : ↥(Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      HA (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) = psi1 X.B.I h := rfl

def gamR : Subgroup (Hfin X u) :=
  ((HFinIn (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)).subgroupOf
    (Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).comap (psiH X u).toMonoidHom

def kR : Subgroup (Hfin X u) :=
  ((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
    (Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).comap (psiH X u).toMonoidHom

/- English proof (translation)
Conclude with `(massCl_comap (psiH X u) _ _).symm`.
-/
theorem massH_eq : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) =
    massCl (gamR X u) (kR X u) := by
  exact (massCl_comap (psiH X u) _ _).symm

/- English proof (translation)
Establish `hsig : ((X.B.I.cm.sig : X.B.I.E →ₐ[X.B.I.F] X.B.I.E) : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E` using `RingHom.ext fun _ => rfl`. Establish `e1 : h ∈ gamR X u ↔ psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J` using `by first`. Consider the case `exact Iff.rfl`. Consider the case `(simp only [gamR, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf, psiH_val, HFinIn]; exact Iff.rfl)`. Establish `e2 : psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J ↔ ∃ M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J, Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryT …`.

Rewrite using `[← hsig]`. Conclude with `Iff.rfl`. Establish `hmap : ∀ N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, (N.map (Formalism.UG.inclE (F` using `X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))).map (cE X.B.I) = N.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) := by`. Introduce `N`. Use extensionality with `i j`.

Simplify using `[c_inclE]`. Rewrite using `[e1, e2]`. Use `exists_congr fun M => and_congr_right fun _ => ?_` and prove the remaining obligations. Establish `hbc : ((Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) M : GL (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[ …` using `rfl`. Rewrite using `[Units.ext_iff, hbc, coe_psi0_eq_map_cE, ← hmap]`.

Prove the components needed by the constructor for the conclusion. Introduce `hM`. Conclude with `(Matrix.map_injective (cE X.B.I).injective hM).symm`. Introduce `hM`. Conclude with `congrArg (fun N => N.map (cE X.B.I)) hM.symm`.
-/
theorem mem_gamR_iff (h : Hfin X u) : h ∈ gamR X u ↔
    ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (h : X.B.I.Gf) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) := by
  have hsig : ((X.B.I.cm.sig : X.B.I.E →ₐ[X.B.I.F] X.B.I.E) : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E :=
    RingHom.ext fun _ => rfl
  have e1 : h ∈ gamR X u ↔
      psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈
        HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J := by
    first
    | exact Iff.rfl
    | (simp only [gamR, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf, psiH_val,
        HFinIn]; exact Iff.rfl)
  have e2 : psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈
        HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J ↔
      ∃ M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J,
        Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) M =
          psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) := by
    rw [← hsig]
    exact Iff.rfl
  have hmap : ∀ N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E,
      (N.map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))).map (cE X.B.I) =
        N.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) := by
    intro N
    ext i j
    simp [c_inclE]
  rw [e1, e2]
  refine exists_congr fun M => and_congr_right fun _ => ?_
  have hbc : ((Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) M :
      GL (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) := rfl
  rw [Units.ext_iff, hbc, coe_psi0_eq_map_cE, ← hmap]
  constructor
  · intro hM
    exact (Matrix.map_injective (cE X.B.I).injective hM).symm
  · intro hM
    exact congrArg (fun N => N.map (cE X.B.I)) hM.symm

/- English proof (translation)
Rewrite using `[kset_iff]`. Use `first`. Consider the case `exact Iff.rfl`. Consider the case `(simp only [kR, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Kf, Subgroup.mem_iInf]; exact Iff.rfl)`.
-/
theorem mem_kR_iff (h : Hfin X u) : h ∈ kR X u ↔ (h : X.B.I.Gf) ∈ X.B.I.Kset := by
  rw [kset_iff]
  first
  | exact Iff.rfl
  | (simp only [kR, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Kf, Subgroup.mem_iInf]; exact Iff.rfl)

end OnX

end Formalism.L2.SG.RhoPf
