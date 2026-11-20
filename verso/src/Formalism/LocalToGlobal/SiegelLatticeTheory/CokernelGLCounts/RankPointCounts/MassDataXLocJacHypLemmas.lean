import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLocJacHyp
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.LocVol.LJP

/- English proof (translation)
Apply `X.ιE.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y]`. Both sides reduce to the same expression.
-/
theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas x) (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y]
  rfl

/- English proof (translation)
Introduce `D X w v`. Establish `hze : ∀ a, (VS D).hT (X.zu w) (X.eX a) = 0`. Introduce `a`. Establish `h` using `(VS D).herm.eq (X.eX a) (X.zu w)`. Rewrite `h` using `[(X.zu_orth w a).1]`.

Simplify using `using h.symm`. Use extensionality with `a b`. Simplify using `only [TFv, Matrix.map_apply, Matrix.diagonal_apply, gramE]`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, hE_crdOf, X.zu_norm, Tw]`. Consider the case `cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, hze, Ne.symm (Fin.castSucc_ne_last j)]`. Consider the case `cast i`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, (X.zu_orth w i).1, Fin.castSucc_ne_last]`. Consider the case `cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_castSucc, hE_crdOf, X.ee, Fin.castSucc_ne_last]`.
-/
theorem diag : DiagProp := by
  intro D X w v
  have hze : ∀ a, (VS D).hT (X.zu w) (X.eX a) = 0 := by
    intro a
    have h := (VS D).herm.eq (X.eX a) (X.zu w)
    rw [(X.zu_orth w a).1] at h
    simpa using h.symm
  ext a b
  simp only [TFv, Matrix.map_apply, Matrix.diagonal_apply, gramE]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, hE_crdOf, X.zu_norm, Tw]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, hze, Ne.symm (Fin.castSucc_ne_last j)]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, (X.zu_orth w i).1, Fin.castSucc_ne_last]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_castSucc, hE_crdOf, X.ee, Fin.castSucc_ne_last]

/- English proof (translation)
Introduce `D X w v`. Rewrite using `[diag X w v]`. Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using `only [Matrix.diagonal_apply_eq]`. Apply the tactic sequence `split_ifs <;> simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`. Simplify using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]`.
-/
theorem herm : HermProp := by
  intro D X w v
  rw [diag X w v]
  intro a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

/- English proof (translation)
Introduce `D X u u' v _ hdiv i j`. Rewrite using `[diag X u' v, diag X u v]`. Distinguish the cases in `h : i = j ∧ i = Fin.last D.R.rS`. Take `⟨rfl, rfl⟩` from `h`. Take `⟨k, hk⟩` from `hdiv`.

Simplify using `only [Matrix.diagonal_apply_eq, if_true]`. Use `letI : CharZero (Fv X.B.I.F v) := charZero_of_injective_algebraMap (algebraMap X.B.I.F (Fv X.B.I.F v)).injective`. Establish `hg : ((gAt X v : ℕ) : Fv X.B.I.F v) ≠ 0` using `Nat.cast_ne_zero.2 (gAt_prime X v).ne_zero`. Establish `hA : ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) = ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (k : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)`. Use `congrArg (Int.cast : ℤ → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) hk` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hs : ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * sc (E` using `X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = 1 := by`. Rewrite using `[show sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (B := X.B.I.E) ((gAt X v : Fv X.B.I.F v))⁻¹ from rfl, ← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (A := Fv X.B.I.F v) (B := X.B.I.E)), ← map …`. Establish `e1 : (-((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) * sc (E` using `X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = inclR (Fv X.B.I.F v) ((k : 𝓞 X.B.I.E) : X.B.I.E) := by`.

Rewrite using `[show -((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) = ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) by ring, hA, mul_comm ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), mul …`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Unfold `OEv`. Conclude with `Submodule.subset_span ⟨(k : 𝓞 X.B.I.E), Set.mem_univ _, rfl⟩`.

Establish `h0 : ∀ d : Fin (D.R.rS + 1) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, (∀ l, l ≠ Fin.last D.R.rS → d l = 0) → Matrix.diagonal d i j = 0`. Introduce `d hd`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`.

Conclude with `hd _ (fun h' => h ⟨rfl, h'⟩)`. Conclude with `Matrix.diagonal_apply_ne _ hij`. Rewrite using `[h0 _ (fun l hl => if_neg hl), h0 _ (fun l hl => if_neg hl), sub_zero, zero_mul]`. Unfold `OEv`. Conclude with `Submodule.zero_mem _`.
-/
theorem integral : IntProp := by
  intro D X u u' v _ hdiv i j
  rw [diag X u' v, diag X u v]
  by_cases h : i = j ∧ i = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, hk⟩ := hdiv
    simp only [Matrix.diagonal_apply_eq, if_true]
    letI : CharZero (Fv X.B.I.F v) := charZero_of_injective_algebraMap (algebraMap X.B.I.F (Fv X.B.I.F v)).injective
    have hg : ((gAt X v : ℕ) : Fv X.B.I.F v) ≠ 0 := Nat.cast_ne_zero.2 (gAt_prime X v).ne_zero
    have hA : ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
        ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (k : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
      have := congrArg (Int.cast : ℤ → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) hk
      push_cast at this
      exact this
    have hs : ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = 1 := by
      rw [show sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ =
          Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (B := X.B.I.E) ((gAt X v : Fv X.B.I.F v))⁻¹ from rfl,
        ← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (A := Fv X.B.I.F v) (B := X.B.I.E)),
        ← map_mul, mul_inv_cancel₀ hg, map_one]
    have e1 : (-((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = inclR (Fv X.B.I.F v) ((k : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [show -((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
          ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) by ring,
        hA, mul_comm ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), mul_assoc, hs, mul_one]
      simp
    rw [e1]
    unfold OEv
    exact Submodule.subset_span ⟨(k : 𝓞 X.B.I.E), Set.mem_univ _, rfl⟩
  · have h0 : ∀ d : Fin (D.R.rS + 1) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, (∀ l, l ≠ Fin.last D.R.rS → d l = 0) →
        Matrix.diagonal d i j = 0 := by
      intro d hd
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]; exact hd _ (fun h' => h ⟨rfl, h'⟩)
      · exact Matrix.diagonal_apply_ne _ hij
    rw [h0 _ (fun l hl => if_neg hl), h0 _ (fun l hl => if_neg hl), sub_zero, zero_mul]
    unfold OEv
    exact Submodule.zero_mem _

end Formalism.L2.SG.LocVol.LJP
