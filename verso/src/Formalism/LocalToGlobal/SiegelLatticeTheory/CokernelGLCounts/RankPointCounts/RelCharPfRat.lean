import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemFlag
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin

noncomputable section

open scoped Classical ComplexConjugate
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.NonRelPf

namespace Formalism.L2.SG.Pf.RelChar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Establish `hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y`. Unfold `HermitianLatticesTheory.isom at hγ`. Conclude with `hγ`. Establish `hXa : ∀ a, (mapFlag γ hγ F).Xa a = (F.Xa a).map γ.toLinearMap`. Introduce `a`.

Unfold `FlagG.Xa`. Rewrite using `[Submodule.map_span, ← Set.image_comp]`. Both sides reduce to the same expression. Establish `hXX : (mapFlag γ hγ F).X = F.X.map γ.toLinearMap`. Unfold `FlagG.X`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Unfold `FlagG.LieN at h ⊢`. Take `⟨h0, h1, h2⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `LieU at h0 ⊢`. Simplify using `only [Set.mem_setOf_eq, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h0 ⊢`. Introduce `x y`. Use `h0 (γ.symm x) (γ.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`.

Rewrite `this` using `[← hiso (γ.symm (Y x)) (γ.symm y), ← hiso (γ.symm x) (γ.symm (Y y))]`. Simplify `this` using `only [LinearEquiv.apply_symm_apply]`. Introduce `a ha1 ha2 x hx`. Rewrite `hx`, the goal using `[hXa]`. Take `⟨x', hx', rfl⟩` from `Submodule.mem_map.1 hx`.

Conclude with `Submodule.mem_map.2 ⟨_, h1 a ha1 ha2 x' hx', by simp⟩`. Introduce `x hx`. Rewrite using `[hXX]`. Establish `hx2 : ∀ w ∈ (mapFlag γ hγ F).X, S.hT w x = 0`. Unfold `perpS at hx`.

Conclude with `hx`. Establish `hx' : γ.symm x ∈ perpS S F.X`. Unfold `perpS`. Use `show ∀ w ∈ F.X, S.hT w (γ.symm x) = 0`. Introduce `w hw`.

Rewrite using `[← hiso w (γ.symm x), LinearEquiv.apply_symm_apply]`. Conclude with `hx2 (γ w) (by rw [hXX]; exact Submodule.mem_map_of_mem hw)`. Conclude with `Submodule.mem_map.2 ⟨_, h2 _ hx', by simp⟩`.
-/
theorem lieN_map (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (Y : S.V →ₗ[E] S.V)
    (h : (γ.symm.toLinearMap ∘ₗ Y ∘ₗ γ.toLinearMap) ∈ F.LieN) : Y ∈ (mapFlag γ hγ F).LieN := by
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := by
    unfold HermitianLatticesTheory.isom at hγ
    exact hγ
  have hXa : ∀ a, (mapFlag γ hγ F).Xa a = (F.Xa a).map γ.toLinearMap := by
    intro a
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  have hXX : (mapFlag γ hγ F).X = F.X.map γ.toLinearMap := by
    unfold FlagG.X
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  unfold FlagG.LieN at h ⊢
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold LieU at h0 ⊢
    simp only [Set.mem_setOf_eq, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h0 ⊢
    intro x y
    have := h0 (γ.symm x) (γ.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [← hiso (γ.symm (Y x)) (γ.symm y), ← hiso (γ.symm x) (γ.symm (Y y))] at this
    simpa only [LinearEquiv.apply_symm_apply] using this
  · intro a ha1 ha2 x hx
    rw [hXa] at hx ⊢
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 hx
    exact Submodule.mem_map.2 ⟨_, h1 a ha1 ha2 x' hx', by simp⟩
  · intro x hx
    rw [hXX]
    have hx2 : ∀ w ∈ (mapFlag γ hγ F).X, S.hT w x = 0 := by
      unfold perpS at hx
      exact hx
    have hx' : γ.symm x ∈ perpS S F.X := by
      unfold perpS
      show ∀ w ∈ F.X, S.hT w (γ.symm x) = 0
      intro w hw
      rw [← hiso w (γ.symm x), LinearEquiv.apply_symm_apply]
      exact hx2 (γ w) (by rw [hXX]; exact Submodule.mem_map_of_mem hw)
    exact Submodule.mem_map.2 ⟨_, h2 _ hx', by simp⟩

/- English proof (translation)
Unfold `perpS`. Use `show ∀ x ∈ F.X, (S.hT x) F.z = 0`. Introduce `x hx`. Unfold `FlagG.X at hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Conclude with `F.z_orth a`. Consider the case `zero => simp`. Consider the case `add y w _ _ hy hw => simp [hy, hw]`.

Consider the case `smul c y _ hy => simp [hy]`.
-/
theorem z_mem_perp (F : FlagG S r T) : F.z ∈ perpS S F.X := by
  unfold perpS
  show ∀ x ∈ F.X, (S.hT x) F.z = 0
  intro x hx
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

/- English proof (translation)
Unfold `FlagG.LieN at hZ`. Take `⟨-, h1, h2⟩` from `hZ`. Establish `hlt` using `a.isLt`. Distinguish the cases in `ha : (a : ℕ) + 1 < r`. Establish `he : F.fvec a.succ = F.e ⟨(a : ℕ) + 1, ha⟩`.

Unfold `FlagG.fvec`. Establish `hs : a.succ = Fin.castSucc (⟨(a : ℕ) + 1, ha⟩ : Fin r)` using `Fin.ext (by simp)`. Rewrite using `[hs, Fin.snoc_castSucc]`. Rewrite using `[he]`. Establish `hx : F.e ⟨(a : ℕ) + 1, ha⟩ ∈ F.Xa ((a : ℕ) + 2)`.

Unfold `FlagG.Xa`. Conclude with `Submodule.subset_span ⟨_, show (a : ℕ) + 1 < (a : ℕ) + 2 by omega, rfl⟩`. Establish `hy` using `h1 ((a : ℕ) + 2) (by omega) (by omega) _ hx`. Unfold `FlagG.Xa at hy`. Unfold `FlagG.X`.

Conclude with `Submodule.span_mono (Set.image_subset_range _ _) hy`. Establish `he : F.fvec a.succ = F.z`. Unfold `FlagG.fvec`. Establish `hs : a.succ = Fin.last r` using `Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)`. Rewrite using `[hs, Fin.snoc_last]`.

Rewrite using `[he]`. Conclude with `h2 _ (z_mem_perp F)`.
-/
theorem lieN_fvec_mem (F : FlagG S r T) {Z : S.V →ₗ[E] S.V} (hZ : Z ∈ F.LieN) (a : Fin r) :
    Z (F.fvec a.succ) ∈ F.X := by
  unfold FlagG.LieN at hZ
  obtain ⟨-, h1, h2⟩ := hZ
  have hlt := a.isLt
  by_cases ha : (a : ℕ) + 1 < r
  · have he : F.fvec a.succ = F.e ⟨(a : ℕ) + 1, ha⟩ := by
      unfold FlagG.fvec
      have hs : a.succ = Fin.castSucc (⟨(a : ℕ) + 1, ha⟩ : Fin r) := Fin.ext (by simp)
      rw [hs, Fin.snoc_castSucc]
    rw [he]
    have hx : F.e ⟨(a : ℕ) + 1, ha⟩ ∈ F.Xa ((a : ℕ) + 2) := by
      unfold FlagG.Xa
      exact Submodule.subset_span ⟨_, show (a : ℕ) + 1 < (a : ℕ) + 2 by omega, rfl⟩
    have hy := h1 ((a : ℕ) + 2) (by omega) (by omega) _ hx
    unfold FlagG.Xa at hy
    unfold FlagG.X
    exact Submodule.span_mono (Set.image_subset_range _ _) hy
  · have he : F.fvec a.succ = F.z := by
      unfold FlagG.fvec
      have hs : a.succ = Fin.last r := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [hs, Fin.snoc_last]
    rw [he]
    exact h2 _ (z_mem_perp F)

/- English proof (translation)
Unfold `FlagG.ell`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `(hT_eq_coefX F (fd a) a (hfd a) (lieN_fvec_mem F hZ a)).symm`.
-/
theorem ell_eq_dual (F : FlagG S r T) (fd : Fin r → S.V) (hfd : ∀ a b, S.hT (fd a) (F.e b) = if b = a then 1 else 0)
    {Z : S.V →ₗ[E] S.V} (hZ : Z ∈ F.LieN) : F.ell Z = ∑ a, S.hT (fd a) (Z (F.fvec a.succ)) := by
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (hT_eq_coefX F (fd a) a (hfd a) (lieN_fvec_mem F hZ a)).symm

end Gen

section Coord

variable {D : D7} (X : HidaSetting D)

def linOfMat (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' (A.map X.ιE) ∘ₗ X.bas.equivFun.toLinearMap

/- English proof (translation)
Unfold `Formalism.L2.SG.HidaSetting.HidaSetting.crd`. Unfold `crdOf`. Use function extensionality and compare the values at `i`. Simplify using `only [← Module.Basis.equivFun_apply, linOfMat, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`. Simplify using the standard rewrite rules.
-/
theorem crd_linOfMat (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (linOfMat X A y) = A *ᵥ X.crd y := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.crd
  unfold crdOf
  funext i
  simp only [← Module.Basis.equivFun_apply, linOfMat, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  simp

/- English proof (translation)
Use `set A := Bm X * W * Bm' X with hA`. Establish `hdot : ∀ p q : Fin X.B.I.n → X.B.I.E, hE X p q = star p ⬝ᵥ (X.B.I.J *ᵥ q)`. Introduce `p q`. Simplify using `only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Both sides reduce to the same expression.

Establish `hJB : (Bm X)ᴴ * X.B.I.J = JB X * Bm' X`. Rewrite using `[JB_eq, Matrix.mul_assoc, Bm_mul_Bm', Matrix.mul_one]`. Establish `hAs : Aᴴ * X.B.I.J = -(X.B.I.J * A)`. Establish `h1 : (Bm' X)ᴴ * (Bm X)ᴴ = 1` using `by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hA]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (Bm' X)ᴴ * (Wᴴ * JB X) * Bm' X := by rw [hJB]; simp only [Matrix.mul_assoc]`. Use `_ = -((Bm' X)ᴴ * (JB X * W) * Bm' X) := by rw [hWs]; simp [Matrix.mul_neg, Matrix.neg_mul]`. Use `_ = -(((Bm' X)ᴴ * (Bm X)ᴴ) * X.B.I.J * (Bm X * W * Bm' X)) := by`.

Rewrite using `[JB_eq]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = -(X.B.I.J * A) := by rw [h1, Matrix.one_mul]`. Establish `hskew : ∀ p q, hE X (A *ᵥ p) q + hE X p (A *ᵥ q) = 0`. Introduce `p q`.

Rewrite using `[hdot, hdot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAs, Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_mulVec]`. Normalize the expressions using the abelian group laws. Establish `hXf : ∀ k, (X.Fu w).Xa k = Submodule.span D.host.E (X.eX '' {i | i.1 < k})`. Introduce `k`. Unfold `FlagG.Xa`.

Rewrite using `[X.Fu_e]`. Establish `hXs : (X.Fu w).X = Submodule.span D.host.E (X.eX '' Set.univ)`. Unfold `FlagG.X`. Rewrite using `[X.Fu_e, Set.image_univ]`. Establish `hB : ∀ a : Fin D.R.rS, Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1`.

Introduce `a`. Rewrite using `[Bm'_mulVec]`. Use function extensionality and compare the values at `k`. Rewrite using `[show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]`. Simplify using `[Pi.single_apply]`.

Establish `he : ∀ a : Fin D.R.rS, Z (X.eX a) ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1})`. Introduce `a`. Use `FlagCoordinates.crd_desc X _ _ ?_` and prove the remaining obligations. Rewrite using `[hZ, show X.crd (X.eX a) = X.eR a from rfl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB]`. Use `FlagCoordinates.Bm_mulVec_mem X _ _ fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[mulVec_single_one]`. Use `hW k _ ?_` and prove the remaining obligations. Break down `k with b | i | b` into its components or cases. Establish `: ¬ b.1 < a.1` using `fun h => hk ⟨b, h, rfl⟩`. Simplify using `only [lvk, Sum.elim_inl]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`.

Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨fun x y => ?_, fun a ha1 har x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Apply `X.ιE.symm.injective` to reduce the goal to its premises.

Rewrite using `[map_add, ← Formalism.L2.SG.NonRelPf.hE_crd X, ← Formalism.L2.SG.NonRelPf.hE_crd X, hZ, hZ, map_zero]`. Conclude with `hskew _ _`. Rewrite `hx`, the goal using `[hXf]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, hb, rfl⟩` from `hy`. Use `Submodule.span_mono ?_ (he b)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `⟨c, by simp only [Set.mem_ofPred_eq] at hb hc ⊢; omega, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hy`. Establish `hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0`.

Introduce `a`. Establish `hmem : X.eX a ∈ (X.Fu w).X`. Rewrite using `[hXs]`. Conclude with `Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩`. Rewrite using `[show X.eR a = X.crd (X.eX a) from rfl, Formalism.L2.SG.NonRelPf.hE_crd X, hx _ hmem, map_zero]`.

Rewrite using `[hXs]`. Use `FlagCoordinates.crd_desc X _ _ ?_` and prove the remaining obligations. Rewrite using `[hZ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]`. Use `FlagCoordinates.Bm_mulVec_mem X Set.univ _ fun k hk => ?_` and prove the remaining obligations. Establish `hk' : ∀ b, k ≠ Sum.inl b`.

Introduce and unpack `b rfl`. Conclude with `hk ⟨b, Set.mem_univ _, rfl⟩`. Rewrite using `[mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hlk` using `lvk_notinl X k hk'`.

Break down `j with b | i | b` into its components or cases. Rewrite using `[hW k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]`. Rewrite using `[hW k _ (by rw [lvk_w]; omega), zero_mul]`. Rewrite using `[show cE X (X.crd x) (Sum.inr (Sum.inr b)) = hE X (X.eR b) (X.crd x) from rfl, hx0 b, mul_zero]`.
-/
theorem lieN_of_coord (w : D.what₂.Word) (W : Matrix (Kap X) (Kap X) X.B.I.E) (Z : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hW : InPat (lvk X) 1 W) (hWs : Wᴴ * JB X = -(JB X * W)) (hZ : ∀ y, X.crd (Z y) = (Bm X * W * Bm' X) *ᵥ X.crd y) :
    Z ∈ (X.Fu w).LieN := by
  set A := Bm X * W * Bm' X with hA
  have hdot : ∀ p q : Fin X.B.I.n → X.B.I.E, hE X p q = star p ⬝ᵥ (X.B.I.J *ᵥ q) := by
    intro p q
    simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rfl
  have hJB : (Bm X)ᴴ * X.B.I.J = JB X * Bm' X := by
    rw [JB_eq, Matrix.mul_assoc, Bm_mul_Bm', Matrix.mul_one]
  have hAs : Aᴴ * X.B.I.J = -(X.B.I.J * A) := by
    have h1 : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
    calc Aᴴ * X.B.I.J = (Bm' X)ᴴ * (Wᴴ * ((Bm X)ᴴ * X.B.I.J)) := by
          rw [hA]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bm' X)ᴴ * (Wᴴ * JB X) * Bm' X := by rw [hJB]; simp only [Matrix.mul_assoc]
      _ = -((Bm' X)ᴴ * (JB X * W) * Bm' X) := by rw [hWs]; simp [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(((Bm' X)ᴴ * (Bm X)ᴴ) * X.B.I.J * (Bm X * W * Bm' X)) := by
          rw [JB_eq]; simp only [Matrix.mul_assoc]
      _ = -(X.B.I.J * A) := by rw [h1, Matrix.one_mul]
  have hskew : ∀ p q, hE X (A *ᵥ p) q + hE X p (A *ᵥ q) = 0 := by
    intro p q
    rw [hdot, hdot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAs,
      Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_mulVec]
    abel
  have hXf : ∀ k, (X.Fu w).Xa k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k; unfold FlagG.Xa; rw [X.Fu_e]
  have hXs : (X.Fu w).X = Submodule.span D.host.E (X.eX '' Set.univ) := by
    unfold FlagG.X; rw [X.Fu_e, Set.image_univ]
  have hB : ∀ a : Fin D.R.rS, Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1 := by
    intro a
    rw [Bm'_mulVec]
    funext k
    rw [show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]
    simp [Pi.single_apply]
  have he : ∀ a : Fin D.R.rS, Z (X.eX a) ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
    intro a
    refine FlagCoordinates.crd_desc X _ _ ?_
    rw [hZ, show X.crd (X.eX a) = X.eR a from rfl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB]
    refine FlagCoordinates.Bm_mulVec_mem X _ _ fun k hk => ?_
    rw [mulVec_single_one]
    refine hW k _ ?_
    rcases k with b | i | b
    · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
      simp only [lvk, Sum.elim_inl]; omega
    · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
    · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega
  refine ⟨fun x y => ?_, fun a ha1 har x hx => ?_, fun x hx => ?_⟩
  · apply X.ιE.symm.injective
    rw [map_add, ← Formalism.L2.SG.NonRelPf.hE_crd X, ← Formalism.L2.SG.NonRelPf.hE_crd X, hZ, hZ, map_zero]
    exact hskew _ _
  · rw [hXf] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      refine Submodule.span_mono ?_ (he b)
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, by simp only [Set.mem_ofPred_eq] at hb hc ⊢; omega, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  · have hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0 := by
      intro a
      have hmem : X.eX a ∈ (X.Fu w).X := by
        rw [hXs]; exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
      rw [show X.eR a = X.crd (X.eX a) from rfl, Formalism.L2.SG.NonRelPf.hE_crd X, hx _ hmem, map_zero]
    rw [hXs]
    refine FlagCoordinates.crd_desc X _ _ ?_
    rw [hZ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]
    refine FlagCoordinates.Bm_mulVec_mem X Set.univ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, Set.mem_univ _, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hW k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hW k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [show cE X (X.crd x) (Sum.inr (Sum.inr b)) = hE X (X.eR b) (X.crd x) from rfl, hx0 b, mul_zero]

/- English proof (translation)
Rewrite using `[Φ_sum]`. Unfold `lamU`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hM : (X.B.I.P v)⁻¹ * (Bm X * W * Bm' X).map (X.B.I.φ v) * X.B.I.P v = Bv X v * W.map (X.B.I.φ v) * Bv' X v`. Unfold `Bv Bv'`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hn : rv X.B.I v (X.crd (nxt X.eX (X.zu w) a)) = nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a`. Rewrite using `[nxt_map (fun y => rv X.B.I v (X.crd y))]`. Both sides reduce to the same expression.

Use `show X.B.I.φ v (X.ιE.symm ((VS D).hT (X.fY a) (Z (nxt X.eX (X.zu w) a)))) = _`. Rewrite using `[← Formalism.L2.SG.NonRelPf.hE_crd X, ← Formalism.L2.SG.Pf.Level.hJ_rv, hZ, ← Formalism.L2.SG.Pf.Level.rv_mulVec, hM, hn]`. Both sides reduce to the same expression.
-/
theorem ell_coord (w : D.what₂.Word) (W : Matrix (Kap X) (Kap X) X.B.I.E) (Z : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hZ : ∀ y, X.crd (Z y) = (Bm X * W * Bm' X) *ᵥ X.crd y) (v : InfinitePlace X.B.I.F) :
    Φ X v (∑ a, (VS D).hT (X.fY a) (Z (nxt X.eX (X.zu w) a))) = lamU X w v (W.map (X.B.I.φ v)) := by
  rw [Φ_sum]
  unfold lamU
  refine Finset.sum_congr rfl fun a _ => ?_
  have hM : (X.B.I.P v)⁻¹ * (Bm X * W * Bm' X).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * W.map (X.B.I.φ v) * Bv' X v := by
    unfold Bv Bv'
    rw [Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hn : rv X.B.I v (X.crd (nxt X.eX (X.zu w) a)) =
      nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a := by
    rw [nxt_map (fun y => rv X.B.I v (X.crd y))]; rfl
  show X.B.I.φ v (X.ιE.symm ((VS D).hT (X.fY a) (Z (nxt X.eX (X.zu w) a)))) = _
  rw [← Formalism.L2.SG.NonRelPf.hE_crd X, ← Formalism.L2.SG.Pf.Level.hJ_rv, hZ, ← Formalism.L2.SG.Pf.Level.rv_mulVec, hM, hn]
  rfl

end Coord

/- English proof (translation)
Introduce `D X Yf u u' t ht M hMU hMc Y hY1 hYc hYs v`. Establish `hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Establish `hisoF : ∀ a b, (VS D).hT (t.lin a) (t.lin b) = (VS D).hT a b` using `hiso`. Use `set F' := mapFlag t.lin hiso (X.Fu u') with hF'`. Establish `hfr : t.frame = ⟨F', t.lin (X.Fu u').z⟩`.

Unfold `GTerm.frame mapLF`. Rewrite using `[dif_pos hiso]`. Both sides reduce to the same expression. Establish `hRF` using `(Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam ((Yf.rowsOK u).1 t.lam t.mem)).2.2.1`. Establish `hrel0` using `(TermDef.isRel_mk D.host.F hRF ⟨t.frame, t.rep.2.2.2.2⟩).1 ht`.

Establish `hrel : Relevant D.host.F (X.Fu u) F'`. Establish `e : t.frame.fl = F'` using `by rw [hfr]`. Rewrite using `[← e]`. Conclude with `hrel0`. Use `set A := Bm X * Y * Bm' X with hA`.

Use `set Yp := Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _) with hYp`. Set `Z1` to `linOfMat X A`. Establish `hZ1 : ∀ y, X.crd (Z1 y) = A *ᵥ X.crd y` using `crd_linOfMat X A`. Set `Z2` to `t.lin.symm.toLinearMap ∘ₗ Z1 ∘ₗ t.lin.toLinearMap`. Establish `hcrdinv : ∀ w, X.crd (t.lin.symm w) = (↑M⁻¹ : Matrix _ _ _) *ᵥ X.crd w`.

Introduce `w`. Establish `h` using `hMc (t.lin.symm w)`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[h, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `hconj : (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * A * (M : Matrix _ _ _) = Bm X * Yp * Bm' X`.

Rewrite using `[hA, hYp]`. Unfold `Gr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Establish `hZ2 : ∀ y, X.crd (Z2 y) = (Bm X * Yp * Bm' X) *ᵥ X.crd y`. Introduce `y`. Use `show X.crd (t.lin.symm (Z1 (t.lin y))) = _`. Rewrite using `[hcrdinv, hZ1, hMc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj, hA]`. Establish `hYps : Ypᴴ * JB X = -(JB X * Yp)` using `(memConjOf_holds D X M hMU).2.1 Y hYs`.

Establish `hL1 : Z1 ∈ (X.Fu u).LieN` using `lieN_of_coord X u Y Z1 hY1 hYs hZ1`. Establish `hL2 : Z2 ∈ (X.Fu u').LieN` using `lieN_of_coord X u' Yp Z2 hYc hYps hZ2`. Establish `hL3 : Z1 ∈ F'.LieN` using `lieN_map t.lin hiso (X.Fu u') Z1 hL2`. Establish `htr` using `hrel Z1 ⟨hL1, hL3⟩`. Unfold `FlagG.dpsi at htr`.

Establish `hl1 : (X.Fu u).ell Z1 = ∑ a, (VS D).hT (X.fY a) (Z1 (nxt X.eX (X.zu u) a))`. Rewrite using `[ell_eq_dual (X.Fu u) X.fY (fun a b => by rw [X.Fu_e]; exact hTfe X a b) hL1]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[fvec_succ, X.Fu_e, X.flagZVector]`. Establish `hl2 : F'.ell Z1 = ∑ a, (VS D).hT (X.fY a) (Z2 (nxt X.eX (X.zu u') a))`.

Rewrite using `[ell_eq_dual F' (fun a => t.lin (X.fY a)) (fun a b => by show (VS D).hT (t.lin (X.fY a)) (t.lin ((X.Fu u').e b)) = _`. Rewrite using `[hisoF, X.Fu_e]`. Conclude with `hTfe X a b) hL3]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `e1 : F'.fvec a.succ = t.lin (nxt X.eX (X.zu u') a)`.

Rewrite using `[fvec_succ, nxt_map t.lin, hF']`. Simplify using `only [mapFlag, X.Fu_e, X.flagZVector]`. Rewrite using `[e1, ← hisoF (X.fY a)]`. Use `congr 1`. Conclude with `(LinearEquiv.apply_symm_apply t.lin _).symm`.

Establish `hΦ1` using `ell_coord X u Y Z1 hZ1 v`. Establish `hΦ2` using `ell_coord X u' Yp Z2 hZ2 v`. Rewrite `hΦ1` using `[← hl1]`. Rewrite `hΦ2` using `[← hl2]`. Establish `hcm` using `Formalism.BasicNotions.Examples₂.cmData D.host`.

Establish `ht1` using `Formalism.MainNotions.BridgeLemma.tie_trace hcm ((X.Fu u).ell Z1)`. Establish `ht2` using `Formalism.MainNotions.BridgeLemma.tie_trace hcm (F'.ell Z1)`. Rewrite `ht1` using `[htr, ht2]`. Establish `hΦe` using `congrArg (Φ X v) ht1`. Rewrite `hΦe` using `[Φ_add, Φ_add, Φ_star, Φ_star, hΦ1, hΦ2, re_add_star, re_add_star]`.

Use `Complex.ofReal_injective hΦe` as an intermediate fact. Rewrite using `[Complex.sub_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ratVanish_holds : RatVanish := by
  intro D X Yf u u' t ht M hMU hMc Y hY1 hYc hYs v
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hisoF : ∀ a b, (VS D).hT (t.lin a) (t.lin b) = (VS D).hT a b := hiso
  set F' := mapFlag t.lin hiso (X.Fu u') with hF'
  have hfr : t.frame = ⟨F', t.lin (X.Fu u').z⟩ := by
    unfold GTerm.frame mapLF; rw [dif_pos hiso]; rfl
  have hRF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam ((Yf.rowsOK u).1 t.lam t.mem)).2.2.1
  have hrel0 := (TermDef.isRel_mk D.host.F hRF ⟨t.frame, t.rep.2.2.2.2⟩).1 ht
  have hrel : Relevant D.host.F (X.Fu u) F' := by
    have e : t.frame.fl = F' := by rw [hfr]
    rw [← e]; exact hrel0

  set A := Bm X * Y * Bm' X with hA
  set Yp := Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _) with hYp
  let Z1 := linOfMat X A
  have hZ1 : ∀ y, X.crd (Z1 y) = A *ᵥ X.crd y := crd_linOfMat X A
  let Z2 := t.lin.symm.toLinearMap ∘ₗ Z1 ∘ₗ t.lin.toLinearMap
  have hcrdinv : ∀ w, X.crd (t.lin.symm w) = (↑M⁻¹ : Matrix _ _ _) *ᵥ X.crd w := by
    intro w
    have h := hMc (t.lin.symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hconj : (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * A * (M : Matrix _ _ _) = Bm X * Yp * Bm' X := by
    rw [hA, hYp]
    unfold Gr
    calc (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * (Bm X * Y * Bm' X) * (M : Matrix _ _ _)
        = (Bm X * Bm' X) * (↑M⁻¹ : Matrix _ _ _) * (Bm X * Y * Bm' X) * (M : Matrix _ _ _) * (Bm X * Bm' X) := by
          rw [Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hZ2 : ∀ y, X.crd (Z2 y) = (Bm X * Yp * Bm' X) *ᵥ X.crd y := by
    intro y
    show X.crd (t.lin.symm (Z1 (t.lin y))) = _
    rw [hcrdinv, hZ1, hMc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj, hA]
  have hYps : Ypᴴ * JB X = -(JB X * Yp) := (memConjOf_holds D X M hMU).2.1 Y hYs
  have hL1 : Z1 ∈ (X.Fu u).LieN := lieN_of_coord X u Y Z1 hY1 hYs hZ1
  have hL2 : Z2 ∈ (X.Fu u').LieN := lieN_of_coord X u' Yp Z2 hYc hYps hZ2
  have hL3 : Z1 ∈ F'.LieN := lieN_map t.lin hiso (X.Fu u') Z1 hL2
  have htr := hrel Z1 ⟨hL1, hL3⟩
  unfold FlagG.dpsi at htr

  have hl1 : (X.Fu u).ell Z1 = ∑ a, (VS D).hT (X.fY a) (Z1 (nxt X.eX (X.zu u) a)) := by
    rw [ell_eq_dual (X.Fu u) X.fY (fun a b => by rw [X.Fu_e]; exact hTfe X a b) hL1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fvec_succ, X.Fu_e, X.flagZVector]
  have hl2 : F'.ell Z1 = ∑ a, (VS D).hT (X.fY a) (Z2 (nxt X.eX (X.zu u') a)) := by
    rw [ell_eq_dual F' (fun a => t.lin (X.fY a))
      (fun a b => by
        show (VS D).hT (t.lin (X.fY a)) (t.lin ((X.Fu u').e b)) = _
        rw [hisoF, X.Fu_e]; exact hTfe X a b) hL3]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e1 : F'.fvec a.succ = t.lin (nxt X.eX (X.zu u') a) := by
      rw [fvec_succ, nxt_map t.lin, hF']
      simp only [mapFlag, X.Fu_e, X.flagZVector]
    rw [e1, ← hisoF (X.fY a)]
    congr 1
    exact (LinearEquiv.apply_symm_apply t.lin _).symm
  have hΦ1 := ell_coord X u Y Z1 hZ1 v
  have hΦ2 := ell_coord X u' Yp Z2 hZ2 v
  rw [← hl1] at hΦ1
  rw [← hl2] at hΦ2

  have hcm := Formalism.BasicNotions.Examples₂.cmData D.host
  have ht1 := Formalism.MainNotions.BridgeLemma.tie_trace hcm ((X.Fu u).ell Z1)
  have ht2 := Formalism.MainNotions.BridgeLemma.tie_trace hcm (F'.ell Z1)
  rw [htr, ht2] at ht1
  have hΦe := congrArg (Φ X v) ht1
  rw [Φ_add, Φ_add, Φ_star, Φ_star, hΦ1, hΦ2, re_add_star, re_add_star] at hΦe
  have := Complex.ofReal_injective hΦe
  rw [Complex.sub_re]
  linarith

/- English proof (translation)
The claim follows from `relCharC_of_rat ratVanish_holds`.
-/
theorem relCharC_holds : RelCharC := relCharC_of_rat ratVanish_holds

end Formalism.L2.SG.Pf.RelChar
