import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.AbsIrrOfAlgClosed

/- English proof (translation)
Use `letI : Algebra k L := f.toAlgebra`. Use `set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ`. Set `r : Γ → Module.End k W` to `fun g => (τ g).restrict (hW g)`. Establish `hr1 : r 1 = 1`. Use extensionality with `v`.

Simplify using `[r]`. Establish `hrm : ∀ g h, r (g * h) = r g * r h`. Introduce `g h`. Use extensionality with `v`. Simplify using `[r]`.

Set `d` to `Module.finrank k W`. Set `e : W ≃ₗ[k] (Fin d → k)` to `(Module.finBasis k W).equivFun`. Set `φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k` to `e.conj.trans LinearMap.toMatrix'`. Establish `hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ (e.symm : (Fin d → k) →ₗ[k] W))` using `fun _ => rfl`. Establish `hφ1 : φ 1 = 1`.

Rewrite using `[hφa]`. Establish `: (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id` using `LinearMap.ext fun v => by simp`. Rewrite using `[this, LinearMap.toMatrix'_id]`. Establish `hφm : ∀ x y, φ (x * y) = φ x * φ y`. Introduce `x y`.

Rewrite using `[hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]`. Use `congr 1`. Conclude with `LinearMap.ext fun v => by simp`. Set `S : Γ →* Matrix (Fin d) (Fin d) k` to `{ toFun := fun g => φ (r g) map_one' := by rw [hr1, hφ1] map_mul' := fun g h => by rw [hrm, hφm] }`. Set `σ : Γ →* GL (Fin d) k` to `MonoidHom.toHomUnits S`.

Establish `hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g)` using `fun g => rfl`. Set `Li : (Fin d → k) →ₗ[k] (Fin a → k)` to `W.subtype ∘ₗ e.symm.toLinearMap`. Establish `hLinj : Function.Injective Li`. Introduce `x y hxy`. Conclude with `e.symm.injective (Subtype.val_injective hxy)`.

Take `⟨L', hL'⟩` from `LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)`. Set `B : Matrix (Fin a) (Fin d) k` to `LinearMap.toMatrix' Li`. Set `C : Matrix (Fin d) (Fin a) k` to `LinearMap.toMatrix' L'`. Establish `hCB : C * B = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]`.

Establish `hBv : ∀ c, B.mulVec c = Li c` using `fun c => LinearMap.toMatrix'_mulVec Li c`. Establish `hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k)`. Introduce `g`. Establish `hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g)`. Establish `: τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)` using `LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]`.

Rewrite using `[this, LinearMap.toMatrix'_toLin']`. Rewrite using `[hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]`. Use `congr 1`. Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)`.

Rewrite using `[e.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) = LinearMap.range (B.map f).mulVecLin`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `⟨f ∘ e ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1 : B.mulVec (e ⟨w, hw⟩) = w`. Rewrite using `[hBv]`.

Express the relevant statement in the definitionally equal form `((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w`. Rewrite using `[e.symm_apply_apply]`. Rewrite using `[Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨c, rfl⟩`.

Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[op_smul_eq_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[← hBv, Matrix.mulVec_single_one]`. Rewrite `habs` using `[hspan]`. Establish `hirr : IsIrrSub (mapRep f σ) ⊤`.

Use `GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hCB]`. Conclude with `Matrix.map_one _ f.map_zero f.map_one`. Introduce `g`. Express the relevant statement in the definitionally equal form `(ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f = B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hint g]`. Establish `h2` using `GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr`. Establish `h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L)`. Use function extensionality and compare the values at `g`. Use extensionality with `p q`.

Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]`. Rewrite `h2` using `[h3]`. Establish `h4` using `GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2`. Establish `h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Establish `h6` using `Submodule.map_span φ.toLinearMap (Set.range r)`. Express the relevant statement in the definitionally equal form `Submodule.span k (Set.range r) = ⊤`. Use `Submodule.map_injective_of_injective φ.injective ?_` and prove the remaining obligations. Rewrite using `[h6, Submodule.map_top, LinearEquiv.range]`.

Rewrite `h4` using `[h5]`. Conclude with `h4`.
-/
theorem span_restrict_eq_top_of_isIrrSub_map {k Γ L : Type} [Field k] [Group Γ] [Field L]
    [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W)
    (habs : IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))))) :
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  classical
  letI : Algebra k L := f.toAlgebra
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun
  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl
  let Li : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective Li := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' Li
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = Li c := fun c => LinearMap.toMatrix'_mulVec Li c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  have hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f)
      (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) =
      fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L) := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

/- English proof (translation)
Introduce `k Γ L _ _ _ _ f a ρ W hinv hirr`. Establish `hW : Stable (matRep ((Units.coeHom _).comp ρ)) W` using `fun g v hv => by`. Use `hinv g v hv` as an intermediate fact. Simplify `this` using `[GlobalTheory.BurnsideSub.matRep_apply]`. Establish `hne : W ≠ ⊥`.

Introduce `h0`. Apply `hirr.1` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hsp` using `span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr`.

Unfold `AbsIrrSub`. Conclude with `GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp`.
-/
theorem absIrrSub_of_isIrrSub_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L]
    (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W →
    IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) →
    AbsIrrSub ρ W := by
  intro k Γ L _ _ _ _ f a ρ W hinv hirr
  have hW : Stable (matRep ((Units.coeHom _).comp ρ)) W := fun g v hv => by
    have := hinv g v hv
    simpa [GlobalTheory.BurnsideSub.matRep_apply] using this
  have hne : W ≠ ⊥ := by
    intro h0
    apply hirr.1
    rw [h0]
    simp
  have hsp := span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr
  unfold AbsIrrSub
  exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp

end GlobalTheory.AbsIrrOfAlgClosed
