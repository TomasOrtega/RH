import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BurnsideSub

/- English proof (translation)
Simplify using `[matRep]`.
-/
theorem matRep_apply {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (g : Γ)
    (v : Fin a → k) :
    matRep ((Units.coeHom _).comp ρ) g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := by
  simp [matRep]

/- English proof (translation)
Establish `hinj : Function.Injective B.mulVecLin`. Introduce `x y hxy`. Use `congrArg C.mulVec hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hCB]`. Establish `hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) → IsInv ρ (U.map B.mulVecLin)`.

Introduce and unpack `U hU g _ ⟨v, hv, rfl⟩`. Use `⟨_, hU g v hv, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]`. Use `⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_map, h0, Submodule.map_bot]`.

Establish `hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin` using `LinearMap.map_le_range`. Break down `h.2.2 _ hle (hmap U hU) with h1 | h1` into its components or cases. Use `left`. Conclude with `Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)`. Use `right`.

Rewrite `h1` using `[LinearMap.range_eq_map]`. Conclude with `Submodule.map_injective_of_injective hinj h1`.
-/
theorem isIrrSub_top_of_intertwine {K Γ : Type} [Field K] [Group Γ] {a d : ℕ}
    (ρ : Γ →* GL (Fin a) K) (σ : Γ →* GL (Fin d) K) (B : Matrix (Fin a) (Fin d) K)
    (C : Matrix (Fin d) (Fin a) K) (hCB : C * B = 1)
    (hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) K) * B = B * (σ g : Matrix (Fin d) (Fin d) K))
    (h : IsIrrSub ρ (LinearMap.range B.mulVecLin)) : IsIrrSub σ ⊤ := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    have := congrArg C.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCB] using this
  have hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) →
      IsInv ρ (U.map B.mulVecLin) := by
    rintro U hU g _ ⟨v, hv, rfl⟩
    refine ⟨_, hU g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  refine ⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩
  · rw [LinearMap.range_eq_map, h0, Submodule.map_bot]
  · have hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin := LinearMap.map_le_range
    rcases h.2.2 _ hle (hmap U hU) with h1 | h1
    · left
      exact Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)
    · right
      rw [LinearMap.range_eq_map] at h1
      exact Submodule.map_injective_of_injective hinj h1

/- English proof (translation)
Introduce `k Γ _ _ a ρ W hW habs`. Use `set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ`. Set `r : Γ → Module.End k W` to `fun g => (τ g).restrict (hW g)`. Establish `hr1 : r 1 = 1`. Use extensionality with `v`.

Simplify using `[r]`. Establish `hrm : ∀ g h, r (g * h) = r g * r h`. Introduce `g h`. Use extensionality with `v`. Simplify using `[r]`.

Set `d` to `Module.finrank k W`. Set `e : W ≃ₗ[k] (Fin d → k)` to `(Module.finBasis k W).equivFun`. Set `φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k` to `e.conj.trans LinearMap.toMatrix'`. Establish `hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ (e.symm : (Fin d → k) →ₗ[k] W))` using `fun _ => rfl`. Establish `hφ1 : φ 1 = 1`.

Rewrite using `[hφa]`. Establish `: (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id` using `LinearMap.ext fun v => by simp`. Rewrite using `[this, LinearMap.toMatrix'_id]`. Establish `hφm : ∀ x y, φ (x * y) = φ x * φ y`. Introduce `x y`.

Rewrite using `[hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]`. Use `congr 1`. Conclude with `LinearMap.ext fun v => by simp`. Set `S : Γ →* Matrix (Fin d) (Fin d) k` to `{ toFun := fun g => φ (r g) map_one' := by rw [hr1, hφ1] map_mul' := fun g h => by rw [hrm, hφm] }`. Set `σ : Γ →* GL (Fin d) k` to `MonoidHom.toHomUnits S`.

Establish `hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g)` using `fun g => rfl`. Set `L : (Fin d → k) →ₗ[k] (Fin a → k)` to `W.subtype ∘ₗ e.symm.toLinearMap`. Establish `hLinj : Function.Injective L`. Introduce `x y hxy`. Conclude with `e.symm.injective (Subtype.val_injective hxy)`.

Take `⟨L', hL'⟩` from `LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)`. Set `B : Matrix (Fin a) (Fin d) k` to `LinearMap.toMatrix' L`. Set `C : Matrix (Fin d) (Fin a) k` to `LinearMap.toMatrix' L'`. Establish `hCB : C * B = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]`.

Establish `hBv : ∀ c, B.mulVec c = L c` using `fun c => LinearMap.toMatrix'_mulVec L c`. Establish `hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k)`. Introduce `g`. Establish `hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g)`. Establish `: τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)` using `LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]`.

Rewrite using `[this, LinearMap.toMatrix'_toLin']`. Rewrite using `[hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]`. Use `congr 1`. Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)`.

Rewrite using `[e.symm_apply_apply]`. Both sides reduce to the same expression. Use `set f := algebraMap k (AlgebraicClosure k) with hf`. Establish `hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) = LinearMap.range (B.map f).mulVecLin`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `⟨f ∘ e ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1 : B.mulVec (e ⟨w, hw⟩) = w`.

Rewrite using `[hBv]`. Express the relevant statement in the definitionally equal form `((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w`. Rewrite using `[e.symm_apply_apply]`. Rewrite using `[Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]`. Both sides reduce to the same expression.

Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[op_smul_eq_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[← hBv, Matrix.mulVec_single_one]`. Unfold `AbsIrrSub at habs`.

Rewrite `habs` using `[hspan]`. Establish `hirr : IsIrrSub (mapRep f σ) ⊤`. Use `isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hCB]`. Conclude with `Matrix.map_one _ f.map_zero f.map_one`.

Introduce `g`. Express the relevant statement in the definitionally equal form `(ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f = B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hint g]`. Establish `h2` using `GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr`. Establish `h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f`.

Use function extensionality and compare the values at `g`. Use extensionality with `p q`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]`. Rewrite `h2` using `[h3]`. Establish `h4` using `GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2`.

Establish `h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Establish `h6` using `Submodule.map_span φ.toLinearMap (Set.range r)`. Express the relevant statement in the definitionally equal form `Submodule.span k (Set.range r) = ⊤`.

Use `Submodule.map_injective_of_injective φ.injective ?_` and prove the remaining obligations. Rewrite using `[h6, Submodule.map_top, LinearEquiv.range]`. Rewrite `h4` using `[h5]`. Conclude with `h4`.
-/
theorem span_restrict_eq_top_of_absIrrSub : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W),
    AbsIrrSub ρ W →
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ a ρ W hW habs
  classical
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

  let L : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' L
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = L c := fun c => LinearMap.toMatrix'_mulVec L c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  set f := algebraMap k (AlgebraicClosure k) with hf
  have hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) =
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
      refine ⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  unfold AbsIrrSub at habs
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]
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

end GlobalTheory.BurnsideSub
