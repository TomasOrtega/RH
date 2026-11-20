import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.LiftForms

/- English proof (translation)
Introduce `D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ`. Use `set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef`. Establish `hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)` using `fun x => rfl`. Establish `hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z)`. Rewrite using `[hZ, span_range_mulVec]`.

Both sides reduce to the same expression. Establish `hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) = J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))`. Introduce `x`. Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Rewrite using `[hspan]`.

Conclude with `Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩`. Introduce `w hw`. Rewrite `hw` using `[hspan]`. Establish `hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤ (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨z, rfl⟩, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner, hform_orth hP, sub_self]`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)`. Establish `hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y = D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y)`. Establish `h` using `LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1)) (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap) (fun k => by show D.what₂.thetaP (tup t) ((i : ℕ) …`.

Rewrite using `[hproj]`. Conclude with `hθ _)`. Introduce `y`. Conclude with `LinearMap.congr_fun h y`. Establish `hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1))`.

Introduce `w hw`. Rewrite using `[LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]`. Establish `hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1)`. Establish `h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ`. Rewrite using `[LinearMap.orthogonal_ker]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.orthogonal_le hle1` as an intermediate fact. Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis.

Conclude with `inf_le_left`. Establish `hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)`. Establish `h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) = (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y`.

Introduce `y`. Simplify using `only [hZj]`. Conclude with `hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ) (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))`. Establish `h6 : Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} = (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce `u hu`. Take `⟨c, hc⟩` from `hu`. Use `⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩` and prove the remaining obligations. Rewrite using `[hJ, LinearEquiv.apply_symm_apply, hc]`.

Both sides reduce to the same expression. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨c, hc⟩` from `(hL.2 x).1 hx`. Establish `hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) = ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v` using `hc`. Establish `key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier}, D.what₂.jMt (tup t) ((i : ℕ) + 1) y = ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v`.

Use `Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier}, D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_` and prove the remaining obligations. Introduce and unpack `_ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩`. Conclude with `⟨y + z, add_mem hy hz, map_add _ _ _⟩`. Take `⟨y, hy⟩` from `D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv`. Use `⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩` and prove the remaining obligations.

Use `⟨fun u => if u = v then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, Finset.sum_eq_single v]`. Simplify using the standard rewrite rules. Introduce `u _ hu`. Simplify using `[hu]`.

Introduce `h`. Conclude with `absurd hv h`. Take `⟨y, hy, hyx⟩` from `key`. Establish `hxy : y = eMt i t x` using `jMt_injective _ _ (hyx.trans hc'.symm)`. Express the relevant statement in the definitionally equal form `eMt i t x ∈ _`.

Rewrite using `[← hxy]`. Conclude with `hy`. Set `π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)` to `((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)`. Establish `hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))`. Introduce `x`.

Use `show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Establish `hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x))`. Introduce `x`. Take `⟨x, rfl⟩` from `(eMt i t).surjective x`.

Rewrite using `[h4', ← hJ, hproj, hπe]`. Both sides reduce to the same expression. Establish `hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} = π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, hx⟩`. Take `⟨u, rfl⟩` from `carrier_subset _ _ m hm`. Conclude with `⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨_, hu, (hπ u).symm⟩`.

Unfold `Idx.TjL`. Rewrite using `[hset, ← Submodule.map_span, h6]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`.

Conclude with `⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩`. Introduce and unpack `⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨y, hy, rfl⟩, hπe y⟩`.
-/
theorem TjL_eq_map_matLat : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ
  classical
  set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef
  have hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) := fun x => rfl
  have hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) =
      Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) := by
    rw [hZ, span_range_mulVec]
    rfl

  have hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) =
      J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro w hw
      rw [hspan] at hw
      have hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤
          (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner,
          hform_orth hP, sub_self]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

  have hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y =
      D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y) := by
    have h := LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
        ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap)
      (fun k => by
        show D.what₂.thetaP (tup t) ((i : ℕ) + 1) (J (Pi.single k 1)) =
          D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J (Pi.single k 1)))
        rw [hproj]
        exact hθ _)
    intro y
    exact LinearMap.congr_fun h y
  have hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) := by
    intro w hw
    rw [LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]
  have hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1) := by
    have h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ := by
      rw [LinearMap.orthogonal_ker]
      rfl
    rw [h1]
    apply le_antisymm
    · have := Submodule.orthogonal_le hle1
      rwa [Submodule.orthogonal_orthogonal] at this
    · exact inf_le_left
  have hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)
  have h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj]
    exact hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ)
      (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))

  have h6 : Submodule.span (𝓞 D.what₂.LL)
      {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro u hu
      obtain ⟨c, hc⟩ := hu
      refine ⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩
      rw [hJ, LinearEquiv.apply_symm_apply, hc]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hL.2 x).1 hx
      have hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) =
          ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
          D.what₂.jMt (tup t) ((i : ℕ) + 1) y =
            ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
        refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
            D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
        · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
        · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv
          refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
          refine ⟨fun u => if u = v then 1 else 0, ?_⟩
          rw [hy, Finset.sum_eq_single v]
          · simp
          · intro u _ hu
            simp [hu]
          · intro h; exact absurd hv h
      obtain ⟨y, hy, hyx⟩ := key
      have hxy : y = eMt i t x := jMt_injective _ _ (hyx.trans hc'.symm)
      change eMt i t x ∈ _
      rw [← hxy]
      exact hy

  let π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ
      (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (eMt i t).surjective x
    rw [h4', ← hJ, hproj, hπe]
    rfl
  have hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end GlobalTheory.Mem.LiftForms

end
