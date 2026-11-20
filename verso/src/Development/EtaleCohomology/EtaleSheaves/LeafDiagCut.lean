import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafDiagCut

def LeafConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n),
  HK.pull R φ F n x = 0 ↔ ∃ r : HK R (mappingCone φ) F n, HK.pull R (mappingCone.inr φ) F n r = x

def LeafThomRel : Prop := E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
  (W : (pullback p p).Opens), (W : Set ↥(pullback p p)) = (Set.range (pullback.diagonal p))ᶜ →
  ∃ θ : Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d),
    ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens), (U : Set X) = (Set.range x)ᶜ →
      ∃ (g : U.toScheme ⟶ W.toScheme) (hg : g ≫ W.ι = U.ι ≫ pullback.lift (p ≫ x) (𝟙 X) (by simp [hx])),
        ∀ r : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d), ∃ m : ℤ, r = m • HK.pull (ZMod q)
          (mappingCone.map ((chains _).map (sch.map U.ι)) ((chains _).map (sch.map W.ι)) ((chains _).map (sch.map g))
            ((chains _).map (sch.map (pullback.lift (p ≫ x) (𝟙 X) (by simp [hx]))))
            (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hg]))
          (tw q d) (2 * d) θ

/- English proof (translation)
Take `⟨x, rfl⟩` from `x.mk_surjective`. Use `congrArg CohomologyClass.mk (Cocycle.ext ?_)` and prove the remaining obligations. Simplify using `[zcomp, Cochain.ofHom_comp]`.
-/
theorem hkPull_comp {R : Type} [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

/- English proof (translation)
Introduce `B q _ k _ _ hq X p _ d _`. Establish `hcl : IsClosed (Set.range (pullback.diagonal p))` using `(pullback.diagonal p).isClosedEmbedding.isClosed_range`. Set `W0 : (pullback p p).Opens` to `⟨(Set.range (pullback.diagonal p))ᶜ, hcl.isOpen_compl⟩`. Take `⟨θ, hθ⟩` from `h2 B q k hq p d W0 rfl`. Use `⟨HK.pull (ZMod q) (mappingCone.inr ((chains _).map (sch.map W0.ι))) (tw q d) (2 * d) θ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `W hW`. Establish `hWW : W = W0` using `TopologicalSpace.Opens.ext hW`. Substitute `hWW` using the available equality. Conclude with `(h1 _ _ _ _ _).mpr ⟨θ, rfl⟩`. Introduce `x hx U hU c hc`.

Take `⟨g, hg, hr⟩` from `hθ x hx U hU`. Take `⟨r, rfl⟩` from `(h1 _ _ _ _ c).mp hc`. Take `⟨m, rfl⟩` from `hr r`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul]`.

Use `congr 1`. Use `show _ = HK.pull _ _ _ _ (HK.pull _ _ _ _ θ)`. Rewrite using `[← hkPull_comp, ← hkPull_comp]`. Use `congr 1`. Simplify using `[mappingCone.map]`.
-/
theorem goal_of (h1 : LeafConeExact) (h2 : LeafThomRel) : E8.LeafDiag := by
  intro B q _ k _ _ hq X p _ d _
  have hcl : IsClosed (Set.range (pullback.diagonal p)) := (pullback.diagonal p).isClosedEmbedding.isClosed_range
  let W0 : (pullback p p).Opens := ⟨(Set.range (pullback.diagonal p))ᶜ, hcl.isOpen_compl⟩
  obtain ⟨θ, hθ⟩ := h2 B q k hq p d W0 rfl
  refine ⟨HK.pull (ZMod q) (mappingCone.inr ((chains _).map (sch.map W0.ι))) (tw q d) (2 * d) θ, ?_, ?_⟩
  · intro W hW
    have hWW : W = W0 := TopologicalSpace.Opens.ext hW
    subst hWW
    exact (h1 _ _ _ _ _).mpr ⟨θ, rfl⟩
  · intro x hx U hU c hc
    obtain ⟨g, hg, hr⟩ := hθ x hx U hU
    obtain ⟨r, rfl⟩ := (h1 _ _ _ _ c).mp hc
    obtain ⟨m, rfl⟩ := hr r
    refine ⟨m, ?_⟩
    rw [map_zsmul]
    congr 1
    show _ = HK.pull _ _ _ _ (HK.pull _ _ _ _ θ)
    rw [← hkPull_comp, ← hkPull_comp]
    congr 1
    simp [mappingCone.map]

end LateralTheory.E.LeafDiagCut
