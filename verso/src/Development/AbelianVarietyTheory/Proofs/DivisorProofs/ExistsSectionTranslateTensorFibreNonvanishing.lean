import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtensionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Use `push_neg at hz`. Set `C : Set X` to `⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ`. Establish `hC : IsClosed C` using `isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl`. Take `⟨w, hw, hcl⟩` from `hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩`.

Take `⟨s, hs⟩` from `h w hcl`. Conclude with `Set.mem_iInter.1 hw s hs`.
-/
theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

/- English proof (translation)
Use `P.isAb.proper` as an intermediate fact. Establish `: QuasiCompact (pullback.fst t P.A.hom)` using `inferInstance`. Conclude with `QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)`.
-/
theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

/- English proof (translation)
Use `compactSpace_fibre P K t` as an intermediate fact. Use `exists_sec_of_closed _ (fun z hz => ?_) z` and prove the remaining obligations. Use `P.isAb.smooth` as an intermediate fact. Establish `: LocallyOfFiniteType (fst (Over.mk t) P.A).left` using `(inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))`. Set `f` to `(fst (Over.mk t) P.A).left`.

Set `p₀` to `pointOfClosedPoint f z hz`. Establish `hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom`. Rewrite using `[← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]`. Conclude with `Category.id_comp _`. Set `q : Over.mk t ⟶ Over.mk t ⊗ P.A` to `Over.homMk p₀ hw`.

Establish `hq : q ≫ fst (Over.mk t) P.A = 𝟙 _` using `by ext1`. Conclude with `pointOfClosedPoint_comp f z hz`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q`.

Rewrite using `[← hq, lift_comp_fst_snd]`. Rewrite `hs` using `[e]`. Establish `h2 : q.left (IsLocalRing.closedPoint K) = z` using `pointOfClosedPoint_apply f z hz _`. Rewrite using `[← h2]`. Conclude with `hs`.
-/
theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

/- English proof (translation)
Introduce `S P k _ t c y`. Conclude with `GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y`.
-/
theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
