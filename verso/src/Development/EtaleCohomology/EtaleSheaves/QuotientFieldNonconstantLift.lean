import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.QuotientFieldNonconstantLift

def LeafCurveSmall : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  (Set.univ : Set C).Infinite ∧ ∀ Z : Set C, IsClosed Z → Z.Infinite → Z = Set.univ

def LeafLiftNonconst : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ y : C0, ∃ a : C0, pullback.lift c0 e he.symm a ≠ pullback.lift c0 e he.symm y

/- English proof (translation)
Take `⟨_, _, _⟩` from `id hc`. Establish `: JacobsonSpace C` using `LocallyOfFiniteType.jacobsonSpace c`. Use `GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_` and prove the remaining obligations. Establish `hcl : IsClosed ({g y} : Set Y)`. Use `g.isClosedMap _ hy` as an intermediate fact.

Simplify using `using this`. Assume the negation of the conclusion as `hinf`. Use `(hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf` as an intermediate fact. Take `⟨a, ha⟩` from `hn y`. Establish `: a ∈ g ⁻¹' {g y}` using `this ▸ Set.mem_univ a`.

Conclude with `ha this`.
-/
theorem lqf_of_nonconst (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C Y : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : IsCurve c) (g : C ⟶ Y) [LocallyOfFiniteType g] [UniversallyClosed g]
    (hn : ∀ y, ∃ a, g a ≠ g y) : LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_
  have hcl : IsClosed ({g y} : Set Y) := by
    have := g.isClosedMap _ hy
    simpa using this
  by_contra hinf
  have := (hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf
  obtain ⟨a, ha⟩ := hn y
  have : a ∈ g ⁻¹' {g y} := this ▸ Set.mem_univ a
  exact ha this

/- English proof (translation)
Take `⟨b, hb⟩` from `((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty`. Take `⟨a, rfl⟩` from `hg.surj b`. Conclude with `⟨a, by simpa using hb.2⟩`.
-/
theorem nonconst_of_surj (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hg : Surjective g) (y : C1) : ∃ a, g a ≠ g y := by
  obtain ⟨b, hb⟩ := ((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty
  obtain ⟨a, rfl⟩ := hg.surj b
  exact ⟨a, by simpa using hb.2⟩

/- English proof (translation)
Take `⟨_, _, _⟩` from `id hc`. Take `⟨_, _, _⟩` from `id hc1`. Establish `: LocallyOfFiniteType g` using `locallyOfFiniteType_of_comp g c0`. Establish `: UniversallyClosed g` using `UniversallyClosed.of_comp_of_isSeparated g c0`. Conclude with `lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)`.
-/
theorem lqf_gamma (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hc1 : IsCurve (g ≫ c0)) (hg : Surjective g) :
    LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  obtain ⟨_, _, _⟩ := id hc1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g c0
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g c0
  exact lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)

/- English proof (translation)
Introduce `k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2`. Use `⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩` and prove the remaining obligations. Take `⟨_, _, _⟩` from `id hc0`. Use `set g := pullback.lift c0 e he.symm with hgdef`. Establish `hfst : g ≫ pullback.fst _ _ = c0` using `pullback.lift_fst _ _ _`.

Establish `: LocallyOfFiniteType (g ≫ pullback.fst _ _)` using `by rw [hfst]; infer_instance`. Establish `: UniversallyClosed (g ≫ pullback.fst _ _)` using `by rw [hfst]; infer_instance`. Establish `: LocallyOfFiniteType g` using `locallyOfFiniteType_of_comp g (pullback.fst _ _)`. Establish `: UniversallyClosed g` using `UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)`. Conclude with `lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)`.
-/
theorem LeafQFOmega_of (hC : LeafCurveSmall) (hL : LeafLiftNonconst) :
    LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩
  obtain ⟨_, _, _⟩ := id hc0
  set g := pullback.lift c0 e he.symm with hgdef
  have hfst : g ≫ pullback.fst _ _ = c0 := pullback.lift_fst _ _ _
  have : LocallyOfFiniteType (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : UniversallyClosed (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.fst _ _)
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)
  exact lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)

end LateralTheory.E.QuotientFieldNonconstantLift
