import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

namespace CxMap

universe a b

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

/- English proof (translation)
Take `⟨g, hg⟩` from `c`. Establish `hg' : K.D0 g = 0` using `hg`. Establish `hc : ∀ T T' (φ : T ⟶ T'), g T' = K.M0.map φ (g T)` using `fun T T' φ => by`. Establish `h` using `congrArg (fun c => c.1 T T' φ) hg'`. Express the relevant statement in the definitionally equal form `g T' - K.M0.map φ (g T) = 0 at h`.

Conclude with `sub_eq_zero.mp h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `T`. Express the relevant statement in the definitionally equal form `m.a0 T (g _) = m'.a0 T (g _)`. Rewrite using `[hc _ _ (θ.app T), hj.e0]`.
-/
theorem h0_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H0) :
    m.h0 c = m'.h0 c := by
  obtain ⟨g, hg⟩ := c
  have hg' : K.D0 g = 0 := hg
  have hc : ∀ T T' (φ : T ⟶ T'), g T' = K.M0.map φ (g T) := fun T T' φ => by
    have h := congrArg (fun c => c.1 T T' φ) hg'
    change g T' - K.M0.map φ (g T) = 0 at h
    exact sub_eq_zero.mp h
  apply Subtype.ext
  funext T
  change m.a0 T (g _) = m'.a0 T (g _)
  rw [hc _ _ (θ.app T), hj.e0]

/- English proof (translation)
Establish `e1 : ∀ A A' A'' (α : A ⟶ A') (β : A' ⟶ A''), c.1 A A'' (α ≫ β) = K.M0.map β (c.1 A A' α) + c.1 A' A'' β`. Introduce `A A' A'' α β`. Establish `h` using `congrArg (fun x => x.1 A A' A'' α β) hc`. Express the relevant statement in the definitionally equal form `K.M0.map β (c.1 A A' α) - c.1 A A'' (α ≫ β) + c.1 A' A'' β = 0 at h`. Take the linear combination `(norm := abel1) -h`.

Establish `e2 : ∀ A A' (α : A ⟶ A'), c.2 A' = K.M1.map α (c.2 A) + K.d0 A' (c.1 A A' α)`. Introduce `A A' α`. Establish `h` using `congrArg (fun x => x.2.1 A A' α) hc`. Express the relevant statement in the definitionally equal form `c.2 A' - K.M1.map α (c.2 A) - K.d0 A' (c.1 A A' α) = 0 at h`. Take the linear combination `(norm := abel1) h`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Express the relevant statement in the definitionally equal form `m'.a0 T' (c.1 _ _ (m'.G.map φ)) = m.a0 T' (c.1 _ _ (m.G.map φ)) + (m'.a0 T' (c.1 _ _ (θ.app T')) - K'.M0.map φ (m'.a0 T (c.1 _ _ (θ.app T))))`. Establish `k1` using `e1 _ _ _ (m.G.map φ) (θ.app T')`. Establish `k2` using `e1 _ _ _ (θ.app T) (m'.G.map φ)`.

Rewrite `k1` using `[θ.naturality φ]`. Establish `k` using `congrArg (m'.a0 T') (k1.symm.trans k2)`. Rewrite `k` using `[map_add, map_add, hj.e0, m'.compDegreeZero_natural]`. Take the linear combination `(norm := abel1) -k`. Use function extensionality and compare the values at `T`.

Express the relevant statement in the definitionally equal form `m'.a1 T (c.2 _) = m.a1 T (c.2 _) + K'.d0 T (m'.a0 T (c.1 _ _ (θ.app T)))`. Rewrite using `[e2 _ _ (θ.app T), map_add, hj.e1, m'.comp_commutes_diffZero]`.
-/
theorem p1_eq_add_D0_of_joined_of_cocycle (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.T1)
    (hc : K.D1 c = 0) :
    m'.p1 c = m.p1 c + K'.D0 (fun T => m'.a0 T (c.1 _ _ (θ.app T))) := by
  have e1 : ∀ A A' A'' (α : A ⟶ A') (β : A' ⟶ A''),
      c.1 A A'' (α ≫ β) = K.M0.map β (c.1 A A' α) + c.1 A' A'' β := by
    intro A A' A'' α β
    have h := congrArg (fun x => x.1 A A' A'' α β) hc
    change K.M0.map β (c.1 A A' α) - c.1 A A'' (α ≫ β) + c.1 A' A'' β = 0 at h
    linear_combination (norm := abel1) -h
  have e2 : ∀ A A' (α : A ⟶ A'), c.2 A' = K.M1.map α (c.2 A) + K.d0 A' (c.1 A A' α) := by
    intro A A' α
    have h := congrArg (fun x => x.2.1 A A' α) hc
    change c.2 A' - K.M1.map α (c.2 A) - K.d0 A' (c.1 A A' α) = 0 at h
    linear_combination (norm := abel1) h
  refine Prod.ext ?_ ?_
  · funext T T' φ
    change m'.a0 T' (c.1 _ _ (m'.G.map φ)) = m.a0 T' (c.1 _ _ (m.G.map φ)) +
      (m'.a0 T' (c.1 _ _ (θ.app T')) - K'.M0.map φ (m'.a0 T (c.1 _ _ (θ.app T))))
    have k1 := e1 _ _ _ (m.G.map φ) (θ.app T')
    have k2 := e1 _ _ _ (θ.app T) (m'.G.map φ)
    rw [θ.naturality φ] at k1
    have k := congrArg (m'.a0 T') (k1.symm.trans k2)
    rw [map_add, map_add, hj.e0, m'.compDegreeZero_natural] at k
    linear_combination (norm := abel1) -k
  · funext T
    change m'.a1 T (c.2 _) = m.a1 T (c.2 _) + K'.d0 T (m'.a0 T (c.1 _ _ (θ.app T)))
    rw [e2 _ _ (θ.app T), map_add, hj.e1, m'.comp_commutes_diffZero]

/- English proof (translation)
Take `⟨⟨x, hx⟩, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (m.z1 ⟨x, hx⟩) : K'.H1) = QuotientAddGroup.mk (m'.z1 ⟨x, hx⟩)`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `⟨fun T => m'.a0 T (x.1 _ _ (θ.app T)), ?_⟩` and prove the remaining obligations. Establish `h` using `p1_eq_add_D0_of_joined_of_cocycle m m' θ hj x (AddMonoidHom.mem_ker.mp hx)`.

Express the relevant statement in the definitionally equal form `_ = -(m.p1 x) + m'.p1 x`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem h1_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H1) :
    m.h1 c = m'.h1 c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  change (QuotientAddGroup.mk (m.z1 ⟨x, hx⟩) : K'.H1) = QuotientAddGroup.mk (m'.z1 ⟨x, hx⟩)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => m'.a0 T (x.1 _ _ (θ.app T)), ?_⟩
  have h := p1_eq_add_D0_of_joined_of_cocycle m m' θ hj x (AddMonoidHom.mem_ker.mp hx)
  change _ = -(m.p1 x) + m'.p1 x
  rw [h]; abel

end CxMap

/- English proof (translation)
Introduce `m m' θ hj` and use `⟨CxMap.h0_eq_of_joined m m' θ hj, CxMap.h1_eq_of_joined m m' θ hj⟩`.
-/
theorem joinedOne_cohomology.{a, b} : JoinedOne.{a, b} := fun m m' θ hj =>
  ⟨CxMap.h0_eq_of_joined m m' θ hj, CxMap.h1_eq_of_joined m m' θ hj⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨joinedOne_cohomology, joinedOne_cohomology, joinedOne_cohomology⟩`.
-/
theorem joinedOne_inst : JoinedOne.{1, 1} ∧ JoinedOne.{1, 0} ∧ JoinedOne.{0, 0} :=
  ⟨joinedOne_cohomology, joinedOne_cohomology, joinedOne_cohomology⟩

end GlobalTheory.CxCoh
