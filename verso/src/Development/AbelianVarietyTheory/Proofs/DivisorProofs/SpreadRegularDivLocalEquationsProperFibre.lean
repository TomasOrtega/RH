import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.Spread

/- English proof (translation)
Use `isOpen_iff_forall_mem_open.2 fun x hx => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, x ∈ D.U j := by`. Establish `: x ∈ (⨆ i, D.U i)` using `D.cover ▸ trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`. Use `⟨(D.U j : Set M.Z) ∩ {w | G / valF M.pt (D.U j) (D.f j) ∈ M.O w}, ?_, (D.U j).isOpen.inter (M.isOpen_setOf_mem_O _), hj, hx _ ⟨j, hj, rfl⟩⟩` and prove the remaining obligations.

Introduce and unpack `w ⟨hwj, hwG⟩ f' ⟨k, hwk, rfl⟩`. Take `⟨u, hu⟩` from `D.assoc j k`. Establish `hne : ((D.U j ⊓ D.U k : M.Z.Opens) : Set M.Z).Nonempty` using `⟨w, hwj, hwk⟩`. Establish `e1 : valF M.pt (D.U k) (D.f k) = valF M.pt (D.U j) (D.f j) * valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k))`. Rewrite using `[← M.valF_resG inf_le_right hne (D.f k), ← hu, ← M.res_apply _ hne, map_mul, M.res_apply, M.res_apply, M.valF_resG inf_le_left hne]`.

Establish `e2 : valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) * valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) = 1`. Rewrite using `[← M.res_apply _ hne, ← M.res_apply _ hne, ← map_mul, Units.mul_inv, map_one]`. Establish `e3 : (valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)))⁻¹ = valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k))` using `inv_eq_of_mul_eq_one_right e2`. Rewrite using `[e1, div_mul_eq_div_div, div_eq_mul_inv _ (valF M.pt (D.U j ⊓ D.U k) _), e3]`. Conclude with `mul_mem hwG (RatModel.valF_mem_O (show w ∈ D.U j ⊓ D.U k from ⟨hwj, hwk⟩) _)`.
-/
theorem isOpen_good {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (D : EffCartierData M.Z) (G : Ω) :
    IsOpen {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ : ∃ j, x ∈ D.U j := by
    have : x ∈ (⨆ i, D.U i) := D.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨(D.U j : Set M.Z) ∩ {w | G / valF M.pt (D.U j) (D.f j) ∈ M.O w}, ?_,
    (D.U j).isOpen.inter (M.isOpen_setOf_mem_O _), hj, hx _ ⟨j, hj, rfl⟩⟩
  rintro w ⟨hwj, hwG⟩ f' ⟨k, hwk, rfl⟩
  obtain ⟨u, hu⟩ := D.assoc j k
  have hne : ((D.U j ⊓ D.U k : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwj, hwk⟩
  have e1 : valF M.pt (D.U k) (D.f k) =
      valF M.pt (D.U j) (D.f j) * valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) := by
    rw [← M.valF_resG inf_le_right hne (D.f k), ← hu, ← M.res_apply _ hne, map_mul, M.res_apply, M.res_apply,
      M.valF_resG inf_le_left hne]
  have e2 : valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) *
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) = 1 := by
    rw [← M.res_apply _ hne, ← M.res_apply _ hne, ← map_mul, Units.mul_inv, map_one]
  have e3 : (valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)))⁻¹ =
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) :=
    inv_eq_of_mul_eq_one_right e2
  rw [e1, div_mul_eq_div_div, div_eq_mul_inv _ (valF M.pt (D.U j ⊓ D.U k) _), e3]
  exact mul_mem hwG (RatModel.valF_mem_O (show w ∈ D.U j ⊓ D.U k from ⟨hwj, hwk⟩) _)

end GlobalTheory.Poinc.Spread

/- English proof (translation)
Introduce `o Ω _ _ _ M₁ M π _ hP D z G hG hfib`. Use `set Good : Set M.Z := {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} with hGood`. Establish `hcl : IsClosed (π.base '' Goodᶜ)` using `π.isClosedMap _ (Spread.isOpen_good M D G).isClosed_compl`. Establish `hz : z ∉ π.base '' Goodᶜ`. Introduce and unpack `⟨x', hx', rfl⟩`.

Conclude with `hx' (hfib x' rfl)`. Establish `hW : z ∈ ({w | G ∈ M₁.O w} ∩ (π.base '' Goodᶜ)ᶜ : Set M₁.Z)` using `⟨hG, hz⟩`. Take `⟨V, hV, hzV, hVW⟩` from `exists_isAffineOpen_mem_and_subset (U := ⟨_, (M₁.isOpen_setOf_mem_O G).inter hcl.isOpen_compl⟩) hW`. Establish `hmem : G ∈ M₁.ringOn (V : Set M₁.Z)` using `RatModel.mem_ringOn.2 fun w hw => (hVW hw).1`. Take `⟨g, hg⟩` from `(RatModel.mem_ringOn_iff_exists ⟨z, hzV⟩).1 hmem`.

Use `⟨⟨V, hV⟩, g, hzV, hg, fun x' hx' => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `(hVW hx').2 ⟨x', h, rfl⟩`.
-/
theorem GlobalTheory.Poinc.spread_regular_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  intro o Ω _ _ _ M₁ M π _ hP D z G hG hfib
  set Good : Set M.Z := {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} with hGood
  have hcl : IsClosed (π.base '' Goodᶜ) :=
    π.isClosedMap _ (Spread.isOpen_good M D G).isClosed_compl
  have hz : z ∉ π.base '' Goodᶜ := by
    rintro ⟨x', hx', rfl⟩
    exact hx' (hfib x' rfl)
  have hW : z ∈ ({w | G ∈ M₁.O w} ∩ (π.base '' Goodᶜ)ᶜ : Set M₁.Z) := ⟨hG, hz⟩
  obtain ⟨V, hV, hzV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, (M₁.isOpen_setOf_mem_O G).inter hcl.isOpen_compl⟩) hW
  have hmem : G ∈ M₁.ringOn (V : Set M₁.Z) := RatModel.mem_ringOn.2 fun w hw => (hVW hw).1
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists ⟨z, hzV⟩).1 hmem
  refine ⟨⟨V, hV⟩, g, hzV, hg, fun x' hx' => ?_⟩
  by_contra h
  exact (hVW hx').2 ⟨x', h, rfl⟩
