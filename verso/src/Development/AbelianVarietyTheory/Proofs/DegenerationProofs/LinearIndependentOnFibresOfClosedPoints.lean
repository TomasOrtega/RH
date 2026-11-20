import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenSetOfLinearIndependentOnFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

/- English proof (translation)
Take `⟨P, p, π, h1, h2, h3, h4⟩` from `exists_fibrePower f r`. Establish `hxt : ∀ t, x t = z` using `fun t => by`. Rewrite using `[← Set.mem_singleton_iff, ← hx]`. Conclude with `⟨t, rfl⟩`. Set `t₀ : Sp K` to `IsLocalRing.closedPoint K`.

Take `⟨a, ha⟩` from `exists_det_ne_zero (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2)) fun c hc => hz c fun g j hg => hc (⟨g, hg⟩, j)`. Set `j : Fin r → L.ι` to `fun k => (a k).2`. Set `U : P.Opens` to `LB.wchart L π j`. Establish `hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k)` using `LB.wchart_le L π j`. Set `M : Matrix (Fin r) (Fin r) Γ(P, U)` to `Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))`.

Establish `hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det = (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det`. Introduce `K _ h hh`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `k i`.

Conclude with `evalHom_appLE h U hh (π k) _ (hU k) _`. Set `O : P.Opens` to `P.basicOpen M.det`. Establish `hmem : z ∈ p '' (O : Set P)`. Take `⟨h, hp, hπ⟩` from `h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2`. Establish `hle : ⊤ ≤ h ⁻¹ᵁ U`.

Introduce `t ht`. Use `Set.mem_iInter.2 fun k => ?_` and prove the remaining obligations. Establish `hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k)`. Assume the negation of the conclusion as `hn`. Conclude with `ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)`.

Use `hk ht` as an intermediate fact. Rewrite `this` using `[← hπ k]`. Conclude with `this`. Use `⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hM]`.

Simplify using `only [hπ]`. Conclude with `ha`. Rewrite using `[← Scheme.Hom.comp_apply, hp, hxt]`. Take `⟨w, hw, rfl⟩` from `hmem`. Set `t : Sp K'` to `IsLocalRing.closedPoint K'`.

Establish `ht : x' t = p w`. Rewrite using `[← Set.mem_singleton_iff, ← hx']`. Conclude with `⟨t, rfl⟩`. Take `⟨h, hh⟩` from `exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm`. Establish `hO : (h ≫ O.ι) t ∈ O` using `(h t).2`.

Establish `hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U` using `(top_le_iff _ U t).2 (P.basicOpen_le _ hO)`. Establish `hd` using `(mem_basicOpen_iff _ U hle M.det t).1 hO`. Rewrite `hd` using `[hM]`. Use `Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)` and prove the remaining obligations. Use `hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem geometric_of_field (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] (L : LB G) (r : ℕ) (s : Fin r → LB.Sec L) (z : Z)
    (K : Type) [Field K] (x : Sp K ⟶ Z) (hx : Set.range x = {z})
    (hz : ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0)
    (K' : Type) [Field K'] [IsAlgClosed K'] (x' : Sp K' ⟶ Z) (hx' : Set.range x' = {z})
    (c : Fin r → K') (hc : ∀ (g : Sp K' ⟶ G) (j : L.ι), g ≫ f = x' →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) : c = 0 := by
  classical
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← hx]
    exact ⟨t, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  have hmem : z ∈ p '' (O : Set P) := by
    obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]
  obtain ⟨w, hw, rfl⟩ := hmem
  let t : Sp K' := IsLocalRing.closedPoint K'
  have ht : x' t = p w := by
    rw [← Set.mem_singleton_iff, ← hx']
    exact ⟨t, rfl⟩
  obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
  have hO : (h ≫ O.ι) t ∈ O := (h t).2
  have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
  have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
  rw [hM] at hd
  refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
  have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

/- English proof (translation)
Introduce `G Z π _ f _ _ L hL r s P h z`. Set `U : Z.Opens` to `⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩`. Establish `hU : U = ⊤` using `(GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by`. Use `⟨fun _ => trivial, fun _ => ?_⟩` and prove the remaining obligations. Take `⟨K, _, x, hx, hz⟩` from `h y hy`.

Introduce `K' _ _ x' hx' c hc`. Conclude with `geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc`. Establish `: z ∈ U` using `by rw [hU]; trivial`. Conclude with `this`.
-/
theorem linearIndependent_on_fibres_of_closedPoints :
    ∀ (G Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G), L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), let P : Z → Prop := fun z => ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0; (∀ z, IsClosed ({z} : Set Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Z), Set.range x = {z} ∧ ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0) → ∀ z, P z := by
  intro G Z π _ f _ _ L hL r s P h z
  let U : Z.Opens := ⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩
  have hU : U = ⊤ := (GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨K, _, x, hx, hz⟩ := h y hy
    intro K' _ _ x' hx' c hc
    exact geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc
  have : z ∈ U := by rw [hU]; trivial
  exact this

end GlobalTheory.FibreLinInd
