import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenPosDefOfContinuous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelOpen

/- English proof (translation)
Establish `han : AnalyticAt ℂ f a` using `analyticAt_pi_iff.mpr fun i => ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha`. Establish `hb` using `GlobalTheory.InjHol.bijective_fderiv_of_injOn n U f hU hf hinj a ha`. Establish `hm : Filter.map f (nhds a) = nhds (f a)` using `han.hasStrictFDerivAt.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hb.2)`. Rewrite using `[← hm]`. Conclude with `Filter.image_mem_map (hU.mem_nhds ha)`.
-/
theorem image_mem_nhds_of_injOn {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {a : Fin n → ℂ}
    (ha : a ∈ U) : f '' U ∈ nhds (f a) := by
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn n U f hU hf hinj a ha
  have hm : Filter.map f (nhds a) = nhds (f a) :=
    han.hasStrictFDerivAt.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hb.2)
  rw [← hm]
  exact Filter.image_mem_map (hU.mem_nhds ha)

/- English proof (translation)
Use extensionality with `i j`. Establish `h1` using `h s(i, j)`. Establish `h2 : s((s(i, j) : Sym2 J).out.1, (s(i, j) : Sym2 J).out.2) = s(i, j)` using `Quot.out_eq (s(i, j) : Sym2 J)`. Break down `Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩` into its components or cases. Rewrite `h1` using `[h3, h4]`. Then use the resulting hypothesis.

Rewrite `h1` using `[h3, h4]`. Rewrite using `[← hs.apply i j, ← ht.apply i j]`. Conclude with `h1`.
-/
theorem eq_of_out {J R : Type} {s t : Matrix J J R} (hs : s.IsSymm) (ht : t.IsSymm)
    (h : ∀ z : Sym2 J, s z.out.1 z.out.2 = t z.out.1 z.out.2) : s = t := by
  ext i j
  have h1 := h s(i, j)
  have h2 : s((s(i, j) : Sym2 J).out.1, (s(i, j) : Sym2 J).out.2) = s(i, j) :=
    Quot.out_eq (s(i, j) : Sym2 J)
  rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rwa [h3, h4] at h1
  · rw [h3, h4] at h1
    rw [← hs.apply i j, ← ht.apply i j]
    exact h1

/- English proof (translation)
Introduce `h B τ b₀ hB hb₀ hd hs hinj`. Set `e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2)` to `Fintype.equivFinOfCardEq (GlobalTheory.card_sym2_fin h)`. Set `p : Matrix (Fin h) (Fin h) ℂ → (Fin (h * (h + 1) / 2) → ℂ)` to `fun t k => t (e.symm k).out.1 (e.symm k).out.2`. Establish `hpc : Continuous p` using `continuous_pi fun k => continuous_id.matrix_elem _ _`. Establish `hp : ∀ s t : Matrix (Fin h) (Fin h) ℂ, s.IsSymm → t.IsSymm → p s = p t → s = t`.

Introduce `s t hs' ht' hst`. Use `eq_of_out hs' ht' fun z => ?_` and prove the remaining obligations. Use `congrFun hst (e z)` as an intermediate fact. Simplify `this` using `only [p, Equiv.symm_apply_apply]`. Establish `key` using `image_mem_nhds_of_injOn (f := fun b => p (τ b)) hB (differentiableOn_pi.mpr fun k => hd _ _) (fun x hx y hy hxy => hinj hx hy (hp _ _ (hs x hx).1 (hs y hy).1 hxy)) hb₀`.

Use `⟨_, hpc.continuousAt.preimage_mem_nhds key, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨b, hb, hbt⟩ ht -`. Conclude with `⟨b, hb, hp _ _ (hs b hb).1 ht hbt⟩`.
-/
theorem exists_nhds_subset_image :
    ∀ (h : ℕ) (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ) (b₀ : Fin (h * (h + 1) / 2) → ℂ), IsOpen B → b₀ ∈ B → (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → Set.InjOn τ B → ∃ N ∈ nhds (τ b₀), ∀ t ∈ N, t.IsSymm → (t.map Complex.im).PosDef → ∃ b ∈ B, τ b = t := by
  intro h B τ b₀ hB hb₀ hd hs hinj
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (GlobalTheory.card_sym2_fin h)
  let p : Matrix (Fin h) (Fin h) ℂ → (Fin (h * (h + 1) / 2) → ℂ) :=
    fun t k => t (e.symm k).out.1 (e.symm k).out.2
  have hpc : Continuous p := continuous_pi fun k => continuous_id.matrix_elem _ _
  have hp : ∀ s t : Matrix (Fin h) (Fin h) ℂ, s.IsSymm → t.IsSymm → p s = p t → s = t := by
    intro s t hs' ht' hst
    refine eq_of_out hs' ht' fun z => ?_
    have := congrFun hst (e z)
    simpa only [p, Equiv.symm_apply_apply] using this
  have key := image_mem_nhds_of_injOn (f := fun b => p (τ b)) hB
    (differentiableOn_pi.mpr fun k => hd _ _)
    (fun x hx y hy hxy => hinj hx hy (hp _ _ (hs x hx).1 (hs y hy).1 hxy)) hb₀
  refine ⟨_, hpc.continuousAt.preimage_mem_nhds key, ?_⟩
  rintro t ⟨b, hb, hbt⟩ ht -
  exact ⟨b, hb, hp _ _ (hs b hb).1 ht hbt⟩

end GlobalTheory.SiegelOpen
