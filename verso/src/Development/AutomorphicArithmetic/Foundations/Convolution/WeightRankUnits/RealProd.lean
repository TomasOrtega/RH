import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealSigned

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ n a b hab e he lam`. Substitute `hab` using the available equality. Use `choose ι hι l₁ l₂ ε hε hinf hid using fun v : InfinitePlace E => UpperTheory.ConvolutionTheory.G2.realSigned a b (lam v) (e v) (he v)`. Set `s : ∀ v, ι v → ℤˣ` to `fun v j => if ε v j = 1 then 1 else -1`. Establish `hs : ∀ v j, ((s v j : ℤ) : ℂ) = ε v j`.

Introduce `v j`. Distinguish the cases in `h : ε v j = 1`. Simplify using `[s, h]`. Establish `h'` using `(hε v j).resolve_left h`. Simplify using `only [s, if_neg h]`.

Rewrite using `[h']`. Simplify using the standard rewrite rules. Use `⟨∀ v, ι v, inferInstance, fun i v => l₁ v (i v), fun i v => l₂ v (i v), fun i => ∏ v, s v (i v), fun i v => hinf v (i v), ?_⟩` and prove the remaining obligations. Introduce and unpack `P₁ P₂ ⟨hm₁, hd₁, hs₁, hr₁⟩ ⟨hm₂, hd₂, hs₂, hr₂⟩ hc`. Establish `key : ∀ v : InfinitePlace E, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v * (starRingEnd ℂ) (chAt (lam v) ((P₁ * P₂).map v.embedding)) = ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) (P₁.map v.embedding)) * (starRingEnd ℂ) (chAt (l₂ v j) (P₂.map v.embedding))`.

Introduce `v`. Establish `hR : resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding (resultant P₁ P₂)`. Rewrite using `[natDegree_map, natDegree_map, resultant_map_map]`. Establish `h` using `hid v (P₁.map v.embedding) (P₂.map v.embedding) (hm₁.map _) (hm₂.map _) (by rw [natDegree_map, hd₁]) (by rw [natDegree_map, hd₂]) (by rw [← Polynomial.map_mul]; exact (hs₁.mul hs₂ hc).map) (by`. Introduce `z hz`.

Rewrite `hz` using `[roots_mul ((hm₁.map _).mul (hm₂.map _)).ne_zero, Multiset.mem_add]`. Conclude with `hz.elim (hr₁ _ z) (hr₂ _ z))`. Rewrite `h` using `[hR]`. Rewrite using `[Polynomial.map_mul]`. Conclude with `h`.

Unfold `chW`. Rewrite using `[← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ => key v, Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib]`. Simplify using `only [Units.coe_prod, Int.cast_prod, hs]`.
-/
theorem UpperTheory.ConvolutionTheory.G2.realProd :
    UpperTheory.ConvolutionTheory.G2.RealProd := by
  intro E _ _ _ n a b hab e he lam
  subst hab
  choose ι hι l₁ l₂ ε hε hinf hid using fun v : InfinitePlace E => UpperTheory.ConvolutionTheory.G2.realSigned a b (lam v) (e v) (he v)
  let s : ∀ v, ι v → ℤˣ := fun v j => if ε v j = 1 then 1 else -1
  have hs : ∀ v j, ((s v j : ℤ) : ℂ) = ε v j := by
    intro v j
    by_cases h : ε v j = 1
    · simp [s, h]
    · have h' := (hε v j).resolve_left h
      simp only [s, if_neg h]
      rw [h']; simp
  refine ⟨∀ v, ι v, inferInstance, fun i v => l₁ v (i v), fun i v => l₂ v (i v), fun i => ∏ v, s v (i v),
    fun i v => hinf v (i v), ?_⟩
  rintro P₁ P₂ ⟨hm₁, hd₁, hs₁, hr₁⟩ ⟨hm₂, hd₂, hs₂, hr₂⟩ hc
  have key : ∀ v : InfinitePlace E, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v *
      (starRingEnd ℂ) (chAt (lam v) ((P₁ * P₂).map v.embedding)) =
      ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) (P₁.map v.embedding)) *
        (starRingEnd ℂ) (chAt (l₂ v j) (P₂.map v.embedding)) := by
    intro v
    have hR : resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding (resultant P₁ P₂) := by
      rw [natDegree_map, natDegree_map, resultant_map_map]
    have h := hid v (P₁.map v.embedding) (P₂.map v.embedding) (hm₁.map _) (hm₂.map _)
      (by rw [natDegree_map, hd₁]) (by rw [natDegree_map, hd₂])
      (by rw [← Polynomial.map_mul]; exact (hs₁.mul hs₂ hc).map)
      (by
        intro z hz
        rw [roots_mul ((hm₁.map _).mul (hm₂.map _)).ne_zero, Multiset.mem_add] at hz
        exact hz.elim (hr₁ _ z) (hr₂ _ z))
    rw [hR] at h
    rw [Polynomial.map_mul]
    exact h
  unfold chW
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ => key v, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Units.coe_prod, Int.cast_prod, hs]
