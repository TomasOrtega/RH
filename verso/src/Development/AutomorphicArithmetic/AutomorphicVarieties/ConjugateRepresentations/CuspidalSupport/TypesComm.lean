import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Set `ev : Y → (V →ₗ[ℂ] ℂ)` to `fun y => (LinearMap.proj y).comp V.subtype`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Apply `Submodule.span_eq_top_of_ne_zero` to reduce the goal to its premises. Introduce `z hz`. Assume the negation of the conclusion as `h`.

Apply `hz` to reduce the goal to its premises. Use extensionality with `y`. Assume the negation of the conclusion as `hy`. Conclude with `h ⟨ev y, ⟨y, rfl⟩, hy⟩`. Set `b` to `Module.finBasis ℂ V`.

Establish `hc : ∀ i, ∃ c : Y →₀ ℂ, (c.sum fun z t => t • ev z) = b.coord i` using `fun i => Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)`. Use `choose c hc using hc`. Use `⟨_, b, c, fun f hf y => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (ev y) (b.sum_repr ⟨f, hf⟩)`. Rewrite `h` using `[map_sum]`.

Simplify using `only [map_smul] at h`. Use `h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Establish `h2 : b.repr ⟨f, hf⟩ i = (c i).sum fun z t => t * f z`. Rewrite using `[← b.coord_apply, ← hc i, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]`. Both sides reduce to the same expression.

Rewrite using `[h2, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Cj.S.exists_interp {Y : Type} (V : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (n : ℕ) (b : Fin n → V) (c : Fin n → Y →₀ ℂ),
      ∀ f ∈ V, ∀ y, f y = ∑ i, (b i).1 y * (c i).sum fun z t => t * f z := by
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  let b := Module.finBasis ℂ V
  have hc : ∀ i, ∃ c : Y →₀ ℂ, (c.sum fun z t => t • ev z) = b.coord i := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨_, b, c, fun f hf y => ?_⟩
  have h := congrArg (ev y) (b.sum_repr ⟨f, hf⟩)
  rw [map_sum] at h
  simp only [map_smul] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h2 : b.repr ⟨f, hf⟩ i = (c i).sum fun z t => t * f z := by
    rw [← b.coord_apply, ← hc i, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
    rfl
  rw [h2, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Introduce `E _ _ _ a V hV T hT φ hφ g`. Take `⟨n, b, c, hc⟩` from `UpperTheory.V.Cj.S.exists_interp V`. Set `R : archCompact E a → Module.End ℂ (Sm E a)` to `fun k => cptRep E a ((Cm.cptEq E a).symm k)`. Establish `hR : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (R k ψ).1 x = ψ.1 (x * infEmb E a k.1)`. Introduce `k ψ x`.

Take `⟨k, rfl⟩` from `(Cm.cptEq E a).surjective k`. Simplify using `only [R]`. Rewrite using `[MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]`. Both sides reduce to the same expression. Establish `hTR : ∀ (k : archCompact E a) (ψ : Sm E a), T (R k ψ) = R k (T ψ)` using `fun k ψ => LinearMap.congr_fun (hT _).eq ψ`.

Establish `hev : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z ψ : Sm E a).1 x = ∑ i, (b i).1 k * (c i).sum fun z t => t * ψ.1 (x * infEmb E a z.1)`. Introduce `k ψ x`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, Finsupp.sum]`. Establish `h1 : ∀ k : archCompact E a, R k φ = ∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z φ`. Introduce `k`.

Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Rewrite using `[hR, hev]`. Conclude with `hc _ (hφ x) k`. Establish `h2 : (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) = ∑ i, ((c i).sum fun z t => t * (T φ).1 (g * infEmb E a z.1)) • (b i).1`. Use function extensionality and compare the values at `k`.

Rewrite using `[← hR k, ← hTR, h1 k]`. Simplify using `only [map_sum, map_smul, hTR]`. Rewrite using `[hev]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]`. Rewrite using `[h2]`.

Conclude with `V.sum_mem fun i _ => V.smul_mem _ (b i).2`.
-/
theorem UpperTheory.V.Cj.S.typesComm :
    UpperTheory.V.Cj.S.TypesComm := by
  intro E _ _ _ a V hV T hT φ hφ g
  obtain ⟨n, b, c, hc⟩ := UpperTheory.V.Cj.S.exists_interp V
  let R : archCompact E a → Module.End ℂ (Sm E a) := fun k => cptRep E a ((Cm.cptEq E a).symm k)
  have hR : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (R k ψ).1 x = ψ.1 (x * infEmb E a k.1) := by
    intro k ψ x
    obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    simp only [R]
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  have hTR : ∀ (k : archCompact E a) (ψ : Sm E a), T (R k ψ) = R k (T ψ) := fun k ψ =>
    LinearMap.congr_fun (hT _).eq ψ
  have hev : ∀ (k : archCompact E a) (ψ : Sm E a) (x),
      (∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z ψ : Sm E a).1 x =
        ∑ i, (b i).1 k * (c i).sum fun z t => t * ψ.1 (x * infEmb E a z.1) := by
    intro k ψ x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, Finsupp.sum]
  have h1 : ∀ k : archCompact E a, R k φ = ∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z φ := by
    intro k
    refine Subtype.ext (funext fun x => ?_)
    rw [hR, hev]
    exact hc _ (hφ x) k
  have h2 : (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) =
      ∑ i, ((c i).sum fun z t => t * (T φ).1 (g * infEmb E a z.1)) • (b i).1 := by
    funext k
    rw [← hR k, ← hTR, h1 k]
    simp only [map_sum, map_smul, hTR]
    rw [hev]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h2]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
