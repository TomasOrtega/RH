import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_smul_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Introduce `r X ξ f hadd hsm`. Establish `hsmul_mem : ∀ (α : 𝓞 E) (x : Fin r → E), x ∈ X.Λp ξ → (α : E) • x ∈ X.Λp ξ`. Introduce `α x hx`. Simplify using `only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢`. Take `⟨h1, h2⟩` from `hx`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `X.Λ.smul_mem α h1`. Rewrite `h3` using `[algebra_compatible_smul E α x]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `herm X.Gm ((α : E) • x) ξ = 0`. Express the relevant statement in the definitionally equal form `herm X.Gm x ξ = 0 at h2`.

Rewrite using `[herm_smul_left', h2, mul_zero]`. Set `N0 : Submodule (𝓞 E) (Fin r → E)` to `{ carrier := X.Λp ξ add_mem' := fun ha hb => (X.Λp ξ).add_mem ha hb zero_mem' := (X.Λp ξ).zero_mem smul_mem' := fun α x hx => by`. Rewrite using `[algebra_compatible_smul E α x]`. Conclude with `hsmul_mem α x hx }`. Set `fL : N0 →ₗ[𝓞 E] E` to `{ toFun := fun x => f x map_add' := fun x y => hadd x x.2 y y.2 map_smul' := fun α x => by`.

Express the relevant statement in the definitionally equal form `f (α • (x : Fin r → E)) = α • f x`. Rewrite using `[algebra_compatible_smul E α (x : Fin r → E), hsm α x x.2, Algebra.smul_def] }`. Take `⟨s, hsM, hspan, hli⟩` from `exists_linearIndependent E (X.Λp ξ : Set (Fin r → E))`. Establish `hli' : LinearIndepOn E id s` using `hli`. Set `B` to `Module.Basis.extend (K := E) (s := s) hli'`.

Set `F : (Fin r → E) →ₗ[E] E` to `B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0)`. Establish `hFs : ∀ v ∈ s, F v = f v`. Introduce `v hv`. Establish `hv' : v ∈ LinearIndepOn.extend hli' (Set.subset_univ s)` using `Module.Basis.subset_extend hli' hv`. Establish `h1` using `B.constr_basis E (fun v => if (v : Fin r → E) ∈ s then f v else 0) ⟨v, hv'⟩`.

Establish `h2 : B ⟨v, hv'⟩ = v` using `by simp [B, Module.Basis.coe_extend]`. Rewrite `h1` using `[h2]`. Express the relevant statement in the definitionally equal form `B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0) v = f v`. Rewrite using `[h1]`. Simplify using `[hv]`.

Use `⟨F, fun μ hμ => ?_⟩` and prove the remaining obligations. Establish `hμs : μ ∈ Submodule.span E s`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span hμ`. Take `⟨n, c, g, hsum⟩` from `Submodule.mem_span_set'.1 hμs`.

Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ c`. Establish `hd' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (d : 𝓞 E) • c i` using `fun i => RingHom.mem_rangeS.1 (hd i)`. Use `choose a ha using hd'`. Establish `hgM : ∀ i, ((g i : Fin r → E)) ∈ X.Λp ξ` using `fun i => hsM (g i).2`. Establish `hdE : algebraMap (𝓞 E) E (d : 𝓞 E) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2`.

Establish `hFμ : F μ = ∑ i, c i * f (g i)`. Rewrite using `[← hsum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hFs _ (g i).2, smul_eq_mul]`. Establish `hdμ : algebraMap (𝓞 E) E (d : 𝓞 E) • μ = ∑ i, algebraMap (𝓞 E) E (a i) • (g i : Fin r → E)`.

Rewrite using `[← hsum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ha i, smul_smul, Algebra.smul_def (d : 𝓞 E) (c i)]`. Establish `hmemd : algebraMap (𝓞 E) E (d : 𝓞 E) • μ ∈ N0` using `hsmul_mem (d : 𝓞 E) μ hμ`. Establish `hfd : f (algebraMap (𝓞 E) E (d : 𝓞 E) • μ) = ∑ i, algebraMap (𝓞 E) E (a i) * f (g i)`.

Establish `h1 : (⟨_, hmemd⟩ : N0) = ∑ i, a i • (⟨g i, hgM i⟩ : N0)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Rewrite using `[hdμ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[algebra_compatible_smul E (a i)]`. Establish `h2` using `congrArg fL h1`. Rewrite `h2` using `[map_sum]`. Express the relevant statement in the definitionally equal form `f _ = _ at h2`.

Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `h3 : algebraMap (𝓞 E) E (d : 𝓞 E) * f μ = algebraMap (𝓞 E) E (d : 𝓞 E) * F μ`.

Rewrite using `[← hsm (d : 𝓞 E) μ hμ, hfd, hFμ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ha i, Algebra.smul_def, mul_assoc]`. Conclude with `(mul_left_cancel₀ hdE h3).symm`.
-/
theorem sExt : SExt E := by
  intro r X ξ f hadd hsm
  classical
  have hsmul_mem : ∀ (α : 𝓞 E) (x : Fin r → E), x ∈ X.Λp ξ → (α : E) • x ∈ X.Λp ξ := by
    intro α x hx
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨?_, ?_⟩
    · have h3 := X.Λ.smul_mem α h1
      rwa [algebra_compatible_smul E α x] at h3
    · change herm X.Gm ((α : E) • x) ξ = 0
      change herm X.Gm x ξ = 0 at h2
      rw [herm_smul_left', h2, mul_zero]
  let N0 : Submodule (𝓞 E) (Fin r → E) :=
    { carrier := X.Λp ξ
      add_mem' := fun ha hb => (X.Λp ξ).add_mem ha hb
      zero_mem' := (X.Λp ξ).zero_mem
      smul_mem' := fun α x hx => by
        rw [algebra_compatible_smul E α x]
        exact hsmul_mem α x hx }
  let fL : N0 →ₗ[𝓞 E] E :=
    { toFun := fun x => f x
      map_add' := fun x y => hadd x x.2 y y.2
      map_smul' := fun α x => by
        change f (α • (x : Fin r → E)) = α • f x
        rw [algebra_compatible_smul E α (x : Fin r → E), hsm α x x.2, Algebra.smul_def] }
  obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent E (X.Λp ξ : Set (Fin r → E))
  have hli' : LinearIndepOn E id s := hli
  let B := Module.Basis.extend (K := E) (s := s) hli'
  let F : (Fin r → E) →ₗ[E] E := B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0)
  have hFs : ∀ v ∈ s, F v = f v := by
    intro v hv
    have hv' : v ∈ LinearIndepOn.extend hli' (Set.subset_univ s) := Module.Basis.subset_extend hli' hv
    have h1 := B.constr_basis E (fun v => if (v : Fin r → E) ∈ s then f v else 0) ⟨v, hv'⟩
    have h2 : B ⟨v, hv'⟩ = v := by simp [B, Module.Basis.coe_extend]
    rw [h2] at h1
    change B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0) v = f v
    rw [h1]
    simp [hv]
  refine ⟨F, fun μ hμ => ?_⟩
  have hμs : μ ∈ Submodule.span E s := by
    rw [hspan]
    exact Submodule.subset_span hμ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hμs
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ c
  have hd' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (d : 𝓞 E) • c i := fun i =>
    RingHom.mem_rangeS.1 (hd i)
  choose a ha using hd'
  have hgM : ∀ i, ((g i : Fin r → E)) ∈ X.Λp ξ := fun i => hsM (g i).2
  have hdE : algebraMap (𝓞 E) E (d : 𝓞 E) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have hFμ : F μ = ∑ i, c i * f (g i) := by
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFs _ (g i).2, smul_eq_mul]
  have hdμ : algebraMap (𝓞 E) E (d : 𝓞 E) • μ = ∑ i, algebraMap (𝓞 E) E (a i) • (g i : Fin r → E) := by
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, smul_smul, Algebra.smul_def (d : 𝓞 E) (c i)]
  have hmemd : algebraMap (𝓞 E) E (d : 𝓞 E) • μ ∈ N0 := hsmul_mem (d : 𝓞 E) μ hμ
  have hfd : f (algebraMap (𝓞 E) E (d : 𝓞 E) • μ) = ∑ i, algebraMap (𝓞 E) E (a i) * f (g i) := by
    have h1 : (⟨_, hmemd⟩ : N0) = ∑ i, a i • (⟨g i, hgM i⟩ : N0) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [hdμ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algebra_compatible_smul E (a i)]
    have h2 := congrArg fL h1
    rw [map_sum] at h2
    change f _ = _ at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h3 : algebraMap (𝓞 E) E (d : 𝓞 E) * f μ = algebraMap (𝓞 E) E (d : 𝓞 E) * F μ := by
    rw [← hsm (d : 𝓞 E) μ hμ, hfd, hFμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, Algebra.smul_def, mul_assoc]
  exact (mul_left_cancel₀ hdE h3).symm

end UnipMove
