import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Introduce `A _ Γ _ _ c ε hc hc1 hε`. Use `haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)`. Set `f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A)` to `{ toFun := coord c ε map_add' := by`. Introduce `x y`. Use function extensionality and compare the values at `i`.

Simplify using `only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := by`. Introduce `a x`. Use function extensionality and compare the values at `i`.

Simplify using `only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]`. Use `ring }`. Establish `hf : ∀ w, f w = coord c ε w` using `fun w => rfl`. Establish `hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A`. Use extensionality with `w`.

Rewrite using `[LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]`. Establish `hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i'`. Introduce `i i' h`. Rewrite using `[← mk_rep i, ← mk_rep i', h]`. Establish `hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i`.

Introduce `i i' h`. Establish `e1 : i' = i`. Rewrite using `[← mk_rep i', ← mk_rep i, h]`. Conclude with `((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm`. Substitute `e1` using the available equality.

Establish `e2 : c * rep i' = 1 * rep i'` using `by rw [← h, one_mul]`. Conclude with `hc1 (mul_right_cancel e2)`. Establish `hsurj : Function.Surjective f`. Introduce `v`. Use `⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i0`. Rewrite using `[hf, coord]`. Simplify using `only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Rewrite using `[Finset.sum_eq_single i0, Finset.sum_eq_zero]`. Simplify using the standard rewrite rules.

Introduce `i _`. Rewrite using `[if_neg (hcrep i0 i)]`. Introduce `i _ hi`. Rewrite using `[if_neg (fun h => hi (hrepinj i i0 h))]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i0) h`. Set `e : Rq A c ε ≃ₗ[A] (Qc c → A)` to `(Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj`. Conclude with `⟨e, fun w => rfl⟩`.
-/
theorem UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∃ e : Rq A c ε ≃ₗ[A] (Qc c → A), ∀ w : MonoidAlgebra A Γ, e (cls A c ε w) = coord c ε w := by
  intro A _ Γ _ _ c ε hc hc1 hε
  classical
  haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)
  let f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A) :=
    { toFun := coord c ε
      map_add' := by
        intro x y
        funext i
        simp only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply]
        ring }
  have hf : ∀ w, f w = coord c ε w := fun w => rfl
  have hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A := by
    ext w
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]
  have hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i' := by
    intro i i' h
    rw [← mk_rep i, ← mk_rep i', h]
  have hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i := by
    intro i i' h
    have e1 : i' = i := by
      rw [← mk_rep i', ← mk_rep i, h]
      exact ((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm
    subst e1
    have e2 : c * rep i' = 1 * rep i' := by rw [← h, one_mul]
    exact hc1 (mul_right_cancel e2)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩
    funext i0
    rw [hf, coord]
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg (hcrep i0 i)]
    · intro i _ hi
      rw [if_neg (fun h => hi (hrepinj i i0 h))]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  let e : Rq A c ε ≃ₗ[A] (Qc c → A) :=
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun w => rfl⟩
