import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.GoodBaseChange

/- English proof (translation)
Introduce `p _ A _ B _ _ r K₁ K₀ _ _ _ _ d hd`. Introduce `C _ _ hC w hw k`. Use `letI : Algebra A C := Algebra.compHom C (algebraMap A B)`. Use `haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `e₁` to `AlgebraTensorModule.cancelBaseChange A B C C K₁`.

Set `e₀` to `AlgebraTensorModule.cancelBaseChange A B C C K₀`. Establish `hnat : ∀ v, e₀ ((d.baseChange B).lTensor C v) = d.lTensor C (e₁ v)`. Introduce `v`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b x`. Simplify using `[e₀, e₁, LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]`.

Consider the case `add y y' h h' => simp only [tmul_add, map_add, h, h']`. Consider the case `add v v' h h' => simp only [map_add, h, h']`. Establish `hw' : d.lTensor C (e₁ w) = 0` using `by rw [← hnat, hw, map_zero]`. Establish `hmem` using `hd C hC (e₁ w) hw' k`. Establish `hsmul : r k • e₁ w = e₁ (algebraMap A B (r k) • w)`.

Rewrite using `[← algebraMap_smul C (algebraMap A B (r k)) w, map_smul, algebraMap_smul]`. Both sides reduce to the same expression. Establish `key : ∀ u : C ⊗[A] LinearMap.ker d, e₁.symm ((LinearMap.ker d).subtype.lTensor C u) ∈ LinearMap.range ((LinearMap.ker (d.baseChange B)).subtype.lTensor C)`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c x`. Establish `hx : (1 : B) ⊗ₜ[A] (x : K₁) ∈ LinearMap.ker (d.baseChange B)`. Simplify using `[LinearMap.baseChange_tmul, x.2]`. Use `⟨c ⊗ₜ ⟨_, hx⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[e₁, AlgebraTensorModule.cancelBaseChange_symm_tmul]`. Consider the case `add u u' h h' => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ h h'`. Take `⟨u, hu⟩` from `hmem`. Use `key u` as an intermediate fact.

Rewrite `this` using `[hu, hsmul, LinearEquiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem good_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A) (K₁ K₀ : Type) [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀] (d : K₁ →ₗ[A] K₀), Good p r d → Good p (fun k => algebraMap A B (r k)) (d.baseChange B) := by
  intro p _ A _ B _ _ r K₁ K₀ _ _ _ _ d hd
  intro C _ _ hC w hw k
  letI : Algebra A C := Algebra.compHom C (algebraMap A B)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁ := AlgebraTensorModule.cancelBaseChange A B C C K₁
  let e₀ := AlgebraTensorModule.cancelBaseChange A B C C K₀
  have hnat : ∀ v, e₀ ((d.baseChange B).lTensor C v) = d.lTensor C (e₁ v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [e₀, e₁, LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
      | add y y' h h' => simp only [tmul_add, map_add, h, h']
    | add v v' h h' => simp only [map_add, h, h']
  have hw' : d.lTensor C (e₁ w) = 0 := by rw [← hnat, hw, map_zero]
  have hmem := hd C hC (e₁ w) hw' k
  have hsmul : r k • e₁ w = e₁ (algebraMap A B (r k) • w) := by
    rw [← algebraMap_smul C (algebraMap A B (r k)) w, map_smul, algebraMap_smul]
    rfl
  have key : ∀ u : C ⊗[A] LinearMap.ker d,
      e₁.symm ((LinearMap.ker d).subtype.lTensor C u) ∈
        LinearMap.range ((LinearMap.ker (d.baseChange B)).subtype.lTensor C) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      have hx : (1 : B) ⊗ₜ[A] (x : K₁) ∈ LinearMap.ker (d.baseChange B) := by
        simp [LinearMap.baseChange_tmul, x.2]
      refine ⟨c ⊗ₜ ⟨_, hx⟩, ?_⟩
      simp [e₁, AlgebraTensorModule.cancelBaseChange_symm_tmul]
    | add u u' h h' => rw [map_add, map_add]; exact Submodule.add_mem _ h h'
  obtain ⟨u, hu⟩ := hmem
  have := key u
  rw [hu, hsmul, LinearEquiv.symm_apply_apply] at this
  exact this

end GlobalTheory.CompanionTheory.GoodBaseChange
