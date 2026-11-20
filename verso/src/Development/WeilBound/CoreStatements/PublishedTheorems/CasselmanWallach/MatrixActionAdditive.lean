import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Unfold `casimirK`. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Establish `hs : adjSign ε a b = 1` using `by simp [adjSign, hab]`.

Rewrite using `[hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]`.
-/
theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
/- English proof (translation)
Introduce `n ε V _ _ E hGl hU hLF`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨S, hfin, hvS, hstab⟩` from `hLF v`. Establish `hK : ∀ w ∈ S, casimirK ε E w ∈ S`.

Introduce `w hw`. Unfold `casimirK`. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.1 hb).2`.

Conclude with `hstab a b hab.symm _ (hstab b a hab _ hw)`. Set `T : S →ₗ[ℂ] S` to `(casimirK ε E).restrict hK`. Establish `hT : T.IsSymmetric`. Introduce `x y`. Conclude with `casK_symm hU x y`.

Establish `hn : Module.finrank ℂ S = Module.finrank ℂ S` using `rfl`. Establish `hsum` using `(hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩`. Establish `hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V)`. Establish `h0` using `congrArg Subtype.val hsum`. Simplify using `using h0.symm`.

Rewrite using `[hv]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)` and prove the remaining obligations. Use `show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)`. Conclude with `congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)`.
-/
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
