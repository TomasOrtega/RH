import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.CoefIrred

/- English proof (translation)
Rewrite using `[or_iff_not_imp_left]`. Introduce `hne`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))`. Set `Φ : MultilinearMap K (fun τ => Module.End K (V τ)) W` to `∑ i, B.repr x i • t.compLinearMap fun τ => LinearMap.applyₗ (b τ (i τ))`. Establish `hΦ : ∀ T, Φ T = ∑ i, B.repr x i • t fun τ => T τ (b τ (i τ))`. Introduce `T`.

Simplify using `[Φ]`. Establish `h0 : U.mkQ.compMultilinearMap Φ = 0`. Use `MultilinearMap.ext_of_span_eq_top hρ fun g => ?_` and prove the remaining obligations. Take `⟨L, hL, hLU⟩` from `hU g`. Establish `: Φ (fun τ => ρ τ (g τ)) = L x`.

Rewrite using `[hΦ]`. Use `conv_rhs => rw [← B.sum_repr x]`. Simplify using `only [map_sum, map_smul, hB, hL]`. Simplify `hLU x hx` using `[this]`. Establish `hmem : ∀ T, Φ T ∈ U` using `fun T => by`.

Simplify using `using congrArg (fun m => m T) h0`. Establish `hj : ∀ j, B j ∈ U`. Introduce `j`. Establish `h1` using `hmem fun τ => ((b τ).coord (i₀ τ)).smulRight (b τ (j τ))`. Rewrite `h1` using `[hΦ, Finset.sum_eq_single i₀]`.

Simplify using `only [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul, ← hB] at h1`. Conclude with `(U.smul_mem_iff hi₀).1 h1`. Introduce `i _ hi`. Take `⟨τ, hτ⟩` from `Function.ne_iff.1 hi`. Rewrite using `[t.map_coord_zero τ, smul_zero]`.

Simplify using `[Finsupp.single_eq_of_ne hτ.symm]`. Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff, ← B.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hj j`.
-/
theorem eq_bot_or_top_of_tensor {K ι : Type} [Field K] [Fintype ι] {V κ G : ι → Type}
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module K (V τ)] [Fintype (∀ τ, κ τ)] {W : Type} [AddCommGroup W] [Module K W]
    (b : ∀ τ, Module.Basis (κ τ) K (V τ)) (t : MultilinearMap K V W) (B : Module.Basis (∀ τ, κ τ) K W)
    (hB : ∀ i, B i = t fun τ => b τ (i τ)) (ρ : ∀ τ, G τ → Module.End K (V τ))
    (hρ : ∀ τ, Submodule.span K (Set.range (ρ τ)) = ⊤) (U : Submodule K W)
    (hU : ∀ g : ∀ τ, G τ, ∃ L : Module.End K W,
      (∀ f, L (t f) = t fun τ => ρ τ (g τ) (f τ)) ∧ ∀ x ∈ U, L x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  let Φ : MultilinearMap K (fun τ => Module.End K (V τ)) W :=
    ∑ i, B.repr x i • t.compLinearMap fun τ => LinearMap.applyₗ (b τ (i τ))
  have hΦ : ∀ T, Φ T = ∑ i, B.repr x i • t fun τ => T τ (b τ (i τ)) := by
    intro T
    simp [Φ]
  have h0 : U.mkQ.compMultilinearMap Φ = 0 := by
    refine MultilinearMap.ext_of_span_eq_top hρ fun g => ?_
    obtain ⟨L, hL, hLU⟩ := hU g
    have : Φ (fun τ => ρ τ (g τ)) = L x := by
      rw [hΦ]
      conv_rhs => rw [← B.sum_repr x]
      simp only [map_sum, map_smul, hB, hL]
    simpa [this] using hLU x hx
  have hmem : ∀ T, Φ T ∈ U := fun T => by
    simpa using congrArg (fun m => m T) h0
  have hj : ∀ j, B j ∈ U := by
    intro j
    have h1 := hmem fun τ => ((b τ).coord (i₀ τ)).smulRight (b τ (j τ))
    rw [hΦ, Finset.sum_eq_single i₀] at h1
    · simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, one_smul, ← hB] at h1
      exact (U.smul_mem_iff hi₀).1 h1
    · intro i _ hi
      obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hi
      rw [t.map_coord_zero τ, smul_zero]
      simp [Finsupp.single_eq_of_ne hτ.symm]
    · simp
  rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hj j

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ}

def tenMul (lam : ι → DomWeight n) : MultilinearMap K (fun τ => nablaSq K n (lam τ)) (VV K lam) :=
  haveI := Classical.decEq ι
  ((MultilinearMap.mkPiAlgebra K ι (Pol K ι n)).compLinearMap fun τ =>
    (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap ∘ₗ (nablaSq K n (lam τ)).subtype).codRestrict (VV K lam)
    fun f => Submodule.subset_span ⟨fun τ => f τ, fun τ => (f τ).2, by simp⟩

/- English proof (translation)
Conclude with `(MultilinearMap.mkPiAlgebra_apply (R := K) _).trans rfl`.
-/
theorem tenMul_coe (lam : ι → DomWeight n) (f : ∀ τ, nablaSq K n (lam τ)) :
    (tenMul lam f : Pol K ι n) = ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) K) := by
  classical
  exact (MultilinearMap.mkPiAlgebra_apply (R := K) _).trans rfl

def ssBasis (K : Type) [Field K] (mu : DomWeight n) :
    Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) K (nablaSq K n mu) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.2.1)

/- English proof (translation)
Simplify using `only [ssBasis, ssB, Module.Basis.map_apply, Module.Basis.span_apply]`. Both sides reduce to the same expression.
-/
theorem ssBasis_coe (mu : DomWeight n) (i : Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) :
    (ssBasis K mu i : MvPolynomial (Fin n × Fin n) K) = ssB K mu.natW i := by
  simp only [ssBasis, ssB, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/- English proof (translation)
Introduce `ι _ n lam U hU`. Use `eq_bot_or_top_of_tensor (G := fun _ => Matrix.unitaryGroup (Fin n) ℂ) (fun τ => ssBasis ℂ (lam τ)) (tenMul lam) (bVV ℂ lam) (fun i => ?_) (fun τ => smallRep (unitaryIncl n) (lam τ)) (fun τ => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (isIrreducible_smallRep_u …` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[bVV_coe, tenMul_coe, bVVfun]`. Simplify using `only [ssBasis_coe]`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[tenMul_coe]`. Express the relevant statement in the definitionally equal form `actP lam _ (tenMul lam f : Pol ℂ ι n) = _`. Rewrite using `[tenMul_coe, actTen]`. Both sides reduce to the same expression.
-/
theorem vv_irreducible_unitary :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n) (U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam)), (∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ x ∈ U, Formalism.L2.DIV.rhoK lam g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro ι _ n lam U hU
  refine eq_bot_or_top_of_tensor (G := fun _ => Matrix.unitaryGroup (Fin n) ℂ)
    (fun τ => ssBasis ℂ (lam τ)) (tenMul lam) (bVV ℂ lam) (fun i => ?_)
    (fun τ => smallRep (unitaryIncl n) (lam τ))
    (fun τ => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (isIrreducible_smallRep_unitary n (lam τ)))
    U fun g => ⟨rhoK lam fun τ => unitaryIncl n (g τ), fun f => ?_, hU _ fun τ => (g τ).2⟩
  · apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  · apply Subtype.ext
    rw [tenMul_coe]
    change actP lam _ (tenMul lam f : Pol ℂ ι n) = _
    rw [tenMul_coe, actTen]
    rfl

end GlobalTheory.CoefIrred
