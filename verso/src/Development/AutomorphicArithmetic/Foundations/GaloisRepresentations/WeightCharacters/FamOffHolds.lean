import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `E _ _ _ a τ W K ν d B hB U hU hBU hne τ' hτ'`. Take `⟨y₁, y₂, v₀, hv₀⟩` from `hne`. Use `set v := InfinitePlace.mk τ' with hv`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e, B y₁ y₂ (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `h1` using `(GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (UA E a → ℂ) 0).unique (y₁ := B y₁ y₂) (y₂ := 0) (fun u => hc u) (fun u => rfl)`. Conclude with `hv₀ (by rw [h1]; rfl)`. Establish `h : (AU.mk ⟨U, hU⟩).HasWt v.embedding (W v)`. Use `⟨isIrreducible_sqRep a (W v), B y₁ y₂ ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun x => hBU _ _ _, fun x u => ?_⟩` and prove the remaining obligations.

Use `LinearMap.congr_fun h0 (e v)` as an intermediate fact. Simplify `this` using `[MultilinearMap.toLinearMap]`. Establish `hx : x.1 ∈ infU E a` using `embU_le_infU _ x.2`. Establish `h1 : cEmb τ x.1 = 1` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 τ) (by rw [InfinitePlace.mk_embedding]; exact hτ'.symm)`. Establish `h2` using `hB.inf ⟨x.1, hx⟩ y₁ y₂ (GlobalTheory.CoefIrred.tenMul W (Function.update e v u))`.

Rewrite `h2` using `[rep_tenMul_update W v ⟨x.1, hx⟩ x.2, h1, one_mul, one_mul]`. Conclude with `h2.symm`. Break down `InfinitePlace.embedding_mk_eq τ' with e | e` into its components or cases. Establish `h'` using `h`. Rewrite `h'` using `[← Wt.at_embedding W v, e]`.

Conclude with `h'`. Establish `h2` using `h.conjugate`. Rewrite `h2` using `[← Wt.at_embedding W v, ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ']`. Conclude with `h2`.
-/
theorem famOff_holds : FamOff := by
  intro E _ _ _ a τ W K ν d B hB U hU hBU hne τ' hτ'
  classical
  obtain ⟨y₁, y₂, v₀, hv₀⟩ := hne
  set v := InfinitePlace.mk τ' with hv
  obtain ⟨e, he⟩ : ∃ e, B y₁ y₂ (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (UA E a → ℂ) 0).unique (y₁ := B y₁ y₂) (y₂ := 0)
      (fun u => hc u) (fun u => rfl)
    exact hv₀ (by rw [h1]; rfl)
  have h : (AU.mk ⟨U, hU⟩).HasWt v.embedding (W v) := by
    refine ⟨isIrreducible_sqRep a (W v), B y₁ y₂ ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun x => hBU _ _ _,
      fun x u => ?_⟩
    · have := LinearMap.congr_fun h0 (e v)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E a := embU_le_infU _ x.2
      have h1 : cEmb τ x.1 = 1 :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 τ) (by rw [InfinitePlace.mk_embedding]; exact hτ'.symm)
      have h2 := hB.inf ⟨x.1, hx⟩ y₁ y₂ (GlobalTheory.CoefIrred.tenMul W (Function.update e v u))
      rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2, h1, one_mul, one_mul] at h2
      exact h2.symm
  rcases InfinitePlace.embedding_mk_eq τ' with e | e
  · have h' := h
    rw [← Wt.at_embedding W v, e] at h'
    exact h'
  · have h2 := h.conjugate
    rw [← Wt.at_embedding W v, ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ'] at h2
    exact h2

/- English proof (translation)
Establish `e : (Finset.univ.filter fun j : Fin a => j.val < i + 1) = insert i (Finset.univ.filter fun j : Fin a => j.val < i)`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[psum, e, Finset.sum_insert (by simp), add_comm, psum]`.
-/
theorem psum_succ {a : ℕ} (κ : DomWeight a) (i : Fin a) : psum κ (i + 1) = psum κ i + κ.w i := by
  have e : (Finset.univ.filter fun j : Fin a => j.val < i + 1) = insert i (Finset.univ.filter fun j : Fin a => j.val < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [psum, e, Finset.sum_insert (by simp), add_comm, psum]

/- English proof (translation)
Introduce `hOff hSum E _ _ _ a τ W K ν d B hB U hU hBU hne`. Take `⟨mu, hmu⟩` from `GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU`. Use `⟨mu, ⟨hU, hmu, ?_⟩, fun τ' h => hasWeightAt_unique ⟨U, hU⟩ τ' (hmu τ') (hOff E a τ W K ν d B hB U hU hBU hne τ' h), fun i => ?_⟩` and prove the remaining obligations. Take `⟨y₁, y₂, v, hv⟩` from `hne`. Conclude with `⟨_, hBU y₁ y₂ v, hv, fun x hx => hB.fix x hx _ _ _⟩`.

Establish `h1` using `hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) i`. Establish `h2` using `hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) (i + 1)`. Rewrite `h2` using `[psum_succ, psum_succ]`. Rewrite using `[abs_le]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
theorem famWt_of : FamOff → FamSum → FamWt := by
  intro hOff hSum E _ _ _ a τ W K ν d B hB U hU hBU hne
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU
  refine ⟨mu, ⟨hU, hmu, ?_⟩, fun τ' h => hasWeightAt_unique ⟨U, hU⟩ τ' (hmu τ') (hOff E a τ W K ν d B hB U hU hBU hne τ' h),
    fun i => ?_⟩
  · obtain ⟨y₁, y₂, v, hv⟩ := hne
    exact ⟨_, hBU y₁ y₂ v, hv, fun x hx => hB.fix x hx _ _ _⟩
  · have h1 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) i
    have h2 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) (i + 1)
    rw [psum_succ, psum_succ] at h2
    rw [abs_le]
    push_cast
    omega

end UpperTheory.Gal.Wt

end
