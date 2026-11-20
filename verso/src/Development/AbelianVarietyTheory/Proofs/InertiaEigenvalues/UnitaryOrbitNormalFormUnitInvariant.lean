import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjTransposeVecMulVecSelf
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

/- English proof (translation)
Establish `hU : Unram F E` using `inferInstance`. Establish `hfin : FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`. Set `S : Submodule F E` to `{ carrier := {z | star z = z} add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [star_add, ha, hb] zero_mem' := by simp smul_mem' := by`. Introduce `c z hz`. Simplify using `only [Set.mem_setOf_eq] at *`.

Rewrite using `[Algebra.smul_def, star_mul, hz, hU.star_fix, mul_comm] }`. Establish `h1 : (Submodule.span F {(1 : E)}) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Simplify using `only [Set.mem_singleton_iff] at hz`.

Substitute `hz` using the available equality. Use `show star (1 : E) = 1`. Conclude with `star_one E`. Establish `hne : S ≠ ⊤`. Take `⟨z, hz⟩` from `hU.star_ne`.

Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `: z ∈ S` using `h ▸ Submodule.mem_top`. Conclude with `this`. Establish `hlt : Module.finrank F S < 2`.

Rewrite using `[← hU.finrank_eq]`. Conclude with `Submodule.finrank_lt hne`. Establish `hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1` using `finrank_span_singleton one_ne_zero`. Establish `heq : Submodule.span F {(1 : E)} = S` using `Submodule.eq_of_le_of_finrank_le h1 (by omega)`. Establish `hyS : y ∈ S` using `hy`.

Rewrite `hyS` using `[← heq, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `hyS`. Conclude with `⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩`.
-/
theorem exists_algebraMap_of_star_eq (y : E) (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  have hU : Unram F E := inferInstance
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  let S : Submodule F E :=
    { carrier := {z | star z = z}
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [star_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, star_mul, hz, hU.star_fix, mul_comm] }
  have h1 : (Submodule.span F {(1 : E)}) ≤ S := by
    rw [Submodule.span_le]; intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz
    show star (1 : E) = 1; exact star_one E
  have hne : S ≠ ⊤ := by
    obtain ⟨z, hz⟩ := hU.star_ne
    intro h; apply hz; have : z ∈ S := h ▸ Submodule.mem_top; exact this
  have hlt : Module.finrank F S < 2 := by
    rw [← hU.finrank_eq]; exact Submodule.finrank_lt hne
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hyS : y ∈ S := hy
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨c, hc⟩ := hyS
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

section Full
variable {r : ℕ} {k : Type} [CommRing k]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_cc (Y : Gl r k) (i j : Fin r) : full Y (Fin.castSucc i) (Fin.castSucc j) = Y.1 i j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_cl (Y : Gl r k) (i : Fin r) : full Y (Fin.castSucc i) (Fin.last r) = Y.2.1 i := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_lc (Y : Gl r k) (j : Fin r) : full Y (Fin.last r) (Fin.castSucc j) = Y.2.2.1 j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end Full

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step

open GlobalTheory.JR.Step.UNormal in

/- English proof (translation)
Introduce `F E _ _ _ _ _ r X a hX ha`. Establish `h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0)`. Use `congrArg (fun p => p.2.1 0) hX` as an intermediate fact. Simplify `this` using `[inv, mom, Hn.toGl, Inv.map]`. Establish `hl : X.2.2 = a.2.2`.

Use `congrArg (fun p => p.2.2) hX` as an intermediate fact. Simplify using `only [inv, Hn.toGl, Inv.map] at this`. Conclude with `(algebraMap F E).injective this`. Take `⟨ν, hν⟩` from `GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (a.2.1 0) ha`. Establish `ha0 : algebraMap F E (a.2.1 0) ≠ 0`.

Rewrite using `[map_ne_zero]`. Introduce `h`. Rewrite `ha` using `[h, norm_zero]`. Conclude with `zero_ne_one ha`. Establish `hνn : star (ν • eL r E) ⬝ᵥ (ν • eL r E) = ν * star ν`.

Simplify using `[eL, dotProduct, Pi.single_apply, mul_comm]`. Establish `hv : star X.2.1 ⬝ᵥ X.2.1 = star (ν • eL r E) ⬝ᵥ (ν • eL r E)`. Rewrite using `[h0, hνn, hν]`. Take `⟨g, hg⟩` from `GlobalTheory.unitary_transitive_of_norm F E (r + 1) X.2.1 _ hv (h0 ▸ ha0)`. Use `set M := g.1 * X.1.1 * star g.1 with hMdef`.

Establish `hM : Mᴴ = M` using `IsSelfAdjoint.conjugate X.1.2 g.1`. Establish `hMe : ∀ i j, M j i = star (M i j)`. Introduce `i j`. Use `congrFun (congrFun hM j) i` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply]`.

Conclude with `this.symm`. Take `⟨l', hl'⟩` from `exists_algebraMap_of_star_eq (F := F) (M (Fin.last r) (Fin.last r)) (hMe _ _).symm`. Establish `hsub : M.submatrix Fin.castSucc Fin.castSucc ∈ selfAdjoint (Matrix (Fin r) (Fin r) E)`. Rewrite using `[selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, hM]`. Use `⟨g, (⟨M.submatrix Fin.castSucc Fin.castSucc, hsub⟩, fun i => M (Fin.castSucc i) (Fin.last r), l'), ν, hν, ?_⟩` and prove the remaining obligations.

Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Apply `Subtype.ext show M = full _` to reduce the goal to its premises. Use extensionality with `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [full_ll]`. Simplify using `[Hn.toGl, hl']`. Consider the case `cast j => rw [full_lc]`. Simplify using `[Hn.toGl, hMe (Fin.castSucc j) (Fin.last r)]`.

Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [full_cl]`. Simplify using `[Hn.toGl]`. Consider the case `cast j => rw [full_cc]`.

Simplify using `[Hn.toGl]`. Conclude with `hg`. Conclude with `hl`.
-/
theorem uNormal : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a →
    ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E),
      ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  intro F E _ _ _ _ _ r X a hX ha
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun p => p.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have hl : X.2.2 = a.2.2 := by
    have := congrArg (fun p => p.2.2) hX
    simp only [inv, Hn.toGl, Inv.map] at this
    exact (algebraMap F E).injective this
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (a.2.1 0) ha
  have ha0 : algebraMap F E (a.2.1 0) ≠ 0 := by
    rw [map_ne_zero]
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hνn : star (ν • eL r E) ⬝ᵥ (ν • eL r E) = ν * star ν := by
    simp [eL, dotProduct, Pi.single_apply, mul_comm]
  have hv : star X.2.1 ⬝ᵥ X.2.1 = star (ν • eL r E) ⬝ᵥ (ν • eL r E) := by
    rw [h0, hνn, hν]
  obtain ⟨g, hg⟩ := GlobalTheory.unitary_transitive_of_norm F E (r + 1) X.2.1 _ hv (h0 ▸ ha0)
  set M := g.1 * X.1.1 * star g.1 with hMdef
  have hM : Mᴴ = M := IsSelfAdjoint.conjugate X.1.2 g.1
  have hMe : ∀ i j, M j i = star (M i j) := by
    intro i j
    have := congrFun (congrFun hM j) i
    rw [conjTranspose_apply] at this
    exact this.symm
  obtain ⟨l', hl'⟩ := exists_algebraMap_of_star_eq (F := F) (M (Fin.last r) (Fin.last r))
    (hMe _ _).symm
  have hsub : M.submatrix Fin.castSucc Fin.castSucc ∈ selfAdjoint (Matrix (Fin r) (Fin r) E) := by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, hM]
  refine ⟨g, (⟨M.submatrix Fin.castSucc Fin.castSucc, hsub⟩, fun i => M (Fin.castSucc i) (Fin.last r), l'), ν, hν, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    show M = full _
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [full_ll]; simp [Hn.toGl, hl']
      | cast j => rw [full_lc]; simp [Hn.toGl, hMe (Fin.castSucc j) (Fin.last r)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [full_cl]; simp [Hn.toGl]
      | cast j => rw [full_cc]; simp [Hn.toGl]
  · exact hg
  · exact hl

end GlobalTheory.JR.Step
