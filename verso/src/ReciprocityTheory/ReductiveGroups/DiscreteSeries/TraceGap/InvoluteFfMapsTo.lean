import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AlgebraMapInvFf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Simplify using `only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢`. Introduce `i a hia`. Establish `h` using `LinearMap.congr_fun (fock_inv_cm i a) x`. Simplify using `only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply, hx i a hia, map_zero] at h`. Conclude with `neg_eq_zero.mp h.symm`.
-/
theorem involute_physFock {x : Fock n} (hx : x ∈ physFock ε) : CliffordAlgebra.involute x ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i a hia
  have h := LinearMap.congr_fun (fock_inv_cm i a) x
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply, hx i a hia, map_zero] at h
  exact neg_eq_zero.mp h.symm

/- English proof (translation)
Introduce `x hx`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Conclude with `involute_physFock (ff_physFock k hx)`.
-/
theorem involute_ff_mapsTo (k : Matrix (Fin n) (Fin n) ℂ) :
    ∀ x ∈ physFock ε, (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap) x ∈ physFock ε := by
  intro x hx
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  exact involute_physFock (ff_physFock k hx)

/- English proof (translation)
Simplify using `only [physFock, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `i a hia`. Establish `hm : finProdFinEquiv (i, a) ∉ S.1`. Introduce `h`. Use `S.2 h` as an intermediate fact.

Rewrite `this` using `[lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply]`. Conclude with `hia this.2`. Conclude with `lf_cm_basis_of_not_mem (x := (i, a)) hm`.
-/
theorem physWedge_mem (S : LfIdx ε) : fockBasis n S.1 ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  have hm : finProdFinEquiv (i, a) ∉ S.1 := by
    intro h
    have := S.2 h
    rw [lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply] at this
    exact hia this.2
  exact lf_cm_basis_of_not_mem (x := (i, a)) hm

/- English proof (translation)
Apply `LinearIndependent.of_comp (physFock ε).subtype` to reduce the goal to its premises. Conclude with `(fockBasis n).linearIndependent.comp _ Subtype.val_injective`.
-/
theorem physWedge_li :
    LinearIndependent ℂ (fun S : LfIdx ε => (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε)) := by
  apply LinearIndependent.of_comp (physFock ε).subtype
  exact (fockBasis n).linearIndependent.comp _ Subtype.val_injective

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression.

Establish `h0 : (fockBasis n).repr y T = 0`. Assume the negation of the conclusion as `h0`. Conclude with `h (gc_support_phys y.2 (by rwa [Module.Basis.coord_apply]))`. Rewrite using `[h0, zero_smul]`. Use `_ = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • fockBasis n S.1 := Finset.sum_subtype _ (fun T => by simp) _`.
-/
theorem phys_eq_sum (y : physFock ε) :
    (y : Fock n) = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • fockBasis n S.1 := by
  calc (y : Fock n) = ∑ T, (fockBasis n).repr y T • fockBasis n T := ((fockBasis n).sum_repr _).symm
    _ = ∑ T ∈ univ.filter (fun T => T ⊆ lfPhysModes ε), (fockBasis n).repr y T • fockBasis n T := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs with h
        · rfl
        · have h0 : (fockBasis n).repr y T = 0 := by
            by_contra h0
            exact h (gc_support_phys y.2 (by rwa [Module.Basis.coord_apply]))
          rw [h0, zero_smul]
    _ = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • fockBasis n S.1 :=
        Finset.sum_subtype _ (fun T => by simp) _

/- English proof (translation)
Introduce `y _`. Establish `hy : y = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `conv_lhs => rw [phys_eq_sum y]`. Rewrite using `[Submodule.coe_sum]`.

Both sides reduce to the same expression. Rewrite using `[hy]`. Conclude with `Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)`.
-/
theorem physWedge_span :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun S : LfIdx ε => (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε))) := by
  intro y _
  have hy : y = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε) := by
    apply Subtype.ext
    conv_lhs => rw [phys_eq_sum y]
    rw [Submodule.coe_sum]
    rfl
  rw [hy]
  exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

def physBasis (ε : Fin n → Bool) : Module.Basis (LfIdx ε) ℂ (physFock ε) :=
  Module.Basis.mk physWedge_li physWedge_span

/- English proof (translation)
Simplify using `[physBasis]`.
-/
theorem physBasis_coe (S : LfIdx ε) : (physBasis ε S : Fock n) = fockBasis n S.1 := by
  simp [physBasis]

/- English proof (translation)
Establish `: Finsupp.lapply S ∘ₗ (physBasis ε).repr.toLinearMap = Finsupp.lapply S.1 ∘ₗ (fockBasis n).repr.toLinearMap ∘ₗ (physFock ε).subtype`. Use `(physBasis ε).ext fun T => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, Submodule.subtype_apply, physBasis_coe, Finsupp.single_apply, Subtype.ext_iff]`. Conclude with `LinearMap.congr_fun this y`.
-/
theorem physBasis_repr (y : physFock ε) (S : LfIdx ε) :
    (physBasis ε).repr y S = (fockBasis n).repr y S.1 := by
  have : Finsupp.lapply S ∘ₗ (physBasis ε).repr.toLinearMap =
      Finsupp.lapply S.1 ∘ₗ (fockBasis n).repr.toLinearMap ∘ₗ (physFock ε).subtype := by
    refine (physBasis ε).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      Submodule.subtype_apply, physBasis_coe, Finsupp.single_apply, Subtype.ext_iff]
  exact LinearMap.congr_fun this y

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => simp [ExteriorAlgebra.ιMulti_zero_apply]`. Consider the case `succ p ih`. Rewrite using `[ExteriorAlgebra.ιMulti_succ_apply, map_mul, ih, CliffordAlgebra.involute_ι, mul_smul_comm, neg_mul, pow_succ, mul_neg_one, neg_smul, smul_neg]`.
-/
theorem involute_ιMulti (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute (ExteriorAlgebra.ιMulti ℂ p v) = ((-1 : ℂ) ^ p) • ExteriorAlgebra.ιMulti ℂ p v := by
  induction p with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ p ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, ih, CliffordAlgebra.involute_ι, mul_smul_comm, neg_mul,
      pow_succ, mul_neg_one, neg_smul, smul_neg]

/- English proof (translation)
Rewrite using `[fockBasis_eq, involute_ιMulti]`.
-/
theorem involute_basis (S : Finset (Fin (n * n))) :
    CliffordAlgebra.involute (fockBasis n S) = ((-1 : ℂ) ^ S.card) • fockBasis n S := by
  rw [fockBasis_eq, involute_ιMulti]

/- English proof (translation)
Establish `hterm : ∀ S : LfIdx ε, (physBasis ε).repr (((CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)) (physBasis ε S)) S = (-1 : ℂ) ^ S.1.card * ffMat ε k S.1 S.1`. Introduce `S`. Rewrite using `[physBasis_repr, LinearMap.coe_restrict_apply, physBasis_coe]`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[← ff_involute, involute_basis, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply]`.

Rewrite using `[strPhys, LinearMap.trace_eq_matrix_trace ℂ (physBasis ε), Matrix.trace]`. Simplify using `only [Matrix.diag, LinearMap.toMatrix_apply, hterm]`. Conclude with `Finset.sum_subtype _ (fun S => by simp [IsPhysSet, Finset.subset_iff, lfPhysModes, IsPhys]) _`.
-/
theorem strPhys_eq_trace (k : Matrix (Fin n) (Fin n) ℂ) :
    strPhys ε k = LinearMap.trace ℂ (physFock ε)
      ((CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)) := by
  have hterm : ∀ S : LfIdx ε, (physBasis ε).repr
      (((CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k))
        (physBasis ε S)) S = (-1 : ℂ) ^ S.1.card * ffMat ε k S.1 S.1 := by
    intro S
    rw [physBasis_repr, LinearMap.coe_restrict_apply, physBasis_coe]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [← ff_involute, involute_basis, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, ffMat,
      LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply]
  rw [strPhys, LinearMap.trace_eq_matrix_trace ℂ (physBasis ε), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hterm]
  exact Finset.sum_subtype _ (fun S => by simp [IsPhysSet, Finset.subset_iff, lfPhysModes, IsPhys]) _

end ReciprocityTheory.ChartRestriction.DS.TRGap
