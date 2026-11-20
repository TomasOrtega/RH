import Formalism.LatticeRigidity.StatementD
import Mathlib

namespace Formalism.SA.P

open Matrix Polynomial
open scoped ComplexOrder

section TracePow

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/- English proof (translation)
Use `first`. Consider the case `exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)`. Consider the case `exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.iSupIndep_maxGenEigenspace f)`. Consider the case `exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)`. Consider the case `exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent (Module.End.independent_maxGenEigenspace f)`.

Consider the case `exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt (Module.End.independent_maxGenEigenspace f)`. Consider the case `exact (Module.End.independent_maxGenEigenspace f).finite_ne_bot`. Consider the case `exact (Module.End.iSupIndep_maxGenEigenspace f).finite_ne_bot`.
-/
theorem finite_eig (f : Module.End K V) : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := by
  first
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.iSupIndep_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt
      (Module.End.independent_maxGenEigenspace f)
  | exact (Module.End.independent_maxGenEigenspace f).finite_ne_bot
  | exact (Module.End.iSupIndep_maxGenEigenspace f).finite_ne_bot

/- English proof (translation)
Establish `h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)` using `Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ`. Establish `hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ, (((f.restrict h1) ^ m) z : V) = (f ^ m) z`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro z`.

Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `z`. Use `first`. Consider the case `rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]`.

Consider the case `rw [pow_succ', LinearMap.mul_apply, pow_succ', LinearMap.mul_apply, ← ih]`. Both sides reduce to the same expression. Establish `hg : (f ^ j).restrict (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) = (f.restrict h1) ^ j` using `LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)`. Rewrite using `[hg]`. Establish `hxy : IsNilpotent (f.restrict h1 - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ)`.

Use `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1` and compare the differences between its conclusion and the goal. Use `LinearMap.ext fun z => Subtype.ext ?_` and prove the remaining obligations. Use `first`. Consider the case `rfl`. Consider the case `simp [LinearMap.restrict_apply]`.

Consider the case `simp`. Generalize the expression as in `f.restrict h1 = x at hxy ⊢`. Establish `hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ)` using `(Algebra.commutes μ x).symm`. Establish `hnil : IsNilpotent (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j)`. Rewrite using `[← hc.geom_sum₂_mul]`.

Establish `hcomm : Commute (∑ i ∈ Finset.range j, x ^ i * (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i)) (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ)`. Use `Commute.sub_right ?_ ?_` and prove the remaining obligations. Use `first`. Consider the case `exact Commute.sum_left _ _ _ fun i _ => ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)`. Consider the case `exact Commute.sum_left fun i _ => ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)`.

Use `first`. Consider the case `exact Commute.sum_left _ _ _ fun i _ => (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)`. Consider the case `exact Commute.sum_left fun i _ => (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)`. Use `first`. Consider the case `exact hcomm.isNilpotent_mul_left hxy`.

Consider the case `exact hcomm.isNilpotent_mul_right hxy`. Consider the case `exact hcomm.symm.isNilpotent_mul_left hxy`. Consider the case `exact hcomm.symm.isNilpotent_mul_right hxy`. Establish `h0 : LinearMap.trace K _ (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0` using `by first`. Consider the case `exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero`.

Consider the case `exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Rewrite using `[h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))), Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]`.
-/
theorem trace_pow_restrict_maxGen (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ,
      (((f.restrict h1) ^ m) z : V) = (f ^ m) z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      first
      | rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      | rw [pow_succ', LinearMap.mul_apply, pow_succ', LinearMap.mul_apply, ← ih]
      rfl
  have hg : (f ^ j).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) =
      (f.restrict h1) ^ j :=
    LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)
  rw [hg]
  have hxy : IsNilpotent (f.restrict h1 -
      algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
    convert Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1
    refine LinearMap.ext fun z => Subtype.ext ?_
    first
    | rfl
    | simp [LinearMap.restrict_apply]
    | simp
  generalize f.restrict h1 = x at hxy ⊢
  have hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) :=
    (Algebra.commutes μ x).symm
  have hnil : IsNilpotent
      (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) := by
    rw [← hc.geom_sum₂_mul]
    have hcomm : Commute (∑ i ∈ Finset.range j, x ^ i *
        (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i))
        (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      refine Commute.sub_right ?_ ?_
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
        | exact Commute.sum_left fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
        | exact Commute.sum_left fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
    first
    | exact hcomm.isNilpotent_mul_left hxy
    | exact hcomm.isNilpotent_mul_right hxy
    | exact hcomm.symm.isNilpotent_mul_left hxy
    | exact hcomm.symm.isNilpotent_mul_right hxy
  have h0 : LinearMap.trace K _ (x ^ j -
      (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0 := by
    first
    | exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    | exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))),
    Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤`. Use `eq_top_iff.mpr ?_` and prove the remaining obligations. Use `first`. Consider the case `rw [← Module.End.iSup_maxGenEigenspace_eq_top f]`. Consider the case `rw [← Module.End.iSup_maxGenEigenspace_eq_top (f := f)]`.

Use `iSup_le fun μ => ?_` and prove the remaining obligations. Distinguish the cases in `hμ : f.maxGenEigenspace μ = ⊥`. Rewrite using `[hμ]`. Conclude with `bot_le`. Conclude with `le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ) μ (by simpa using hμ) le_rfl`.

Establish `hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K))` using `by first`. Consider the case `exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective`. Consider the case `exact (Module.End.iSupIndep_maxGenEigenspace f).comp Subtype.val_injective`. Establish `hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)` using `fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ`. Establish `key` using `LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm`.

Establish `htr` using `LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j) (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))`. Conclude with `htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))`.
-/
theorem trace_pow_eq_sum (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  classical
  have htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤ := by
    refine eq_top_iff.mpr ?_
    first
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top (f := f)]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.maxGenEigenspace μ = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ)
        μ (by simpa using hμ) le_rfl
  have hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K)) := by
    first
    | exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective
    | exact (Module.End.iSupIndep_maxGenEigenspace f).comp Subtype.val_injective
  have hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm
  have htr := LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j)
    (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))
  exact htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))

end TracePow

section Lattice

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Lattice

end Formalism.SA.P
