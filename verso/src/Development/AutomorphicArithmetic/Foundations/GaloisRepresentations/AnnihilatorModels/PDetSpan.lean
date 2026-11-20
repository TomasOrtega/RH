import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hco l _ P AI hT K LL a ρ hρ S _ π`. Take `⟨T⟩` from `hT`. Use `haveI := LL.2`. Use `haveI : FiniteDimensional ℚ_[l] (Fin a → ↥LL.1) := Module.Finite.trans ↥LL.1 (Fin a → ↥LL.1)`. Establish `honB : ∀ (f : End ℚ_[l] (Bst P)) (y : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P), onB P ℚ_[l] (Fin a → ↥LL.1) f y = AlgebraTensorModule.map (LinearMap.id : (Fin a → ↥LL.1) →ₗ[↥LL.1] (Fin a → ↥LL.1)) f y`.

Introduce `f y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => rw [onB_tmul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hsumco : ∀ {k : ℕ} (Y : Fin k → (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) (m : Fin a), co (∑ j, Y j) m = ∑ j, co (Y j) m`. Introduce `k Y m`. Unfold `co`. Conclude with `map_sum _ _ _`.

Establish `hone : ∀ i m : Fin a, π (co ((Pi.single i 1 : Fin a → ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : Bst P)) m) = (Pi.single i 1 : Fin a → S) m`. Introduce `i m`. Rewrite using `[co_tmul, Pi.single_apply, Pi.single_apply]`. Use `split_ifs`. Rewrite using `[← Algebra.TensorProduct.one_def, map_one]`.

Rewrite using `[zero_tmul, map_zero]`. Establish `key : ∀ i : Fin a, (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))`. Introduce `i`. Take `⟨k, b, x, hx, hsum⟩` from `GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K (Fin a → ↥LL.1) (GlobalTheory.PstCoeff.resQ ρ) (GlobalTheory.GalCut.IwaTwist.isSst_resQ P ρ hρ) (Pi.single i 1)`. Establish `hxD : ∀ j, x j ∈ Dpst P ρ` using `fun j => (mem_Dpst P ρ).mpr ⟨K, fun g _ => by`.

Establish `h` using `(mem_Dst P _).mp (hx j) g`. Rewrite using `[GlobalTheory.PstCoeff.stRep_resQ] at h⟩` and apply the resulting hypothesis. Establish `hfin : (Pi.single i 1 : Fin a → S) = ∑ j, π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] b j) • (fun m => π (co (x j) m))`. Use function extensionality and compare the values at `m`. Rewrite using `[← hone i m, hsum, hsumco, map_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[honB, (hco ℚ_[l] ↥LL.1 (Bst P) a).2.2.1 (b j) (x j)]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[hfin]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x j, hxD j⟩, rfl⟩)`.

Rewrite using `[eq_top_iff, ← (Pi.basisFun S (Fin a)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Pi.basisFun_apply]`. Conclude with `key i`.
-/
theorem UpperTheory.Gal.crystallineComparison.detSpan_of :
    CoFacts → SpanS := by
  intro hco l _ P AI hT K LL a ρ hρ S _ π
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥LL.1) := Module.Finite.trans ↥LL.1 (Fin a → ↥LL.1)
  have honB : ∀ (f : End ℚ_[l] (Bst P)) (y : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P),
      onB P ℚ_[l] (Fin a → ↥LL.1) f y =
        AlgebraTensorModule.map (LinearMap.id : (Fin a → ↥LL.1) →ₗ[↥LL.1] (Fin a → ↥LL.1)) f y := by
    intro f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rw [onB_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsumco : ∀ {k : ℕ} (Y : Fin k → (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) (m : Fin a),
      co (∑ j, Y j) m = ∑ j, co (Y j) m := by
    intro k Y m
    unfold co
    exact map_sum _ _ _
  have hone : ∀ i m : Fin a, π (co ((Pi.single i 1 : Fin a → ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : Bst P)) m) =
      (Pi.single i 1 : Fin a → S) m := by
    intro i m
    rw [co_tmul, Pi.single_apply, Pi.single_apply]
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [zero_tmul, map_zero]
  have key : ∀ i : Fin a, (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i =>
      π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) := by
    intro i
    obtain ⟨k, b, x, hx, hsum⟩ := GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K (Fin a → ↥LL.1) (GlobalTheory.PstCoeff.resQ ρ)
      (GlobalTheory.GalCut.IwaTwist.isSst_resQ P ρ hρ) (Pi.single i 1)
    have hxD : ∀ j, x j ∈ Dpst P ρ := fun j => (mem_Dpst P ρ).mpr ⟨K, fun g _ => by
      have h := (mem_Dst P _).mp (hx j) g
      rwa [GlobalTheory.PstCoeff.stRep_resQ] at h⟩
    have hfin : (Pi.single i 1 : Fin a → S) =
        ∑ j, π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] b j) • (fun m => π (co (x j) m)) := by
      funext m
      rw [← hone i m, hsum, hsumco, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [honB, (hco ℚ_[l] ↥LL.1 (Bst P) a).2.2.1 (b j) (x j)]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [hfin]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x j, hxD j⟩, rfl⟩)
  rw [eq_top_iff, ← (Pi.basisFun S (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact key i
