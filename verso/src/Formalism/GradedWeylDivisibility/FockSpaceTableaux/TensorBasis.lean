import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module

open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Use `revert hx`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `only [Finset.prod_empty]`. Conclude with `Submodule.one_le.mp le_rfl`.

Introduce `s T hs ih hx`. Rewrite using `[Finset.prod_insert hs, Finset.prod_insert hs]`. Conclude with `Submodule.mul_mem_mul (hx s (Finset.mem_insert_self s T)) (ih fun t ht => hx t (Finset.mem_insert_of_mem ht))`.
-/
theorem ldtensor_prod_mem_prod {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {S : Type*}
    (T : Finset S) (N : S → Submodule R A) (x : S → A) (hx : ∀ s ∈ T, x s ∈ N s) :
    ∏ s ∈ T, x s ∈ ∏ s ∈ T, N s := by
  classical
  revert hx
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp le_rfl
  · intro s T hs ih hx
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact Submodule.mul_mem_mul (hx s (Finset.mem_insert_self s T))
      (ih fun t ht => hx t (Finset.mem_insert_of_mem ht))

/- English proof (translation)
Establish `h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (Set.range fun j => blockEmb K s (b s j))`. Introduce `s`. Establish `h` using `Submodule.mem_map_of_mem (f := ((blockEmb K s).toLinearMap.restrictScalars R)) (hF s)`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h`.

Establish `h2` using `ldtensor_prod_mem_prod Finset.univ _ _ fun s _ => h1 s`. Rewrite `h2` using `[Submodule.prod_span]`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[Set.mem_finset_prod]`.

Take `⟨g, hg, rfl⟩` from `hy`. Use `choose i hi using fun s => hg (Finset.mem_univ s)`. Conclude with `⟨i, Finset.prod_congr rfl fun s _ => hi s⟩`.
-/
theorem ldtensor_span_prod (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S]
    {k n : ℕ} {ι : S → Type*}
    (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K) (F : S → MvPolynomial (Fin k × Fin n) K)
    (hF : ∀ s, F s ∈ Submodule.span R (Set.range (b s))) :
    ∏ s, blockEmb K s (F s) ∈
      Submodule.span R (Set.range fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (Set.range fun j => blockEmb K s (b s j)) := by
    intro s
    have h := Submodule.mem_map_of_mem (f := ((blockEmb K s).toLinearMap.restrictScalars R)) (hF s)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  have h2 := ldtensor_prod_mem_prod Finset.univ _ _ fun s _ => h1 s
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro y hy
  rw [Set.mem_finset_prod] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  choose i hi using fun s => hg (Finset.mem_univ s)
  exact ⟨i, Finset.prod_congr rfl fun s _ => hi s⟩

section Field

variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}

/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single s]`. Conclude with `Finsupp.mapDomain_apply (fun x y h => by simpa using h) _ v`. Introduce `t _ hts`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨w, hw⟩`.

Conclude with `hts (congrArg Prod.fst hw)`. Simplify using the standard rewrite rules.
-/
theorem ldtensor_glue_apply (α : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    (∑ t, (α t).mapDomain (Prod.mk t)) (s, v) = α s v := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (fun x y h => by simpa using h) _ v
  · intro t _ hts
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w, hw⟩
    exact hts (congrArg Prod.fst hw)
  · simp

/- English proof (translation)
Introduce `α β h`. Use function extensionality and compare the values at `s`. Use extensionality with `v`. Establish `e` using `congrArg (fun f => f (s, v)) h`. Simplify `e` using `[ldtensor_glue_apply]`.
-/
theorem ldtensor_glue_injective :
    Function.Injective (fun α : S → (Fin k × Fin n →₀ ℕ) => ∑ t, (α t).mapDomain (Prod.mk t)) := by
  intro α β h
  funext s
  ext v
  have e := congrArg (fun f => f (s, v)) h
  simpa [ldtensor_glue_apply] using e

/- English proof (translation)
Simplify using `only [blockEmb, rename_monomial]`. Rewrite using `[monomial_sum_one]`.
-/
theorem ldtensor_prod_monomial (α : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ s, blockEmb K s (monomial (α s) (1 : K)) = monomial (∑ t, (α t).mapDomain (Prod.mk t)) 1 := by
  simp only [blockEmb, rename_monomial]
  rw [monomial_sum_one]

def ldtensor_psi : PiTensorProduct K (fun _ : S => MvPolynomial (Fin k × Fin n) K) →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × (Fin k × Fin n)) K)).compLinearMap
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap))

/- English proof (translation)
Unfold `ldtensor_psi`. Rewrite using `[PiTensorProduct.lift.tprod]`. Simplify using `[MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`.
-/
theorem ldtensor_psi_tprod (F : S → MvPolynomial (Fin k × Fin n) K) :
    ldtensor_psi K (tprod K F) = ∏ s, blockEmb K s (F s) := by
  unfold ldtensor_psi
  rw [PiTensorProduct.lift.tprod]
  simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/- English proof (translation)
Set `B` to `Basis.piTensorProduct (fun _ : S => MvPolynomial.basisMonomials (Fin k × Fin n) K)`. Establish `hB : ∀ α, B α = tprod K (fun s => monomial (α s) (1 : K))` using `fun α => by`. Simplify using `[B, Basis.piTensorProduct_apply, MvPolynomial.coe_basisMonomials]`. Establish `hli : LinearIndependent K (ldtensor_psi K ∘ B)`. Establish `e : ldtensor_psi K ∘ B = fun α => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K)`.

Use function extensionality and compare the values at `α`. Simplify using `only [Function.comp_apply, hB, ldtensor_psi_tprod, ldtensor_prod_monomial]`. Rewrite using `[e]`. Establish `h` using `(MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K).linearIndependent.comp _ (ldtensor_glue_injective (S := S) (k := k) (n := n))`. Establish `e2 : (fun α : S → (Fin k × Fin n →₀ ℕ) => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K)) = ⇑(MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K) ∘ (fun α => ∑ t, (α t).mapDomain (Prod.mk t))`.

Use function extensionality and compare the values at `α`. Simplify using `[MvPolynomial.coe_basisMonomials]`. Rewrite using `[e2]`. Conclude with `h`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Rewrite `hx`, the goal using `[← B.linearCombination_repr x]`. Rewrite `hx` using `[Finsupp.apply_linearCombination]`. Establish `h0` using `(linearIndependent_iff.mp hli) _ hx`. Rewrite using `[h0, map_zero]`.
-/
theorem ldtensor_psi_injective : Function.Injective (ldtensor_psi K (S := S) (k := k) (n := n)) := by
  classical
  let B := Basis.piTensorProduct (fun _ : S => MvPolynomial.basisMonomials (Fin k × Fin n) K)
  have hB : ∀ α, B α = tprod K (fun s => monomial (α s) (1 : K)) := fun α => by
    simp [B, Basis.piTensorProduct_apply, MvPolynomial.coe_basisMonomials]
  have hli : LinearIndependent K (ldtensor_psi K ∘ B) := by
    have e : ldtensor_psi K ∘ B = fun α => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K) := by
      funext α
      simp only [Function.comp_apply, hB, ldtensor_psi_tprod, ldtensor_prod_monomial]
    rw [e]
    have h := (MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K).linearIndependent.comp _
      (ldtensor_glue_injective (S := S) (k := k) (n := n))
    have e2 : (fun α : S → (Fin k × Fin n →₀ ℕ) => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K)) =
        ⇑(MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K) ∘
          (fun α => ∑ t, (α t).mapDomain (Prod.mk t)) := by
      funext α
      simp [MvPolynomial.coe_basisMonomials]
    rw [e2]
    exact h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← B.linearCombination_repr x] at hx ⊢
  rw [Finsupp.apply_linearCombination] at hx
  have h0 := (linearIndependent_iff.mp hli) _ hx
  rw [h0, map_zero]

/- English proof (translation)
Set `E` to `fun s => Basis.extend (hb s).linearIndepOn_id`. Set `p : (∀ s, ι s) → ∀ s, ((hb s).linearIndepOn_id.extend (Set.subset_univ _) : Set _)` to `fun i s => ⟨b s (i s), Basis.subset_extend _ (Set.mem_range_self _)⟩`. Establish `hp : Function.Injective p`. Introduce `i j h`. Use function extensionality and compare the values at `s`.

Use `congrArg (fun q => ((q s : _) : MvPolynomial (Fin k × Fin n) K)) h` as an intermediate fact. Conclude with `(hb s).injective this`. Use `(Basis.piTensorProduct E).linearIndependent.comp p hp` as an intermediate fact. Establish `e : (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) = (Basis.piTensorProduct E) ∘ p`. Use function extensionality and compare the values at `i`.

Simplify using `[E, p, Basis.piTensorProduct_apply, Basis.coe_extend]`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem ldtensor_tprod_linInd {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) := by
  let E := fun s => Basis.extend (hb s).linearIndepOn_id
  let p : (∀ s, ι s) → ∀ s, ((hb s).linearIndepOn_id.extend (Set.subset_univ _) : Set _) :=
    fun i s => ⟨b s (i s), Basis.subset_extend _ (Set.mem_range_self _)⟩
  have hp : Function.Injective p := by
    intro i j h
    funext s
    have := congrArg (fun q => ((q s : _) : MvPolynomial (Fin k × Fin n) K)) h
    exact (hb s).injective this
  have := (Basis.piTensorProduct E).linearIndependent.comp p hp
  have e : (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) = (Basis.piTensorProduct E) ∘ p := by
    funext i
    simp [E, p, Basis.piTensorProduct_apply, Basis.coe_extend]
  rw [e]
  exact this

/- English proof (translation)
Establish `h` using `(ldtensor_tprod_linInd K b hb).map' (ldtensor_psi K) (LinearMap.ker_eq_bot.mpr (ldtensor_psi_injective K))`. Establish `e : (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) = ldtensor_psi K ∘ (fun i => tprod K fun s => b s (i s))`. Use function extensionality and compare the values at `i`. Simplify using `[ldtensor_psi_tprod]`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem ldtensor_prod_linInd_field {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h := (ldtensor_tprod_linInd K b hb).map' (ldtensor_psi K)
    (LinearMap.ker_eq_bot.mpr (ldtensor_psi_injective K))
  have e : (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) =
      ldtensor_psi K ∘ (fun i => tprod K fun s => b s (i s)) := by
    funext i
    simp [ldtensor_psi_tprod]
  rw [e]
  exact h

end Field

/- English proof (translation)
Introduce `R K _ _ _ _ _ S _ _ k n ι M b hb hM`. Establish `hK : ∀ s, LinearIndependent K (b s)` using `fun s => (LinearIndependent.iff_fractionRing R K).mp (hb s)`. Use `⟨(LinearIndependent.iff_fractionRing R K).mpr (ldtensor_prod_linInd_field K b hK), ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun s => b s (i s), fun s => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← hM s]`. Conclude with `Submodule.subset_span ⟨i s, rfl⟩`.

Unfold `tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Conclude with `ldtensor_span_prod R K b F fun s => by rw [hM s]; exact hF s`.
-/
theorem tensor_power_basis : TensorBasis := by
  intro R K _ _ _ _ _ S _ _ k n ι M b hb hM
  have hK : ∀ s, LinearIndependent K (b s) := fun s => (LinearIndependent.iff_fractionRing R K).mp (hb s)
  refine ⟨(LinearIndependent.iff_fractionRing R K).mpr (ldtensor_prod_linInd_field K b hK), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => b s (i s), fun s => ?_, rfl⟩
    rw [← hM s]
    exact Submodule.subset_span ⟨i s, rfl⟩
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact ldtensor_span_prod R K b F fun s => by rw [hM s]; exact hF s

end Formalism.GradedWeylDivisibility
