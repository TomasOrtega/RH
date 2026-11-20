import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFibA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFibB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]

variable (ι) in

def segMono (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, i k⟩

/- English proof (translation)
Simplify using `[segMono, segre, map_prod]`.
-/
theorem eval_segMono (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : eval z (segMono ι i) = segre z i := by
  simp [segMono, segre, map_prod]

/- English proof (translation)
Use `IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (fun k => blkW ι ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)` as an intermediate fact. Unfold `segMono`. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Simplify using `[blkW, Finset.sum_apply, Pi.single_apply]`.
-/
theorem segMono_homog (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkW ι) (segMono ι i) (fun _ => 1) := by
  have := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (fun k => blkW ι ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  unfold segMono
  convert this using 1
  funext k'
  simp [blkW, Finset.sum_apply, Pi.single_apply]

variable {e : ℕ}

def psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Σ k, ι k) ℂ :=
  ∑ i, C (Ψ (fun i' => if i = i' then 1 else 0) j) * segMono ι i

/- English proof (translation)
Establish `hs : segre z = ∑ i, segre z i • (fun i' => if i = i' then (1 : ℂ) else 0)`. Use function extensionality and compare the values at `i'`. Simplify using `[Finset.sum_apply]`. Simplify using `only [psiPoly, map_sum, map_mul, eval_C, eval_segMono]`. Use `conv_rhs => rw [hs]`.

Rewrite using `[map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem eval_psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1))
    (z : (Σ k, ι k) → ℂ) : eval z (psiPoly Ψ j) = Ψ (segre z) j := by
  have hs : segre z = ∑ i, segre z i • (fun i' => if i = i' then (1 : ℂ) else 0) := by
    funext i'
    simp [Finset.sum_apply]
  simp only [psiPoly, map_sum, map_mul, eval_C, eval_segMono]
  conv_rhs => rw [hs]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `hmem : psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1)`. Unfold `psiPoly`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[C_mul']`. Conclude with `Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (segMono_homog i))`.

Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp hmem`.
-/
theorem psiPoly_homog (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
  have hmem : psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1) := by
    unfold psiPoly
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (segMono_homog i))
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hmem

variable (ι) in

def idealC (P : Ideal (MRing ι)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.map (map (Int.castRingHom ℂ)) P

/- English proof (translation)
Establish `hle : idealC ι P ≤ RingHom.ker (eval z)`. Rewrite using `[idealC, Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Conclude with `hz.2 g hg`.

Conclude with `hle hf`.
-/
theorem eval_idealC {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {f}
    (hf : f ∈ idealC ι P) : eval z f = 0 := by
  have hle : idealC ι P ≤ RingHom.ker (eval z) := by
    rw [idealC, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 g hg
  exact hle hf

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hP`. Rewrite using `[idealC, Ideal.map_span]`. Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨a, ha⟩` from `hS g hg`.

Conclude with `⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_map_of_isMultiHomog ha)⟩`.
-/
theorem idealC_homog {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    (idealC ι P).IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [idealC, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hS g hg
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_map_of_isMultiHomog ha)⟩

/- English proof (translation)
Use `set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := idealC ι P ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hJ`. Establish `hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J)`. Rewrite using `[MvPolynomial.mem_vanishingIdeal_iff]`. Introduce `z hz0`. Rewrite `hz0` using `[MvPolynomial.mem_zeroLocus_iff]`.

Establish `hz : ∀ p ∈ J, eval z p = 0` using `fun p hp => hz0 p hp`. Express the relevant statement in the definitionally equal form `eval z (segMono ι i) = 0`. Assume the negation of the conclusion as `hne`. Establish `hmc : z ∈ mcPts P`. Use `⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eval_segMono]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) h0`. Conclude with `hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))`.

Apply `hΨ z hmc` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `hz (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))` as an intermediate fact. Rewrite `this` using `[eval_psiPoly]`. Conclude with `this`.

Rewrite `hvan` using `[MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]`. Take `⟨n, hn⟩` from `hvan`. Establish `hn1 : segMono ι i ^ (n + 1) ∈ J`. Rewrite using `[pow_succ]`. Conclude with `J.mul_mem_right _ hn`.

Take `⟨g, hg, a, ha, hga⟩` from `Submodule.mem_sup.mp hn1`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp ha`. Establish `hcomp : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ n ∧ ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) (fun _ => n) (c j)) = eval (segre z) G` using `fun j => diag_of_homog n (weightedHomogeneousComponent_isWeightedHomogeneous _ _)`. Use `choose G hG1 hG2 using hcomp`. Use `⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hG1 j, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Establish `hD : (fun _ : K => n + 1) = (fun _ : K => n) + (fun _ : K => 1)`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `hseg : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (segMono ι i ^ (n + 1)) = segMono ι i ^ (n + 1)`.

Establish `hh` using `(segMono_homog (ι := ι) i).pow (n + 1)`. Establish `hh' : (n + 1) • (fun _ : K => (1 : ℕ)) = fun _ : K => n + 1` using `by funext k; simp`. Rewrite `hh` using `[hh']`. Conclude with `weightedHomogeneousComponent_eq_self hh`. Establish `hgc : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) g ∈ idealC ι P`.

Establish `h` using `(idealC_homog hP) (fun _ : K => n + 1) hg`. Rewrite using `[← weightedDecomposition.decompose'_apply ℂ (blkW ι) g (fun _ : K => n + 1)]`. Conclude with `h`. Establish `hterm : ∀ j, weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (c j * psiPoly Ψ j) = weightedHomogeneousComponent (blkW ι) (fun _ : K => n) (c j) * psiPoly Ψ j`. Introduce `j`.

Rewrite using `[hD]`. Conclude with `comp_mul_homog (psiPoly_homog Ψ j) (c j) _`. Establish `heq` using `congrArg (weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1)) hga`. Rewrite `heq` using `[hseg, map_add, ← hc, map_sum]`. Simplify using `only [hterm] at heq`.

Establish `hev` using `congrArg (eval z) heq`. Rewrite `hev` using `[map_add, map_sum, eval_idealC hz hgc, zero_add, map_pow, eval_segMono]`. Rewrite using `[← hev]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hG2, eval_psiPoly, mul_comm]`.
-/
theorem segre_rel {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ mcPts P, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := idealC ι P ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hJ
  have hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz0
    rw [MvPolynomial.mem_zeroLocus_iff] at hz0
    have hz : ∀ p ∈ J, eval z p = 0 := fun p hp => hz0 p hp
    change eval z (segMono ι i) = 0
    by_contra hne
    have hmc : z ∈ mcPts P := by
      refine ⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩
      · intro h0
        apply hne
        rw [eval_segMono]
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · exact hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
    apply hΨ z hmc
    funext j
    have := hz (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))
    rw [eval_psiPoly] at this
    exact this
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  obtain ⟨n, hn⟩ := hvan
  have hn1 : segMono ι i ^ (n + 1) ∈ J := by
    rw [pow_succ]
    exact J.mul_mem_right _ hn
  obtain ⟨g, hg, a, ha, hga⟩ := Submodule.mem_sup.mp hn1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hcomp : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ n ∧ ∀ z : (Σ k, ι k) → ℂ,
      eval z (weightedHomogeneousComponent (blkW ι) (fun _ => n) (c j)) = eval (segre z) G :=
    fun j => diag_of_homog n (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG1 hG2 using hcomp
  refine ⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hG1 j, ?_⟩
  intro z hz
  have hD : (fun _ : K => n + 1) = (fun _ : K => n) + (fun _ : K => 1) := by
    funext k; simp
  have hseg : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (segMono ι i ^ (n + 1)) =
      segMono ι i ^ (n + 1) := by
    have hh := (segMono_homog (ι := ι) i).pow (n + 1)
    have hh' : (n + 1) • (fun _ : K => (1 : ℕ)) = fun _ : K => n + 1 := by funext k; simp
    rw [hh'] at hh
    exact weightedHomogeneousComponent_eq_self hh
  have hgc : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) g ∈ idealC ι P := by
    have h := (idealC_homog hP) (fun _ : K => n + 1) hg
    rw [← weightedDecomposition.decompose'_apply ℂ (blkW ι) g (fun _ : K => n + 1)]
    exact h
  have hterm : ∀ j, weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (c j * psiPoly Ψ j) =
      weightedHomogeneousComponent (blkW ι) (fun _ : K => n) (c j) * psiPoly Ψ j := by
    intro j
    rw [hD]
    exact comp_mul_homog (psiPoly_homog Ψ j) (c j) _
  have heq := congrArg (weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1)) hga
  rw [hseg, map_add, ← hc, map_sum] at heq
  simp only [hterm] at heq
  have hev := congrArg (eval z) heq
  rw [map_add, map_sum, eval_idealC hz hgc, zero_add, map_pow, eval_segMono] at hev
  rw [← hev]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, hG2, eval_psiPoly, mul_comm]

/- English proof (translation)
Introduce `K _ ι _ P e Ψ hP hΨ y`. Use `choose r hr G hG hrel using fun i => segre_rel hP.2.1.2.1 Ψ hΨ i`. Set `H : ((k : K) → ι k) → MvPolynomial ((k : K) → ι k) ℂ` to `fun i => ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G i j`. Use `(fibSys_finite r H (fun i => ?_)).subset ?_` and prove the remaining obligations. Use `lt_of_le_of_lt ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)) (Nat.sub_lt (hr i) one_pos)` and prove the remaining obligations.

Conclude with `(totalDegree_mul _ _).trans (by simpa using hG i j)`. Introduce and unpack `w ⟨z, hz, rfl, hΨz⟩ i`. Rewrite using `[hrel i z hz, hΨz]`. Simplify using `[H]`.
-/
theorem fibreFinite : FibreFiniteStatement := by
  intro K _ ι _ P e Ψ hP hΨ y
  classical
  choose r hr G hG hrel using fun i => segre_rel hP.2.1.2.1 Ψ hΨ i
  let H : ((k : K) → ι k) → MvPolynomial ((k : K) → ι k) ℂ := fun i =>
    ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G i j
  refine (fibSys_finite r H (fun i => ?_)).subset ?_
  · refine lt_of_le_of_lt ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_))
      (Nat.sub_lt (hr i) one_pos)
    exact (totalDegree_mul _ _).trans (by simpa using hG i j)
  · rintro w ⟨z, hz, rfl, hΨz⟩ i
    rw [hrel i z hz, hΨz]
    simp [H]

end ReciprocityTheory.ChartRestriction.G.Geo
