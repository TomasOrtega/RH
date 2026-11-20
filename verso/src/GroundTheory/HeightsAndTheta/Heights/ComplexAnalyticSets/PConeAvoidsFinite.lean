import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Establish `hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ), (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) = homogeneousComponent i p` using `fun p i => decomposition.decompose'_apply p i`. Establish `h` using `DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a) ((mem_homogeneousSubmodule e g).2 hg)`. Simplify `h` using `only [hd]`.
-/
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by
  have hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) =
        homogeneousComponent i p := fun p i => decomposition.decompose'_apply p i
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a)
    ((mem_homogeneousSubmodule e g).2 hg)
  simpa only [hd] using h

/- English proof (translation)
Establish `: linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))`. Conclude with `(mem_homogeneousSubmodule 1 _).1 this`.
-/
theorem isHomogeneous_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (linPoly A j).IsHomogeneous 1 := by
  have : linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))
  exact (mem_homogeneousSubmodule 1 _).1 this

/- English proof (translation)
Introduce `n d N J A hcone`. Use `letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra`. Use `letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule`. Use `show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)`. Set `gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J)` to `Finset.univ.image fun f : Fin n → Fin N => Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)`.

Set `M` to `Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))`. Establish `hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ), Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M`. Introduce `s p hp`. Establish `: Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p`. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `M.smul_mem s hp`. Establish `hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ), (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M` using `fun s q h => by rw [map_sum]; exact M.sum_mem h`. Establish `hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M`.

Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Establish `key : ∀ (b x : MvPolynomial (Fin n) ℂ), x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) → Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M`. Introduce and unpack `b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)`.

Rewrite using `[homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree) (homogeneousComponent_isHomogeneous f.totalDegree f)] split_ifs with hek`. Establish `hs` using `sum_homogeneousComponent f`. Rewrite `hs` using `[Finset.sum_range_succ]`. Establish `hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f`. Rewrite using `[leadForm]`.

Take the linear combination `hs`. Rewrite using `[hf', mul_sub, map_sub, Finset.mul_sum, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]`. Use `M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _ ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Rewrite using `[homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)] split_ifs with hk`. Establish `hl : linPoly A j = pullback A (X j)` using `by simp [pullback]`. Rewrite using `[mul_comm, hl]`. Conclude with `hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))`.

Simplify using the standard rewrite rules. Introduce `q hq`. Rewrite using `[q.as_sum]`. Use `hsum _ _ fun s hs => ?_` and prove the remaining obligations. Establish `hdeg : s.degree = k`.

Use `hq (mem_support_iff.mp hs)` as an intermediate fact. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `this`. Establish `hCs : monomial s (coeff s q) = pullback A (C (coeff s q)) * monomial s 1`. Simplify using `[pullback, C_mul_monomial]`.

Rewrite using `[hCs]`. Use `hsmul _ _ ?_` and prove the remaining obligations. Distinguish the cases in `hlow : ∀ i, s i < N`. Use `Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))` and prove the remaining obligations. Use `congr 2`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using `only [not_forall, not_lt] at hlow`. Take `⟨i, hi⟩` from `hlow`. Establish `hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A`.

Apply `hcone` to reduce the goal to its premises. Establish `hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1`. Rewrite using `[← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]`. Rewrite using `[hsplit]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)`.

Rewrite `hmem` using `[leadIdeal, linIdeal, ← Ideal.span_union]`. Take `⟨r, a, g, hag⟩` from `Submodule.mem_span_set'.1 hmem`. Establish `hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ))`. Rewrite using `[hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]`. Rewrite using `[hm, map_sum]`.

Conclude with `hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2`. Establish `htop : M = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Rewrite using `[← sum_homogeneousComponent p]`. Conclude with `hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)`. Conclude with `⟨⟨gen, htop⟩⟩`.
-/
theorem ConeAvoidsFinite.proof : ConeAvoidsFinite.Statement := by
  intro n d N J A hcone
  letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule
  show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
  classical
  let gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J) := Finset.univ.image fun f : Fin n → Fin N =>
    Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)
  let M := Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))
  have hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ),
      Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M := by
    intro s p hp
    have : Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]; rfl
    rw [this]; exact M.smul_mem s hp
  have hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ),
      (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M :=
    fun s q h => by rw [map_sum]; exact M.sum_mem h
  have hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>

    have key : ∀ (b x : MvPolynomial (Fin n) ℂ),
        x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) →
        Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M := by
      rintro b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree)
          (homogeneousComponent_isHomogeneous f.totalDegree f)]
        split_ifs with hek
        · have hs := sum_homogeneousComponent f
          rw [Finset.sum_range_succ] at hs
          have hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f := by
            rw [leadForm]; linear_combination hs
          rw [hf', mul_sub, map_sub, Finset.mul_sum,
            Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]
          refine M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _
            ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))
          have := Finset.mem_range.1 hi; omega
        · simp
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)]
        split_ifs with hk
        · have hl : linPoly A j = pullback A (X j) := by simp [pullback]
          rw [mul_comm, hl]
          exact hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))
        · simp

    intro q hq
    rw [q.as_sum]
    refine hsum _ _ fun s hs => ?_
    have hdeg : s.degree = k := by
      have := hq (mem_support_iff.mp hs)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have hCs : monomial s (coeff s q) = pullback A (C (coeff s q)) * monomial s 1 := by
      simp [pullback, C_mul_monomial]
    rw [hCs]
    refine hsmul _ _ ?_
    by_cases hlow : ∀ i, s i < N
    · refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))
      congr 2; ext i; simp
    simp only [not_forall, not_lt] at hlow
    obtain ⟨i, hi⟩ := hlow

    have hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A := by
      apply hcone
      have hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1 := by
        rw [← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
      rw [hsplit]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)
    rw [leadIdeal, linIdeal, ← Ideal.span_union] at hmem
    obtain ⟨r, a, g, hag⟩ := Submodule.mem_span_set'.1 hmem
    have hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ)) := by
      rw [hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]
    rw [hm, map_sum]
    exact hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sum_homogeneousComponent p]
    exact hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)
  exact ⟨⟨gen, htop⟩⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
