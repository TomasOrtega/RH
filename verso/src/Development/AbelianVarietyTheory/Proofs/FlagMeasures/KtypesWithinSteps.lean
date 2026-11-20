import Mathlib
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

open Formalism.REAL
open scoped InnerProductSpace

namespace GlobalTheory.KTypeSteps

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Use `congr 1`. Simplify using `[nsq, dot, sq]`.
-/
theorem sqrt_nsq_eq {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [nsq, dot, sq]

/- English proof (translation)
Rewrite using `[sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]`. Conclude with `norm_add_le _ _`.
-/
theorem sqrt_nsq_add_le {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]
  exact norm_add_le _ _

/- English proof (translation)
Establish `h : ∀ c, root a b c * root a b c = (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0)`. Introduce `c`. Distinguish the cases in `h1 : c = a`. Substitute `h1` using the available equality. Simplify using `[root, hab]`.

Distinguish the cases in `h2 : c = b`. Substitute `h2` using the available equality. Simplify using `[root, h1]`. Simplify using `[root, h1, h2]`. Simplify using `only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Evaluate the numerical expressions.
-/
theorem nsq_root {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  have h : ∀ c, root a b c * root a b c =
      (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      simp [root, hab]
    · by_cases h2 : c = b
      · subst h2
        simp [root, h1]
      · simp [root, h1, h2]
  simp only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

/- English proof (translation)
Introduce `z hz`. Rewrite using `[LinearMap.mem_ker, innerₛₗ_apply_apply]`. Conclude with `kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x (mem_compact_span_self_general x) z hz`.
-/
theorem kSpan_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hne : μ ≠ ν) :
    kSpan ε E y ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  intro z hz
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply]
  exact kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x
    (mem_compact_span_self_general x) z hz

/- English proof (translation)
Use `le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)` and prove the remaining obligations. Take `⟨hA, hθ⟩` from `(arrModule V n ε E 1).1 hg`. Establish `hKU` using `(arrModule V n ε E 1).2 hu`. Use `noncompact_arr_finite_dimensional (j := 1) hfd` as an intermediate fact. Take `⟨m, F, lam, hF, -, hsup⟩` from `kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1) inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable`.

Express the relevant statement in the definitionally equal form `(arrV0 ε E y 1).map (thetaA E 1) ≤ _`. Rewrite using `[← hsup, Submodule.map_le_iff_le_comap]`. Use `iSup_le fun i => ?_` and prove the remaining obligations. Take `⟨hmem, h0, hhi⟩` from `hF i`. Take `⟨a, b, hab, hlam⟩` from `hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0`.

Establish `hθhi : KHighest ε E (lam i) (thetaA E 1 (F i))`. Use `⟨fun c => ?_, fun c d hcd he => ?_⟩` and prove the remaining obligations. Rewrite using `[← hθ, hhi.1 c, map_smul]`. Rewrite using `[← hθ, hhi.2 c d hcd he, map_zero]`. Establish `hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1)`.

Use `compact_span_le_of_stable ?_ (mem_compact_span_self_general _)` and prove the remaining obligations. Introduce `c d hcd G hG`. Rewrite `hG`, the goal using `[Submodule.mem_comap]`. Rewrite using `[hθ]`. Conclude with `compact_span_stable_general _ c d hcd _ hG`.

Conclude with `hle.trans (Submodule.comap_mono (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))`. Rewrite using `[(pfilFacts V n ε E y hg).1]`. Conclude with `kSpan_le_ker hg hu hx hy hne`.
-/
theorem pfil_one_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hfd : FiniteDimensional ℂ (kSpan ε E y))
    (hne : μ ≠ ν) (hne' : ∀ a b, ε a ≠ ε b → μ ≠ ν + root a b) :
    pfil ε E y 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  refine le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)
  · obtain ⟨hA, hθ⟩ := (arrModule V n ε E 1).1 hg
    have hKU := (arrModule V n ε E 1).2 hu
    have := noncompact_arr_finite_dimensional (j := 1) hfd
    obtain ⟨m, F, lam, hF, -, hsup⟩ := kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1)
      inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable
    change (arrV0 ε E y 1).map (thetaA E 1) ≤ _
    rw [← hsup, Submodule.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    obtain ⟨hmem, h0, hhi⟩ := hF i
    obtain ⟨a, b, hab, hlam⟩ := hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0
    have hθhi : KHighest ε E (lam i) (thetaA E 1 (F i)) := by
      refine ⟨fun c => ?_, fun c d hcd he => ?_⟩
      · rw [← hθ, hhi.1 c, map_smul]
      · rw [← hθ, hhi.2 c d hcd he, map_zero]
    have hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1) := by
      refine compact_span_le_of_stable ?_ (mem_compact_span_self_general _)
      intro c d hcd G hG
      rw [Submodule.mem_comap] at hG ⊢
      rw [hθ]
      exact compact_span_stable_general _ c d hcd _ hG
    exact hle.trans (Submodule.comap_mono
      (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))
  · rw [(pfilFacts V n ε E y hg).1]
    exact kSpan_le_ker hg hu hx hy hne

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨w, hw, hp, y, hy, rfl⟩`.
-/
theorem ew_mem_pfil {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    {w : List (Fin n × Fin n)} (hw : w.length ≤ j) (hp : ∀ p ∈ w, ε p.1 ≠ ε p.2) {y : V}
    (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j :=
  Submodule.subset_span ⟨w, hw, hp, y, hy, rfl⟩

/- English proof (translation)
Introduce `V _ _ n ε E Λ u hg hu hΛ hfd j`. Take `⟨h0, -, hst, -, -, -, hfin⟩` from `pfilFacts V n ε E u hg`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `μ x hx hx0 hhi`.

Rewrite `hx` using `[h0]`. Use `compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0` as an intermediate fact. Substitute `this` using the available equality. Simplify using `[nsq, dot]`. Consider the case `succ j ih`.

Introduce `μ x hx hx0 hhi`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Move the coercions through the operations in `at hlt`. Establish `hs2 : 0 ≤ Real.sqrt 2` using `Real.sqrt_nonneg 2`.

Use `hfin hfd j` as an intermediate fact. Take `⟨m, y, lam, hy, -, hsup⟩` from `kDecomp V n ε E (pfil ε E u j) inferInstance (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)`. Establish `hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x)`. Introduce `i`. Take `⟨hmem, hy0, hyh⟩` from `hy i`.

Establish `hb` using `ih (lam i) (y i) hmem hy0 hyh`. Use `pfil_one_le_ker hg hu hhi hyh (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_` and prove the remaining obligations. Introduce `h`. Rewrite `hlt` using `[h]`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `a b hab h`. Establish `hab' : a ≠ b` using `fun h => hab (h ▸ rfl)`. Establish `ht` using `sqrt_nsq_add_le (lam i - Λ) (root a b)`. Rewrite `ht` using `[nsq_root hab']`. Establish `he : μ - Λ = lam i - Λ + root a b` using `by rw [h]; abel`.

Rewrite `hlt` using `[he]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x)`. Rewrite using `[← hsup]`. Use `iSup_le fun i => le_trans ?_ (hone i)` and prove the remaining obligations.

Take `⟨g0, g1, -⟩` from `pfilFacts V n ε E (y i) hg`. Rewrite using `[← g0]`. Conclude with `g1 0`. Establish `hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b)`. Introduce `a b`.

Rewrite using `[← hsup]`. Use `iSup_le fun i z hz => hone i ?_` and prove the remaining obligations. Take `⟨g0, -, -, g3, -⟩` from `pfilFacts V n ε E (y i) hg`. Rewrite `hz` using `[← g0]`. Conclude with `g3 0 a b z hz`.

Establish `hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, hp, z, hz, rfl⟩`. Consider the cases of `w with`. Consider the case `nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)`.

Consider the case `cons p w`. Establish `hw' : w.length ≤ j` using `by simpa using hw`. Conclude with `hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)`. Use `hC hx` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, innerₛₗ_apply_apply]`.

Conclude with `hx0 (inner_self_eq_zero.mp this)`.
-/
theorem ktypes_within_steps :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E →
      KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
      ∀ (j : ℕ) (μ : Fin n → ℝ), ∀ x ∈ pfil ε E u j, x ≠ 0 → KHighest ε E μ x →
        Real.sqrt (nsq (μ - Λ)) ≤ Real.sqrt 2 * j := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd j
  obtain ⟨h0, -, hst, -, -, -, hfin⟩ := pfilFacts V n ε E u hg
  induction j with
  | zero =>
    intro μ x hx hx0 hhi
    rw [h0] at hx
    have := compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0
    subst this
    simp [nsq, dot]
  | succ j ih =>
    intro μ x hx hx0 hhi
    by_contra hlt
    rw [not_le] at hlt
    push_cast at hlt
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have := hfin hfd j
    obtain ⟨m, y, lam, hy, -, hsup⟩ := kDecomp V n ε E (pfil ε E u j) inferInstance
      (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)
    have hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      intro i
      obtain ⟨hmem, hy0, hyh⟩ := hy i
      have hb := ih (lam i) (y i) hmem hy0 hyh
      refine pfil_one_le_ker hg hu hhi hyh
        (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_
      · intro h
        rw [h] at hlt
        nlinarith
      · intro a b hab h
        have hab' : a ≠ b := fun h => hab (h ▸ rfl)
        have ht := sqrt_nsq_add_le (lam i - Λ) (root a b)
        rw [nsq_root hab'] at ht
        have he : μ - Λ = lam i - Λ + root a b := by rw [h]; abel
        rw [he] at hlt
        nlinarith
    have hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      rw [← hsup]
      refine iSup_le fun i => le_trans ?_ (hone i)
      obtain ⟨g0, g1, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0]
      exact g1 0
    have hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b) := by
      intro a b
      rw [← hsup]
      refine iSup_le fun i z hz => hone i ?_
      obtain ⟨g0, -, -, g3, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0] at hz
      exact g3 0 a b z hz
    have hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hp, z, hz, rfl⟩
      cases w with
      | nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)
      | cons p w =>
        have hw' : w.length ≤ j := by simpa using hw
        exact hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)
    have := hC hx
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at this
    exact hx0 (inner_self_eq_zero.mp this)

end GlobalTheory.KTypeSteps
