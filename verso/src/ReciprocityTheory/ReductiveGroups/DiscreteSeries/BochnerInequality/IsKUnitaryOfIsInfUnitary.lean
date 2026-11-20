import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
import Lemmata.SimultaneousEigenvectors.BlSimeig

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)

/- English proof (translation)
Introduce `a b h x y`. Rewrite using `[hU a b x y]`. Simplify using `[adjSign, h]`.
-/
theorem isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by
  intro a b h x y
  rw [hU a b x y]
  simp [adjSign, h]

def kUnitNatB (a b : Fin 2) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  LinearMap.smulRight (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).toLinearMap
    (EuclideanSpace.single a 1)

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (hA a a c c) v`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Both sides reduce to the same expression.

Simplify using `only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h`. Conclude with `h`.
-/
theorem kUnit_diag_comm (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (hA c c a b) w`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Simplify using `[hab, Ne.symm hab] at h ⊢`.

Take the linear combination `(norm := module) h`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Simplify using `[hca] at h ⊢`. Take the linear combination `(norm := module) h`.

Simplify using `[hca, hcb, Ne.symm hcb] at h ⊢`. Take the linear combination `(norm := module) h`.
-/
theorem kUnit_weight_shift (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)`.
-/
theorem kUnit_exists_joint (hA : IsGlRep A) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)

/- English proof (translation)
Establish `h` using `hU c c rfl w w`. Rewrite `h` using `[hw, inner_smul_left, inner_smul_right]`. Establish `hne : inner ℂ w w ≠ (0 : ℂ)` using `inner_self_ne_zero.mpr hw0`. Establish `h2 : (starRingEnd ℂ) z = z` using `mul_right_cancel₀ hne h`. Conclude with `(Complex.conj_eq_iff_re.mp h2).symm`.
-/
theorem kUnit_eig_real (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c

/- English proof (translation)
Establish `hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Establish `h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) = kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ))`. Simplify using `only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith

/- English proof (translation)
Establish `hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S` using `fun c => hS c c rfl`. Set `P : Set (Fin n → ℝ)` to `{μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}`. Establish `hPfin : P.Finite`. Use `(Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)}) (fun c => (Module.End.finite_hasEigenvalue _).preimage (Complex.ofReal_injective.injOn))).subset ?_` and prove the remaining obligations. Introduce and unpack `μ ⟨w, hw, hw0, hμ⟩ c -`.

Use `show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)`. Use `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `Subtype.ext (by simpa using hμ c)`. Introduce `h`.

Conclude with `hw0 (congrArg Subtype.val h)`. Establish `hPne : P.Nonempty`. Take `⟨w, hw, hw0, z, hz⟩` from `kUnit_exists_joint hA Finset.univ S hfd hSc hne`. Use `⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[hz c (Finset.mem_univ c)]`.

Use `congr 1`. Conclude with `kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))`. Take `⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩` from `Set.exists_max_image P kUnitWtLin hPfin hPne`. Use `⟨w, hw, hw0, μ, hμ, ?_⟩` and prove the remaining obligations. Introduce `a b hab hεab`.

Assume the negation of the conclusion as `h`. Establish `hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P` using `⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩`. Conclude with `absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))`.
-/
theorem exists_khw (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

/- English proof (translation)
Introduce `a b hab v hv`. Rewrite `hv`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← hU b a hab.symm u v]`. Conclude with `hv _ (hS b a hab.symm u hu)`.
-/
theorem orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by
  intro a b hab v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hU b a hab.symm u v]
  exact hv _ (hS b a hab.symm u hu)

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Conclude with `hS a b hab _ (Submodule.starProjection_apply_mem S x)`. Introduce `w hw`. Rewrite using `[← map_sub]`. Establish `h1 : x - S.starProjection x ∈ Sᗮ` using `Submodule.sub_starProjection_mem_orthogonal x`.

Establish `h2` using `orthogonal_kStable hU hS a b hab _ h1`. Rewrite `h2` using `[Submodule.mem_orthogonal]`. Rewrite using `[inner_eq_zero_symm]`. Conclude with `h2 w hw`.
-/
theorem starProjection_comm (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw

end KUnit

end ReciprocityTheory.ChartRestriction.DS
