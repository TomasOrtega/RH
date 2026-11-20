import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

noncomputable section

open Finset Module.End
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace CompactOperatorsAlt

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def Lop (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (a b : Fin n) : Module.End ℂ M :=
  E a b - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)

def Bq (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (y z : M) : ℂ :=
  ∑ a, ∑ b, ⟪Lop E μ a b y, Lop E μ a b z⟫_ℂ

def Qop (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) : Module.End ℂ M :=
  ∑ a, ∑ b, (adjSign ε a b • E b a - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)) * Lop E μ a b

/- English proof (translation)
Simplify using `only [qf, Bq, Lop, map_sum, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_self_eq_norm_sq]`.
-/
theorem qf_eq (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (x : M) :
    qf E μ x = RCLike.re (Bq E μ x x) := by
  simp only [qf, Bq, Lop, map_sum, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    inner_self_eq_norm_sq]

/- English proof (translation)
Simplify using `only [Bq, Qop, inner_sum, LinearMap.sum_apply, Module.End.mul_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Generalize the expression as in `Lop E μ a b z = w`. Simplify using `only [Lop, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hU a b y w]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Bq_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (μ : Fin n → ℝ) (y z : M) :
    Bq E μ y z = ⟪y, Qop ε E μ z⟫_ℂ := by
  simp only [Bq, Qop, inner_sum, LinearMap.sum_apply, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  generalize Lop E μ a b z = w
  simp only [Lop, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, hU a b y w]
  split_ifs <;> simp

/- English proof (translation)
Establish `h` using `hE c c a a`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Both sides reduce to the same expression. Rewrite `h` using `[if_neg hca, if_neg (Ne.symm hca), sub_zero]`.

Conclude with `sub_eq_zero.mp h`.
-/
theorem glRep_diag {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a c : Fin n) :
    E c c * E a a = E a a * E c c := by
  have h := hE c c a a
  by_cases hca : c = a
  · subst hca
    rfl
  · rw [if_neg hca, if_neg (Ne.symm hca), sub_zero] at h
    exact sub_eq_zero.mp h

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Simplify using `only [casimirK, casimir, Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [adjSign]`. Apply the tactic sequence `split_ifs <;> simp [two_smul]`.
-/
theorem sum_adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    ∑ a, ∑ b, adjSign ε a b • (E b a * E a b) = (2 : ℂ) • casimirK ε E - casimir E := by
  rw [Finset.sum_comm]
  simp only [casimirK, casimir, Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [adjSign]
  split_ifs <;> simp [two_smul]

/- English proof (translation)
Rewrite using `[← sum_adj]`. Simplify using `only [Qop, Lop]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `key : ∀ b, (adjSign ε a b • E b a - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)) * (E a b - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)) = adjSign ε a b • (E b a * E a b) + if a = b then ((E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) * (E a a - (μ a : ℂ) • (1 …`.

Introduce `b`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [adjSign, if_true, one_smul]`. Normalize the expressions using the abelian group laws.

Simplify using `[smul_mul_assoc]`. Simplify using `only [key, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem Qop_eq (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) :
    Qop ε E μ = ((2 : ℂ) • casimirK ε E - casimir E) +
      ∑ a, ((E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) * (E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) - E a a * E a a) := by
  rw [← sum_adj]
  simp only [Qop, Lop]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : ∀ b, (adjSign ε a b • E b a - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)) *
      (E a b - (if a = b then (μ a : ℂ) else 0) • (1 : Module.End ℂ M)) =
      adjSign ε a b • (E b a * E a b) + if a = b then
        ((E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) * (E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) -
          E a a * E a a) else 0 := by
    intro b
    split_ifs with h
    · subst h
      simp only [adjSign, if_true, one_smul]
      abel
    · simp [smul_mul_assoc]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Establish `hc : ∀ c d, Commute (E c d) (casimir E)`. Introduce `c d`. Establish `key : ∀ a b, E c d * (E a b * E b a) - E a b * E b a * E c d = ((if d = a then E c b else 0) - (if b = c then E a d else 0)) * E b a + E a b * ((if d = b then E c a else 0) - (if a = c then E b d else 0))`. Introduce `a b`. Rewrite using `[← hE c d a b, ← hE c d b a]`.

Use `noncomm_ring`. Use `show E c d * casimir E = casimir E * E c d`. Rewrite using `[← sub_eq_zero, casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]`. Simplify using `[sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite]`.

Conclude with `Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => (hc a b).mul_left (hc b a)`.
-/
theorem comm_casimir_casimirK {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (ε : Fin n → Bool) :
    Commute (casimirK ε E) (casimir E) := by
  have hc : ∀ c d, Commute (E c d) (casimir E) := by
    intro c d
    have key : ∀ a b, E c d * (E a b * E b a) - E a b * E b a * E c d =
        ((if d = a then E c b else 0) - (if b = c then E a d else 0)) * E b a +
          E a b * ((if d = b then E c a else 0) - (if a = c then E b d else 0)) := by
      intro a b
      rw [← hE c d a b, ← hE c d b a]
      noncomm_ring
    show E c d * casimir E = casimir E * E c d
    rw [← sub_eq_zero, casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
    simp [sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
      mul_ite]
  exact Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => (hc a b).mul_left (hc b a)

/- English proof (translation)
Rewrite using `[Qop_eq]`. Use `((hA1.smul_right _).sub_right hA2).add_right (Commute.sum_right _ _ _ fun a _ => ?_)` and prove the remaining obligations. Establish `h1 : Commute A (E a a - (μ a : ℂ) • (1 : Module.End ℂ M))` using `(hA3 a).sub_right ((Commute.one_right A).smul_right _)`. Conclude with `(h1.mul_right h1).sub_right ((hA3 a).mul_right (hA3 a))`.
-/
theorem comm_Qop {E : Fin n → Fin n → Module.End ℂ M} (ε : Fin n → Bool) (μ : Fin n → ℝ)
    (A : Module.End ℂ M) (hA1 : Commute A (casimirK ε E)) (hA2 : Commute A (casimir E)) (hA3 : ∀ a, Commute A (E a a)) :
    Commute A (Qop ε E μ) := by
  rw [Qop_eq]
  refine ((hA1.smul_right _).sub_right hA2).add_right (Commute.sum_right _ _ _ fun a _ => ?_)
  have h1 : Commute A (E a a - (μ a : ℂ) • (1 : Module.End ℂ M)) := (hA3 a).sub_right ((Commute.one_right A).smul_right _)
  exact (h1.mul_right h1).sub_right ((hA3 a).mul_right (hA3 a))

/- English proof (translation)
Distinguish the cases in `hy0 : y = 0`. Simplify using `[hy0]`. Establish `hα : (starRingEnd ℂ) α = α`. Establish `h` using `hA y y`. Rewrite `h` using `[hy, inner_smul_left, inner_smul_right]`.

Conclude with `mul_right_cancel₀ (inner_self_ne_zero.2 hy0) h`. Establish `h` using `hA y (P z)`. Rewrite `h` using `[hy, inner_smul_left, hα]`. Establish `h2 : A (P z) = β • P z` using `by rw [← Module.End.mul_apply, hP.eq, Module.End.mul_apply, hz, map_smul]`. Rewrite `h` using `[h2, inner_smul_right]`.

Conclude with `(mul_eq_mul_right_iff.1 h).resolve_left hαβ`.
-/
theorem orth {A P : Module.End ℂ M} (hA : ∀ x y : M, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (hP : Commute A P) {y z : M} {α β : ℂ}
    (hy : A y = α • y) (hz : A z = β • z) (hαβ : α ≠ β) : ⟪y, P z⟫_ℂ = 0 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hα : (starRingEnd ℂ) α = α := by
    have h := hA y y
    rw [hy, inner_smul_left, inner_smul_right] at h
    exact mul_right_cancel₀ (inner_self_ne_zero.2 hy0) h
  have h := hA y (P z)
  rw [hy, inner_smul_left, hα] at h
  have h2 : A (P z) = β • P z := by rw [← Module.End.mul_apply, hP.eq, Module.End.mul_apply, hz, map_smul]
  rw [h2, inner_smul_right] at h
  exact (mul_eq_mul_right_iff.1 h).resolve_left hαβ

/- English proof (translation)
Establish `h` using `hA y y`. Rewrite `h` using `[hy, inner_smul_left, inner_smul_right]`. Establish `h2` using `mul_right_cancel₀ (inner_self_ne_zero.2 hy0) h`. Conclude with `Complex.conj_eq_iff_re.1 h2`.
-/
theorem real_of_eigen {A : Module.End ℂ M} (hA : ∀ x y : M, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) {y : M} {α : ℂ}
    (hy : A y = α • y) (hy0 : y ≠ 0) : ((α.re : ℝ) : ℂ) = α := by
  have h := hA y y
  rw [hy, inner_smul_left, inner_smul_right] at h
  have h2 := mul_right_cancel₀ (inner_self_ne_zero.2 hy0) h
  exact Complex.conj_eq_iff_re.1 h2

def Aop (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Option (Fin n) → Module.End ℂ M
  | none => casimirK ε E
  | some c => E c c

end CompactOperatorsAlt

/- English proof (translation)
Establish `key : ∀ a b, E c d * (E a b * E b a) - E a b * E b a * E c d = ((if d = a then E c b else 0) - (if b = c then E a d else 0)) * E b a + E a b * ((if d = b then E c a else 0) - (if a = c then E b d else 0))`. Introduce `a b`. Rewrite using `[← hE c d a b, ← hE c d b a]`. Use `noncomm_ring`. Use `show E c d * casimir E = casimir E * E c d`.

Rewrite using `[← sub_eq_zero, casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]`. Simplify using `[sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite]`.
-/
private theorem commute_E_casimir_of_isGlRep {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (c d : Fin n) :
    Commute (E c d) (casimir E) := by
  have key : ∀ a b, E c d * (E a b * E b a) - E a b * E b a * E c d =
      ((if d = a then E c b else 0) - (if b = c then E a d else 0)) * E b a +
        E a b * ((if d = b then E c a else 0) - (if a = c then E b d else 0)) := by
    intro a b
    rw [← hE c d a b, ← hE c d b a]
    noncomm_ring
  show E c d * casimir E = casimir E * E c d
  rw [← sub_eq_zero, casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
  simp [sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
    mul_ite]

/- English proof (translation)
Establish `h1` using `hE c c a b`. Establish `h2` using `hE c c b a`. Use `show E c c * (E a b * E b a) = E a b * E b a * E c c`. Rewrite using `[← sub_eq_zero]`. Establish `h3 : E c c * (E a b * E b a) - E a b * E b a * E c c = (E c c * E a b - E a b * E c c) * E b a + E a b * (E c c * E b a - E b a * E c c)` using `by noncomm_ring`.

Rewrite using `[h3, h1, h2]`. Use `clear h1 h2 h3 hE`. Apply the tactic sequence `split_ifs <;> subst_vars <;> simp_all`.
-/
private theorem commute_E_diag_E_mul_E_of_isGlRep {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (c a b : Fin n) :
    Commute (E c c) (E a b * E b a) := by
  have h1 := hE c c a b
  have h2 := hE c c b a
  show E c c * (E a b * E b a) = E a b * E b a * E c c
  rw [← sub_eq_zero]
  have h3 : E c c * (E a b * E b a) - E a b * E b a * E c c =
      (E c c * E a b - E a b * E c c) * E b a + E a b * (E c c * E b a - E b a * E c c) := by
    noncomm_ring
  rw [h3, h1, h2]
  clear h1 h2 h3 hE
  split_ifs <;> subst_vars <;> simp_all

open CompactOperatorsAlt in
/- English proof (translation)
Introduce `_ n ε M _ _ E hE hU μ S x hx0 hK hq`. Take `⟨F, hFd, hFK, hxF⟩` from `hK`. Establish `hstab : ∀ o, ∀ v ∈ F, Aop ε E o v ∈ F`. Introduce `o v hv`. Consider the cases of `o with`.

Consider the case `none => show casimirK ε E v ∈ F`. Rewrite using `[casimirK, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations.

Establish `hε : ε b = ε a` using `(Finset.mem_filter.mp hb).2`. Conclude with `hFK a b hε.symm _ (hFK b a hε v hv)`. Consider the case `some c => exact hFK c c rfl v hv`. Establish `hsa : ∀ o (u v : M), ⟪Aop ε E o u, v⟫_ℂ = ⟪u, Aop ε E o v⟫_ℂ`. Introduce `o u v`.

Consider the cases of `o with`. Consider the case `none => show ⟪casimirK ε E u, v⟫_ℂ = ⟪u, casimirK ε E v⟫_ℂ`. Simplify using `only [casimirK, LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hε : ε b = ε a` using `(Finset.mem_filter.mp hb).2`.

Rewrite using `[hU a b, hU b a u]`. Simplify using `[adjSign, hε]`. Consider the case `some c => show ⟪E c c u, v⟫_ℂ = ⟪u, E c c v⟫_ℂ`. Rewrite using `[hU c c]`. Simplify using `[adjSign]`.

Establish `hKc : ∀ c, Commute (E c c) (casimirK ε E)` using `fun c => Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => commute_E_diag_E_mul_E_of_isGlRep hE c a b`. Establish `hcomm : ∀ o o', Commute (Aop ε E o) (Aop ε E o')`. Introduce `o o'`. Consider the cases of `o with`. Consider the case `none`.

Consider the cases of `o' with`. Consider the case `none => exact Commute.refl _`. Consider the case `some d => exact (hKc d).symm`. Consider the case `some c`. Consider the cases of `o' with`.

Consider the case `none => exact hKc c`. Consider the case `some d => exact glRep_diag hE d c`. Establish `hQ : ∀ o, Commute (Aop ε E o) (Qop ε E μ)`. Introduce `o`. Consider the cases of `o with`.

Consider the case `none => exact comm_Qop ε μ _ (Commute.refl _) (comm_casimir_casimirK hE ε) fun a => (hKc a).symm`. Consider the case `some c => exact comm_Qop ε μ _ (hKc c) (commute_E_casimir_of_isGlRep hE c c) fun a => glRep_diag hE a c`. Set `T : Option (Fin n) → Module.End ℂ F` to `fun o => (Aop ε E o).restrict (hstab o)`. Establish `hTs : ∀ o, (T o).IsSymmetric` using `fun o u v => by`. Simplify using `only [T, Submodule.coe_inner, LinearMap.restrict_coe_apply]`.

Conclude with `hsa o u v`. Establish `hTc : Pairwise (Function.onFun Commute T)` using `fun o o' _ => by show T o * T o' = T o' * T o`. Use extensionality with `u`. Simplify using `only [T, Module.End.mul_apply, LinearMap.restrict_coe_apply]`. Rewrite using `[← Module.End.mul_apply, (hcomm o o').eq, Module.End.mul_apply]`.

Use `haveI := hFd`. Establish `htop` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hTc`. Establish `hx : (⟨x, hxF⟩ : F) ∈ ⨆ χ : Option (Fin n) → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i)`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Take `⟨f, hfmem, hfsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx`. Use `set s := f.support with hs`. Set `c : (Option (Fin n) → ℂ) → M` to `fun χ => ((f χ : F) : M)`. Establish `hxs : x = ∑ χ ∈ s, c χ`. Establish `h` using `congrArg Subtype.val hfsum`.

Rewrite `h` using `[Finsupp.sum, Submodule.coe_sum]`. Conclude with `h.symm`. Establish `heig : ∀ χ o, Aop ε E o (c χ) = χ o • c χ`. Introduce `χ o`. Establish `h` using `(Submodule.mem_iInf _).mp (hfmem χ) o`.

Rewrite `h` using `[Module.End.mem_eigenspace_iff]`. Establish `h2` using `congrArg Subtype.val h`. Simplify `h2` using `[T, LinearMap.restrict_coe_apply]`. Establish `hne : ∀ χ ∈ s, c χ ≠ 0`. Introduce `χ hχ h`.

Conclude with `(Finsupp.mem_support_iff.mp hχ) (Subtype.ext h)`. Establish `hoff : ∀ χ ψ, χ ≠ ψ → ∀ P : Module.End ℂ M, (∀ o, Commute (Aop ε E o) P) → ⟪c χ, P (c ψ)⟫_ℂ = 0`. Introduce `χ ψ hχψ P hP`. Take `⟨o, ho⟩` from `Function.ne_iff.mp hχψ`. Conclude with `orth (hsa o) (hP o) (heig χ o) (heig ψ o) ho`.

Establish `hdiagsum : ∀ P : Module.End ℂ M, (∀ o, Commute (Aop ε E o) P) → ⟪x, P x⟫_ℂ = ∑ χ ∈ s, ⟪c χ, P (c χ)⟫_ℂ`. Introduce `P hP`. Rewrite using `[hxs, map_sum, sum_inner]`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`.

Conclude with `Finset.sum_eq_single χ (fun ψ _ hψ => hoff χ ψ (Ne.symm hψ) P hP) (fun h => absurd hχ h)`. Establish `hqf : qf E μ x = ∑ χ ∈ s, qf E μ (c χ)`. Rewrite using `[qf_eq, Bq_eq ε hU, hdiagsum _ hQ, map_sum]`. Use `Finset.sum_congr rfl fun χ _ => ?_` and prove the remaining obligations. Rewrite using `[qf_eq, Bq_eq ε hU]`.

Establish `hnorm : ‖x‖ ^ 2 = ∑ χ ∈ s, ‖c χ‖ ^ 2`. Establish `h` using `hdiagsum 1 (fun o => Commute.one_right _)`. Simplify using `only [Module.End.one_apply] at h`. Establish `h2` using `congrArg RCLike.re h`. Rewrite `h2` using `[map_sum]`.

Simplify using `only [inner_self_eq_norm_sq] at h2`. Conclude with `h2`. Establish `hgood : ∀ χ ∈ s, Good ε E (fun a => (χ (some a)).re) (χ none).re (c χ)`. Introduce `χ hχ`. Use `⟨hne χ hχ, ⟨F, hFd, hFK, (f χ).2⟩, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[real_of_eigen (hsa _) (heig χ (some a)) (hne χ hχ)]`. Conclude with `heig χ (some a)`. Rewrite using `[real_of_eigen (hsa _) (heig χ none) (hne χ hχ)]`. Conclude with `heig χ none`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hlt : ∀ χ ∈ s, S * ‖c χ‖ ^ 2 < qf E μ (c χ)` using `fun χ hχ => hcon _ _ _ (hgood χ hχ)`. Establish `hsne : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`.

Apply `hx0` to reduce the goal to its premises. Rewrite using `[hxs, h, Finset.sum_empty]`. Establish `h` using `Finset.sum_lt_sum_of_nonempty hsne hlt`. Rewrite `h` using `[← Finset.mul_sum, ← hnorm, ← hqf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem comp_proof : SqId → Comp := by
  intro _ n ε M _ _ E hE hU μ S x hx0 hK hq
  obtain ⟨F, hFd, hFK, hxF⟩ := hK
  have hstab : ∀ o, ∀ v ∈ F, Aop ε E o v ∈ F := by
    intro o v hv
    cases o with
    | none =>
      show casimirK ε E v ∈ F
      rw [casimirK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun b hb => ?_
      have hε : ε b = ε a := (Finset.mem_filter.mp hb).2
      exact hFK a b hε.symm _ (hFK b a hε v hv)
    | some c => exact hFK c c rfl v hv
  have hsa : ∀ o (u v : M), ⟪Aop ε E o u, v⟫_ℂ = ⟪u, Aop ε E o v⟫_ℂ := by
    intro o u v
    cases o with
    | none =>
      show ⟪casimirK ε E u, v⟫_ℂ = ⟪u, casimirK ε E v⟫_ℂ
      simp only [casimirK, LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
      have hε : ε b = ε a := (Finset.mem_filter.mp hb).2
      rw [hU a b, hU b a u]
      simp [adjSign, hε]
    | some c =>
      show ⟪E c c u, v⟫_ℂ = ⟪u, E c c v⟫_ℂ
      rw [hU c c]
      simp [adjSign]
  have hKc : ∀ c, Commute (E c c) (casimirK ε E) := fun c =>
    Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => commute_E_diag_E_mul_E_of_isGlRep hE c a b
  have hcomm : ∀ o o', Commute (Aop ε E o) (Aop ε E o') := by
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none => exact Commute.refl _
      | some d => exact (hKc d).symm
    | some c =>
      cases o' with
      | none => exact hKc c
      | some d => exact glRep_diag hE d c
  have hQ : ∀ o, Commute (Aop ε E o) (Qop ε E μ) := by
    intro o
    cases o with
    | none => exact comm_Qop ε μ _ (Commute.refl _) (comm_casimir_casimirK hE ε) fun a => (hKc a).symm
    | some c => exact comm_Qop ε μ _ (hKc c) (commute_E_casimir_of_isGlRep hE c c) fun a => glRep_diag hE a c
  let T : Option (Fin n) → Module.End ℂ F := fun o => (Aop ε E o).restrict (hstab o)
  have hTs : ∀ o, (T o).IsSymmetric := fun o u v => by
    simp only [T, Submodule.coe_inner, LinearMap.restrict_coe_apply]
    exact hsa o u v
  have hTc : Pairwise (Function.onFun Commute T) := fun o o' _ => by
    show T o * T o' = T o' * T o
    ext u
    simp only [T, Module.End.mul_apply, LinearMap.restrict_coe_apply]
    rw [← Module.End.mul_apply, (hcomm o o').eq, Module.End.mul_apply]
  haveI := hFd
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hTc
  have hx : (⟨x, hxF⟩ : F) ∈ ⨆ χ : Option (Fin n) → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨f, hfmem, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  set s := f.support with hs
  let c : (Option (Fin n) → ℂ) → M := fun χ => ((f χ : F) : M)
  have hxs : x = ∑ χ ∈ s, c χ := by
    have h := congrArg Subtype.val hfsum
    rw [Finsupp.sum, Submodule.coe_sum] at h
    exact h.symm
  have heig : ∀ χ o, Aop ε E o (c χ) = χ o • c χ := by
    intro χ o
    have h := (Submodule.mem_iInf _).mp (hfmem χ) o
    rw [Module.End.mem_eigenspace_iff] at h
    have h2 := congrArg Subtype.val h
    simpa [T, LinearMap.restrict_coe_apply] using h2
  have hne : ∀ χ ∈ s, c χ ≠ 0 := by
    intro χ hχ h
    exact (Finsupp.mem_support_iff.mp hχ) (Subtype.ext h)
  have hoff : ∀ χ ψ, χ ≠ ψ → ∀ P : Module.End ℂ M, (∀ o, Commute (Aop ε E o) P) →
      ⟪c χ, P (c ψ)⟫_ℂ = 0 := by
    intro χ ψ hχψ P hP
    obtain ⟨o, ho⟩ := Function.ne_iff.mp hχψ
    exact orth (hsa o) (hP o) (heig χ o) (heig ψ o) ho
  have hdiagsum : ∀ P : Module.End ℂ M, (∀ o, Commute (Aop ε E o) P) →
      ⟪x, P x⟫_ℂ = ∑ χ ∈ s, ⟪c χ, P (c χ)⟫_ℂ := by
    intro P hP
    rw [hxs, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single χ (fun ψ _ hψ => hoff χ ψ (Ne.symm hψ) P hP) (fun h => absurd hχ h)
  have hqf : qf E μ x = ∑ χ ∈ s, qf E μ (c χ) := by
    rw [qf_eq, Bq_eq ε hU, hdiagsum _ hQ, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [qf_eq, Bq_eq ε hU]
  have hnorm : ‖x‖ ^ 2 = ∑ χ ∈ s, ‖c χ‖ ^ 2 := by
    have h := hdiagsum 1 (fun o => Commute.one_right _)
    simp only [Module.End.one_apply] at h
    have h2 := congrArg RCLike.re h
    rw [map_sum] at h2
    simp only [inner_self_eq_norm_sq] at h2
    exact h2
  have hgood : ∀ χ ∈ s, Good ε E (fun a => (χ (some a)).re) (χ none).re (c χ) := by
    intro χ hχ
    refine ⟨hne χ hχ, ⟨F, hFd, hFK, (f χ).2⟩, fun a => ?_, ?_⟩
    · rw [real_of_eigen (hsa _) (heig χ (some a)) (hne χ hχ)]
      exact heig χ (some a)
    · rw [real_of_eigen (hsa _) (heig χ none) (hne χ hχ)]
      exact heig χ none
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ χ ∈ s, S * ‖c χ‖ ^ 2 < qf E μ (c χ) := fun χ hχ => hcon _ _ _ (hgood χ hχ)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hx0
    rw [hxs, h, Finset.sum_empty]
  have h := Finset.sum_lt_sum_of_nonempty hsne hlt
  rw [← Finset.mul_sum, ← hnorm, ← hqf] at h
  linarith

end PositivityTheory.RgHe3
