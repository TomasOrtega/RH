import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

namespace GlobalTheory.FockCompare.WeylCreate

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i l hl`. Use `h (l ++ [i]) (by simp [hl])` as an intermediate fact. Simplify `this` using `[List.foldr_append]`. Introduce `h l hl`.

Break down `List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩` into its components or cases. Simplify using `at hl`. Use `h i l' (by simpa using hl)` as an intermediate fact. Simplify `this` using `[List.foldr_append]`.
-/
theorem killed_succ_iff (N : ℕ) (m : M) : Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons i l ih => simp only [List.foldr_cons, ih, map_add, map_smul]`.
-/
theorem foldr_add_smul (l : List I) (β : ℂ) (x y : M) :
    l.foldr (fun i x => a i x) (x + β • y) =
      l.foldr (fun i x => a i x) x + β • l.foldr (fun i x => a i x) y := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_add, map_smul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons i l ih => simp only [List.foldr_cons, ih, map_zero]`.
-/
theorem foldr_zero (l : List I) : l.foldr (fun i x => a i x) (0 : M) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_zero]

/- English proof (translation)
Introduce `I M _ _ a c hc N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `m hm l _`. Establish `h0 : m = 0` using `hm [] rfl`.

Rewrite using `[h0, map_zero]`. Conclude with `foldr_zero l`. Consider the case `succ N ih`. Introduce `m hm`. Rewrite using `[killed_succ_iff]`.

Introduce `i`. Take `⟨β, hβ⟩` from `hc i`. Establish `e : a i (c m) = c (a i m) + β • m`. Use `LinearMap.congr_fun hβ m` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this`.

Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Establish `h1` using `ih (a i m) ((killed_succ_iff N m).1 hm i)`. Introduce `l hl`. Rewrite using `[e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]`.
-/
theorem killed_create : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M),
    (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) →
    ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  intro I M _ _ a c hc N
  induction N with
  | zero =>
    intro m hm l _
    have h0 : m = 0 := hm [] rfl
    rw [h0, map_zero]
    exact foldr_zero l
  | succ N ih =>
    intro m hm
    rw [killed_succ_iff]
    intro i
    obtain ⟨β, hβ⟩ := hc i
    have e : a i (c m) = c (a i m) + β • m := by
      have := LinearMap.congr_fun hβ m
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [← this]; abel
    have h1 := ih (a i m) ((killed_succ_iff N m).1 hm i)
    intro l hl
    rw [e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]

end GlobalTheory.FockCompare.WeylCreate
