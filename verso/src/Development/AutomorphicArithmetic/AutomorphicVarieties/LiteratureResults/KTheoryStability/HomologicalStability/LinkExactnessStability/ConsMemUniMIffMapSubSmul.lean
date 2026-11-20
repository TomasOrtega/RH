import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniModVec

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf⟩`. Use `⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩` and prove the remaining obligations. Use `hf ⟨i, hi⟩ ⟨j, hj⟩` as an intermediate fact. Simplify using `only [hi, dif_pos]`.

Simplify `this` using `[Fin.ext_iff]`. Introduce and unpack `⟨f, hf⟩`. Use `⟨fun i => f i, fun i j => ?_⟩` and prove the remaining obligations. Use `hf i j i.isLt j.isLt` as an intermediate fact. Simplify `this` using `[Fin.ext_iff]`.
-/
theorem mem_uniM_iff_nat (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ f : ℕ → M →ₗ[R] R, ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      f i l[j] = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩
    have := hf ⟨i, hi⟩ ⟨j, hj⟩
    simp only [hi, dif_pos]
    simpa [Fin.ext_iff] using this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => f i, fun i j => ?_⟩
    have := hf i j i.isLt j.isLt
    simpa [Fin.ext_iff] using this

end GlobalTheory.UniModVec

namespace GlobalTheory.UniModVec

/- English proof (translation)
Introduce `R M _ _ _ φ v hv l`. Rewrite using `[mem_uniM_iff_nat, mem_uniM_iff_nat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF⟩`. Use `⟨fun i => F (i+1), fun i j hi hj => ?_⟩` and prove the remaining obligations.

Simplify using `only [List.length_map] at hi hj`. Establish `h1` using `hF (i+1) (j+1) (by simp; omega) (by simp; omega)`. Establish `h2` using `hF (i+1) 0 (by simp; omega) (by simp)`. Simplify using `only [List.getElem_cons_succ, List.getElem_cons_zero] at h1 h2`. Simplify using `only [List.getElem_map, map_sub, map_smul, smul_eq_mul, h1, h2]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨H, hH⟩`. Simplify using `only [List.length_map, List.getElem_map] at hH`. Set `P : M →ₗ[R] M` to `LinearMap.id - φ.smulRight v`. Establish `hP : ∀ x, P x = x - φ x • v` using `fun x => by simp [P]`.

Establish `hPv : P v = 0` using `by rw [hP, hv, one_smul, sub_self]`. Set `F : ℕ → M →ₗ[R] R` to `fun i => match i with`. Consider the case `0 => φ - ∑ k : Fin l.length, φ (l.get k) • (H k).comp P`. Consider the case `k+1 => (H k).comp P`. Use `⟨F, fun i j hi hj => ?_⟩` and prove the remaining obligations.

Simplify using `only [List.length_cons] at hi hj`. Apply the tactic sequence `rcases i with _ | i <;> rcases j with _ | j`. Simplify using `[F, hPv, hv]`. Establish `hj' : j < l.length` using `by omega`. Establish `hF0 : F 0 (l[j]) = φ l[j] - ∑ k : Fin l.length, φ (l.get k) * H k (l[j] - φ l[j] • v)`.

Simplify using `only [F, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, hP, smul_eq_mul]`. Simplify using `only [List.getElem_cons_succ]`. Rewrite using `[hF0, Finset.sum_eq_single ⟨j, hj'⟩]`. Rewrite using `[hH j j hj' hj']`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Rewrite using `[hH k j k.isLt hj', if_neg (fun h => hk (Fin.ext h)), mul_zero]`. Simplify using the standard rewrite rules. Simplify using `[F, hPv]`. Establish `hi' : i < l.length` using `by omega`.

Establish `hj' : j < l.length` using `by omega`. Simplify using `only [F, List.getElem_cons_succ, LinearMap.comp_apply, hP, hH i j hi' hj']`. Simplify using the standard rewrite rules.
-/
theorem cons_mem_uniM_iff_map_proj : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  intro R M _ _ _ φ v hv l
  rw [mem_uniM_iff_nat, mem_uniM_iff_nat]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨fun i => F (i+1), fun i j hi hj => ?_⟩
    simp only [List.length_map] at hi hj
    have h1 := hF (i+1) (j+1) (by simp; omega) (by simp; omega)
    have h2 := hF (i+1) 0 (by simp; omega) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1 h2
    simp only [List.getElem_map, map_sub, map_smul, smul_eq_mul, h1, h2]
    simp
  · rintro ⟨H, hH⟩
    simp only [List.length_map, List.getElem_map] at hH
    let P : M →ₗ[R] M := LinearMap.id - φ.smulRight v
    have hP : ∀ x, P x = x - φ x • v := fun x => by simp [P]
    have hPv : P v = 0 := by rw [hP, hv, one_smul, sub_self]
    let F : ℕ → M →ₗ[R] R := fun i => match i with
      | 0 => φ - ∑ k : Fin l.length, φ (l.get k) • (H k).comp P
      | k+1 => (H k).comp P
    refine ⟨F, fun i j hi hj => ?_⟩
    simp only [List.length_cons] at hi hj
    rcases i with _ | i <;> rcases j with _ | j
    · simp [F, hPv, hv]
    · have hj' : j < l.length := by omega
      have hF0 : F 0 (l[j]) = φ l[j] - ∑ k : Fin l.length, φ (l.get k) * H k (l[j] - φ l[j] • v) := by
        simp only [F, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, hP, smul_eq_mul]
      simp only [List.getElem_cons_succ]
      rw [hF0, Finset.sum_eq_single ⟨j, hj'⟩]
      · rw [hH j j hj' hj']; simp
      · intro k _ hk
        rw [hH k j k.isLt hj', if_neg (fun h => hk (Fin.ext h)), mul_zero]
      · simp
    · simp [F, hPv]
    · have hi' : i < l.length := by omega
      have hj' : j < l.length := by omega
      simp only [F, List.getElem_cons_succ, LinearMap.comp_apply, hP, hH i j hi' hj']
      simp

end GlobalTheory.UniModVec

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.UniModVec.cons_mem_uniM_iff_map_proj`. Consider the case `exact @GlobalTheory.UniModVec.mem_uniM_iff_nat`.
-/
theorem _root_.GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniModVec.cons_mem_uniM_iff_map_proj
  | exact @GlobalTheory.UniModVec.mem_uniM_iff_nat
end
