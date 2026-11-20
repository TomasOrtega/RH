import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrixStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorTypeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMapStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApplyStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentityStatement
open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]`. Establish `: ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) = ∏ t ∈ Finset.univ.erase s, (u + ν t)` using `Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]`. Rewrite using `[this]`. Simplify using `only [if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_add_ite_shift {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]
  have : ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) =
      ∏ t ∈ Finset.univ.erase s, (u + ν t) :=
    Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  rw [this]; simp only [if_true]; ring

/- English proof (translation)
Introduce `V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w`. Consider the cases of `n with`. Consider the case `zero => exact j.elim0`. Consider the case `succ m`. Set `M : (Fin (m + 1) → Fin (m + 1) → Module.End ℂ W) → Module.End ℂ (Fin (m + 1) → W)` to `fun B => LinearMap.pi fun a => ∑ k, (B a k).comp (LinearMap.proj k)`.

Establish `hM : ∀ B y a, M B y a = ∑ k, B a k (y k)`. Introduce `B y a`. Simplify using `[M, LinearMap.sum_apply]`. Set `Ω` to `M (fun l a => E' a l)`. Set `X : ℂ → Module.End ℂ (Fin (m + 1) → W)` to `fun u => M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1))`.

Use `choose c hc using fun a k : Fin (m + 1) => GlobalTheory.T.exists_qminor_sub_eq_polynomial (Module.End ℂ W) (m + 1) m E' (Fin.succAbove a) (Fin.succAbove k) 1`. Establish `hXc : ∀ u, X u = ∑ i ∈ Finset.range (m + 1), u ^ i • M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • c a k i)`. Introduce `u`. Use `LinearMap.ext fun y => funext fun a => ?_` and prove the remaining obligations. Simplify using `only [X, hM, hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _` and prove the remaining obligations. Establish `hΩ : ∀ (u : ℂ) (y : Fin (m + 1) → W), u • X u y + Ω (X u y) = (∏ s, (u + ν s)) • y`. Introduce `u y`. Use function extensionality and compare the values at `l`.

Establish `h1 : (u • X u y + Ω (X u y)) l = ∑ a, Tm E' u a l (X u y a)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Ω, hM, Tm, LinearMap.add_apply, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using `[Finset.smul_sum]`.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ k : Fin (m + 1), ∑ a : Fin (m + 1), Tm E' u a l ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)) = if l = k then qdet E' u (y k) else 0`. Introduce `k`.

Use `LinearMap.congr_fun (GlobalTheory.T.capelli_left_comatrix_qminor_eq (Module.End ℂ W) m E' hE' u k l) (y k)` as an intermediate fact. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this`. Simplify using `only [LinearMap.smul_apply, map_smul]`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[h1]`. Simplify using `only [X, hM, map_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [h2]`. Simplify using `[hq]`.

Take `⟨v, hv, hXv⟩` from `GlobalTheory.T.exists_eigenSplit_of_resolventIdentity (Fin (m + 1) → W) (m + 1) Ω X (m + 1) _ ν hν hXc hΩ (Pi.single j w)`. Establish `hqι : ∀ u y, qdet E u (ι y) = (∏ s, (u + ν s)) • ι y`. Introduce `u y`. Rewrite using `[← map_smul, ← hq]`. Conclude with `(GlobalTheory.T.qminor_intertwining_apply V W (m + 1) (m + 1) E E' ι hι id id u y).symm`.

Establish `hmu : ∀ (u : ℂ) (y : Fin (m + 1) → W), qdet E u (∑ a, x a (ι (y a))) = (∏ s, (u + ν s)) • (∑ a, x a (ι (y a))) + ∑ a, x a (ι (X u y a))`. Introduce `u y`. Establish `h3 : ∀ k : Fin (m + 1), qdet E u (x k (ι (y k))) = (∏ s, (u + ν s)) • x k (ι (y k)) + ∑ a : Fin (m + 1), x a (ι ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)))`. Introduce `k`. Use `LinearMap.congr_fun (GlobalTheory.T.capelliDet_mul_vectorType (Module.End ℂ V) m E x hE hx u k) (ι (y k))` as an intermediate fact.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.add_apply, hqι, map_smul] at this`. Rewrite using `[this]`. Simplify using `only [LinearMap.smul_apply, map_smul, GlobalTheory.T.qminor_intertwining_apply V W (m + 1) m E E' ι hι]`. Simplify using `only [map_sum, h3, Finset.sum_add_distrib, Finset.smul_sum, X, hM]`. Rewrite using `[Finset.sum_comm]`.

Use `⟨v, ?_, fun s u => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ a, ∑ s, x a (ι (v s a)) = x a (ι ((Pi.single j w : Fin (m + 1) → W) a))`. Introduce `a`. Rewrite using `[hv]`.

Simplify using `[map_sum]`. Simplify using `only [this]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules. Rewrite using `[hmu, hXv, prod_add_ite_shift, add_smul]`. Simplify using `only [Pi.smul_apply, map_smul, Finset.smul_sum]`.
-/
theorem qdet_vector_multiplier_shift_plus : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), GlRel E → GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t + if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  cases n with
  | zero => exact j.elim0
  | succ m =>
  let M : (Fin (m + 1) → Fin (m + 1) → Module.End ℂ W) → Module.End ℂ (Fin (m + 1) → W) :=
    fun B => LinearMap.pi fun a => ∑ k, (B a k).comp (LinearMap.proj k)
  have hM : ∀ B y a, M B y a = ∑ k, B a k (y k) := by
    intro B y a
    simp [M, LinearMap.sum_apply]
  let Ω := M (fun l a => E' a l)
  let X : ℂ → Module.End ℂ (Fin (m + 1) → W) := fun u => M (fun a k =>
    ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1))
  choose c hc using fun a k : Fin (m + 1) =>
    GlobalTheory.T.exists_qminor_sub_eq_polynomial (Module.End ℂ W) (m + 1) m E' (Fin.succAbove a) (Fin.succAbove k) 1
  have hXc : ∀ u, X u = ∑ i ∈ Finset.range (m + 1), u ^ i •
      M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • c a k i) := by
    intro u
    refine LinearMap.ext fun y => funext fun a => ?_
    simp only [X, hM, hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  have hΩ : ∀ (u : ℂ) (y : Fin (m + 1) → W),
      u • X u y + Ω (X u y) = (∏ s, (u + ν s)) • y := by
    intro u y
    funext l
    have h1 : (u • X u y + Ω (X u y)) l = ∑ a, Tm E' u a l (X u y a) := by
      simp only [Pi.add_apply, Pi.smul_apply, Ω, hM, Tm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp [Finset.smul_sum]
      · intro b _ hb; simp [hb]
      · simp
    have h2 : ∀ k : Fin (m + 1), ∑ a : Fin (m + 1), Tm E' u a l ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)) = if l = k then qdet E' u (y k) else 0 := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelli_left_comatrix_qminor_eq (Module.End ℂ W) m E' hE' u k l) (y k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
      simp only [LinearMap.smul_apply, map_smul]
      rw [this]
      split_ifs <;> simp
    rw [h1]
    simp only [X, hM, map_sum]
    rw [Finset.sum_comm]
    simp only [h2]
    simp [hq]
  obtain ⟨v, hv, hXv⟩ := GlobalTheory.T.exists_eigenSplit_of_resolventIdentity (Fin (m + 1) → W) (m + 1) Ω X (m + 1) _ ν hν hXc hΩ
    (Pi.single j w)
  have hqι : ∀ u y, qdet E u (ι y) = (∏ s, (u + ν s)) • ι y := by
    intro u y
    rw [← map_smul, ← hq]
    exact (GlobalTheory.T.qminor_intertwining_apply V W (m + 1) (m + 1) E E' ι hι id id u y).symm
  have hmu : ∀ (u : ℂ) (y : Fin (m + 1) → W), qdet E u (∑ a, x a (ι (y a))) =
      (∏ s, (u + ν s)) • (∑ a, x a (ι (y a))) + ∑ a, x a (ι (X u y a)) := by
    intro u y
    have h3 : ∀ k : Fin (m + 1), qdet E u (x k (ι (y k))) = (∏ s, (u + ν s)) • x k (ι (y k)) +
        ∑ a : Fin (m + 1), x a (ι ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k))) := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelliDet_mul_vectorType (Module.End ℂ V) m E x hE hx u k) (ι (y k))
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
        LinearMap.add_apply, hqι, map_smul] at this
      rw [this]
      simp only [LinearMap.smul_apply, map_smul, GlobalTheory.T.qminor_intertwining_apply V W (m + 1) m E E' ι hι]
    simp only [map_sum, h3, Finset.sum_add_distrib, Finset.smul_sum, X, hM]
    rw [Finset.sum_comm]
  refine ⟨v, ?_, fun s u => ?_⟩
  · rw [Finset.sum_comm]
    have : ∀ a, ∑ s, x a (ι (v s a)) = x a (ι ((Pi.single j w : Fin (m + 1) → W) a)) := by
      intro a
      rw [hv]
      simp [map_sum]
    simp only [this]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  · rw [hmu, hXv, prod_add_ite_shift, add_smul]
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]

end GlobalTheory
