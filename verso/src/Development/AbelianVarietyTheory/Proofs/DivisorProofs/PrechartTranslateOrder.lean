import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslationMapStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _ _ G _ _ hG N hN q c hc s₀ u`. Establish `hinj : ∀ ψ ψ' : c.C →ₐ[R] K, torsMap ψ c.j = torsMap ψ' c.j → ψ = ψ'` using `fun ψ ψ' h => (c.bij K).injOn (Set.mem_univ _) (Set.mem_univ _) h`. Establish `hpowval : ∀ (x : Tors G N K) (n : ℕ), (x ^ n).1 = x.1 ^ n`. Introduce `x n`. Proceed by induction on `n with`.

Consider the case `zero => rw [pow_zero, pow_zero, tors_one_val]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, tors_mul_val, ih]`. Establish `hkill : ∀ x : Tors G N K, x ^ N = 1` using `fun x => Subtype.ext (by rw [hpowval, x.2, tors_one_val])`. Establish `hpow : ∀ (ψ : c.C →ₐ[R] K) (n : ℕ), ∃ ψ' : c.C →ₐ[R] K, torsMap ψ' c.j = torsMap ψ c.j ^ (n + 1)`. Introduce `ψ n`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨ψ, by rw [zero_add, pow_one]⟩`. Consider the case `succ n ih`. Take `⟨ψ', h⟩` from `ih`. Take `⟨ψ'', h'⟩` from `hc.2 K ψ' ψ`.

Conclude with `⟨ψ'', by rw [h', h, ← pow_succ]⟩`. Establish `hinv : ∀ ψ : c.C →ₐ[R] K, ∃ ψ' : c.C →ₐ[R] K, torsMap ψ' c.j = (torsMap ψ c.j)⁻¹`. Introduce `ψ`. Take `⟨ψ', h⟩` from `hpow ψ (2 * N - 2)`. Use `⟨ψ', ?_⟩` and prove the remaining obligations.

Rewrite using `[h]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, show 2 * N - 2 + 1 + 1 = N * 2 by omega, pow_mul, hkill, one_pow]`. Set `f : Tors G N K → K` to `fun x => if h : ∃ ψ : c.C →ₐ[R] K, x = s₀ * torsMap ψ c.j then h.choose u else 0`. Establish `hf : ∀ ψ : c.C →ₐ[R] K, f (s₀ * torsMap ψ c.j) = ψ u`.

Introduce `ψ`. Establish `h : ∃ ψ' : c.C →ₐ[R] K, s₀ * torsMap ψ c.j = s₀ * torsMap ψ' c.j` using `⟨ψ, rfl⟩`. Establish `e : ψ = h.choose` using `hinj _ _ (mul_left_cancel h.choose_spec)`. Use `show (if h : ∃ ψ' : c.C →ₐ[R] K, s₀ * torsMap ψ c.j = s₀ * torsMap ψ' c.j then h.choose u else 0) = _`. Rewrite using `[dif_pos h, ← e]`.

Establish `hf0 : ∀ x, (∀ ψ : c.C →ₐ[R] K, x ≠ s₀ * torsMap ψ c.j) → f x = 0`. Introduce `x hx`. Conclude with `dif_neg (fun ⟨ψ, h⟩ => hx ψ h)`. Establish `hmem : ∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j)`. Introduce `s`.

Distinguish the cases in `h : ∃ ψ₁ ψ₂ : c.C →ₐ[R] K, s * torsMap ψ₁ c.j = s₀ * torsMap ψ₂ c.j`. Take `⟨ψ₁, ψ₂, h⟩` from `h`. Take `⟨ψ₃, h₃⟩` from `hinv ψ₁`. Take `⟨ψ₀, h₀⟩` from `hc.2 K ψ₂ ψ₃`. Establish `hs : s = s₀ * torsMap ψ₀ c.j`.

Rewrite using `[h₀, h₃, ← _root_.mul_assoc, ← h, mul_inv_cancel_right]`. Take `⟨T, hT⟩` from `GlobalTheory.T.prechart_translation_map R K G N q c hc ψ₀`. Use `⟨T u, fun ψ => ?_⟩` and prove the remaining obligations. Rewrite using `[hs, _root_.mul_assoc, ← hT, hf]`. Both sides reduce to the same expression.

Use `⟨0, fun ψ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, hf0 _ (fun ψ' h' => h ⟨ψ, ψ', h'⟩)]`. Take `⟨k, hk⟩` from `GlobalTheory.T.torsion_function_denominator R K G hG N hN q c hc f hmem`. Use `⟨k, c.r ^ k • f, hk, fun ψ => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, hf, Algebra.smul_def, map_pow]`.

Rewrite using `[Pi.smul_apply, hf0 x hx, smul_zero]`.
-/
theorem exists_extend_zero_mem_ord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ (s₀ : Tors G N K) (u : c.C), ∃ (k : ℕ) (g : Tors G N K → K), g ∈ ord G N K ∧ (∀ ψ : c.C →ₐ[R] K, g (s₀ * torsMap ψ c.j) = algebraMap R K c.r ^ k * ψ u) ∧ ∀ x, (∀ ψ : c.C →ₐ[R] K, x ≠ s₀ * torsMap ψ c.j) → g x = 0 := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN q c hc s₀ u
  classical
  have hinj : ∀ ψ ψ' : c.C →ₐ[R] K, torsMap ψ c.j = torsMap ψ' c.j → ψ = ψ' := fun ψ ψ' h =>
    (c.bij K).injOn (Set.mem_univ _) (Set.mem_univ _) h
  have hpowval : ∀ (x : Tors G N K) (n : ℕ), (x ^ n).1 = x.1 ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero, pow_zero, tors_one_val]
    | succ n ih => rw [pow_succ, pow_succ, tors_mul_val, ih]
  have hkill : ∀ x : Tors G N K, x ^ N = 1 := fun x => Subtype.ext (by rw [hpowval, x.2, tors_one_val])
  have hpow : ∀ (ψ : c.C →ₐ[R] K) (n : ℕ), ∃ ψ' : c.C →ₐ[R] K, torsMap ψ' c.j = torsMap ψ c.j ^ (n + 1) := by
    intro ψ n
    induction n with
    | zero => exact ⟨ψ, by rw [zero_add, pow_one]⟩
    | succ n ih =>
      obtain ⟨ψ', h⟩ := ih
      obtain ⟨ψ'', h'⟩ := hc.2 K ψ' ψ
      exact ⟨ψ'', by rw [h', h, ← pow_succ]⟩
  have hinv : ∀ ψ : c.C →ₐ[R] K, ∃ ψ' : c.C →ₐ[R] K, torsMap ψ' c.j = (torsMap ψ c.j)⁻¹ := by
    intro ψ
    obtain ⟨ψ', h⟩ := hpow ψ (2 * N - 2)
    refine ⟨ψ', ?_⟩
    rw [h]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show 2 * N - 2 + 1 + 1 = N * 2 by omega, pow_mul, hkill, one_pow]
  let f : Tors G N K → K := fun x =>
    if h : ∃ ψ : c.C →ₐ[R] K, x = s₀ * torsMap ψ c.j then h.choose u else 0
  have hf : ∀ ψ : c.C →ₐ[R] K, f (s₀ * torsMap ψ c.j) = ψ u := by
    intro ψ
    have h : ∃ ψ' : c.C →ₐ[R] K, s₀ * torsMap ψ c.j = s₀ * torsMap ψ' c.j := ⟨ψ, rfl⟩
    have e : ψ = h.choose := hinj _ _ (mul_left_cancel h.choose_spec)
    show (if h : ∃ ψ' : c.C →ₐ[R] K, s₀ * torsMap ψ c.j = s₀ * torsMap ψ' c.j then h.choose u else 0) = _
    rw [dif_pos h, ← e]
  have hf0 : ∀ x, (∀ ψ : c.C →ₐ[R] K, x ≠ s₀ * torsMap ψ c.j) → f x = 0 := by
    intro x hx
    exact dif_neg (fun ⟨ψ, h⟩ => hx ψ h)
  have hmem : ∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j) := by
    intro s
    by_cases h : ∃ ψ₁ ψ₂ : c.C →ₐ[R] K, s * torsMap ψ₁ c.j = s₀ * torsMap ψ₂ c.j
    · obtain ⟨ψ₁, ψ₂, h⟩ := h
      obtain ⟨ψ₃, h₃⟩ := hinv ψ₁
      obtain ⟨ψ₀, h₀⟩ := hc.2 K ψ₂ ψ₃
      have hs : s = s₀ * torsMap ψ₀ c.j := by
        rw [h₀, h₃, ← _root_.mul_assoc, ← h, mul_inv_cancel_right]
      obtain ⟨T, hT⟩ := GlobalTheory.T.prechart_translation_map R K G N q c hc ψ₀
      refine ⟨T u, fun ψ => ?_⟩
      rw [hs, _root_.mul_assoc, ← hT, hf]
      rfl
    · refine ⟨0, fun ψ => ?_⟩
      rw [map_zero, hf0 _ (fun ψ' h' => h ⟨ψ, ψ', h'⟩)]
  obtain ⟨k, hk⟩ := GlobalTheory.T.torsion_function_denominator R K G hG N hN q c hc f hmem
  refine ⟨k, c.r ^ k • f, hk, fun ψ => ?_, fun x hx => ?_⟩
  · rw [Pi.smul_apply, hf, Algebra.smul_def, map_pow]
  · rw [Pi.smul_apply, hf0 x hx, smul_zero]

end GlobalTheory.GroupBplus.Aff
