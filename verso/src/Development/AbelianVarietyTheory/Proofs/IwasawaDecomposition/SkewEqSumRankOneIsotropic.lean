import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroHermOfSkewStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

/- English proof (translation)
Introduce `r`. Proceed by induction on `r using Nat.strong_induction_on with`. Consider the case `_ r ih`. Introduce `W hr hW n hn hnW`. Distinguish the cases in `h0 : n = 0`.

Conclude with `⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp [h0]⟩`. Take `⟨x, hx⟩` from `GlobalTheory.T.exists_nonzero_herm_of_skew E N G κ hG hdet hκ hκ0 n hn h0`. Take `⟨ξ, hξ⟩ : ∃ ξ, ξ = n.mulVec x` from `⟨_, rfl⟩`. Take `⟨β, hβ⟩ : ∃ β, β = herm G ξ x` from `⟨_, rfl⟩`. Establish `hβ0 : β ≠ 0` using `by rw [hβ, hξ]; exact hx`.

Establish `hβcc : cc β = -β`. Rewrite using `[hβ, cc_herm G hG, hξ]`. Use `hn x x` as an intermediate fact. Take the linear combination `this`. Take `⟨c, hc⟩ : ∃ c : E, c = -β⁻¹` from `⟨_, rfl⟩`.

Take `⟨t0, ht0⟩ : ∃ t0 : E, t0 = -(κ * β)⁻¹` from `⟨_, rfl⟩`. Establish `hct : c = t0 * κ` using `by rw [hc, ht0]; field_simp`. Establish `ht0cc : cc t0 = t0` using `by rw [ht0, cc_neg, cc_inv, cc_mul, hκ, hβcc, neg_mul_neg]`. Establish `hcc : cc c = -c` using `by rw [hc, cc_neg, cc_inv, hβcc, inv_neg]`. Establish `hcβ : c * β = -1` using `by rw [hc]; field_simp`.

Take `⟨n1, hn1⟩ : ∃ n1, n1 = n - c • rk1 G ξ ξ` from `⟨_, rfl⟩`. Establish `h1 : ∀ y, n1.mulVec y = n.mulVec y - (c * herm G y ξ) • ξ`. Introduce `y`. Rewrite using `[hn1, Matrix.sub_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]`. Establish `hsk : IsSkew G n1`.

Introduce `y z`. Rewrite using `[h1 y, h1 z, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hn y z, cc_mul, hcc, cc_herm G hG]`. Expand and normalize the polynomial expressions, which then agree. Set `f : (Fin N → E) →ₗ[E] E` to `{ toFun := fun v => herm G v x map_add' := fun a b => herm_add_left G a b x map_smul' := fun a v => by simp only [herm_smul_left, RingHom.id_apply, smul_eq_mul] }`. Set `W' : Submodule E (Fin N → E)` to `W ⊓ LinearMap.ker f`.

Establish `hξW : ξ ∈ W` using `hξ ▸ hnW x`. Establish `hn1W : ∀ y, n1.mulVec y ∈ W'`. Introduce `y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `W.sub_mem (hnW y) (W.smul_mem _ hξW)`. Use `show herm G (n1.mulVec y) x = 0`. Rewrite using `[h1, herm_sub_left, herm_smul_left, ← hβ]`. Use `hn y x` as an intermediate fact. Rewrite `this` using `[← hξ]`.

Take the linear combination `this - herm G y ξ * hcβ`. Establish `hlt : W' < W`. Use `SetLike.lt_iff_le_and_exists.2 ⟨inf_le_left, ξ, hξW, fun h => hβ0 ?_⟩` and prove the remaining obligations. Establish `: herm G ξ x = 0` using `h.2`. Rewrite using `[hβ, this]`.

Establish `hrk : Module.finrank E W' < r` using `hr ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨d, ξ', t', hmem, hreal, heq⟩` from `ih _ hrk W' rfl (fun u hu v hv => hW u hu.1 v hv.1) n1 hsk hn1W`. Use `⟨d + 1, Fin.cons ξ ξ', Fin.cons t0 t', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations.

Simplify using `using hξW`. Simplify using `using (hmem j).1`. Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `using ht0cc`.

Simplify using `using hreal j`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← heq, ← hct, hn1]`. Normalize the expressions using the abelian group laws.
-/
theorem skew_eq_sum_rk1_of_finrank (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E) (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0)
    (hκ : cc κ = -κ) (hκ0 : κ ≠ 0) :
    ∀ r, ∀ (W : Submodule E (Fin N → E)), Module.finrank E W = r →
      (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n →
      (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E),
        (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro W hr hW n hn hnW
  by_cases h0 : n = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp [h0]⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_nonzero_herm_of_skew E N G κ hG hdet hκ hκ0 n hn h0
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = n.mulVec x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = herm G ξ x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := by rw [hβ, hξ]; exact hx
  have hβcc : cc β = -β := by
    rw [hβ, cc_herm G hG, hξ]
    have := hn x x
    linear_combination this
  obtain ⟨c, hc⟩ : ∃ c : E, c = -β⁻¹ := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : E, t0 = -(κ * β)⁻¹ := ⟨_, rfl⟩
  have hct : c = t0 * κ := by rw [hc, ht0]; field_simp
  have ht0cc : cc t0 = t0 := by rw [ht0, cc_neg, cc_inv, cc_mul, hκ, hβcc, neg_mul_neg]
  have hcc : cc c = -c := by rw [hc, cc_neg, cc_inv, hβcc, inv_neg]
  have hcβ : c * β = -1 := by rw [hc]; field_simp
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = n - c • rk1 G ξ ξ := ⟨_, rfl⟩
  have h1 : ∀ y, n1.mulVec y = n.mulVec y - (c * herm G y ξ) • ξ := by
    intro y
    rw [hn1, Matrix.sub_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]
  have hsk : IsSkew G n1 := by
    intro y z
    rw [h1 y, h1 z, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hn y z, cc_mul,
      hcc, cc_herm G hG]
    ring
  let f : (Fin N → E) →ₗ[E] E :=
    { toFun := fun v => herm G v x
      map_add' := fun a b => herm_add_left G a b x
      map_smul' := fun a v => by simp only [herm_smul_left, RingHom.id_apply, smul_eq_mul] }
  let W' : Submodule E (Fin N → E) := W ⊓ LinearMap.ker f
  have hξW : ξ ∈ W := hξ ▸ hnW x
  have hn1W : ∀ y, n1.mulVec y ∈ W' := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [h1]; exact W.sub_mem (hnW y) (W.smul_mem _ hξW)
    · show herm G (n1.mulVec y) x = 0
      rw [h1, herm_sub_left, herm_smul_left, ← hβ]
      have := hn y x
      rw [← hξ] at this
      linear_combination this - herm G y ξ * hcβ
  have hlt : W' < W := by
    refine SetLike.lt_iff_le_and_exists.2 ⟨inf_le_left, ξ, hξW, fun h => hβ0 ?_⟩
    have : herm G ξ x = 0 := h.2
    rw [hβ, this]
  have hrk : Module.finrank E W' < r := hr ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨d, ξ', t', hmem, hreal, heq⟩ := ih _ hrk W' rfl
    (fun u hu v hv => hW u hu.1 v hv.1) n1 hsk hn1W
  refine ⟨d + 1, Fin.cons ξ ξ', Fin.cons t0 t', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hξW
    · simpa using (hmem j).1
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using ht0cc
    · simpa using hreal j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← heq, ← hct, hn1]
    abel

/- English proof (translation)
Introduce `E _ _ _ N G κ hG hdet hκ hκ0 W hW n hn hnW`. Conclude with `skew_eq_sum_rk1_of_finrank E N G κ hG hdet hκ hκ0 _ W rfl hW n hn hnW`.
-/
theorem skew_eq_sum_rk1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) →
    ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) →
    ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧
      n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro E _ _ _ N G κ hG hdet hκ hκ0 W hW n hn hnW
  exact skew_eq_sum_rk1_of_finrank E N G κ hG hdet hκ hκ0 _ W rfl hW n hn hnW

end GlobalTheory.UnipKill
