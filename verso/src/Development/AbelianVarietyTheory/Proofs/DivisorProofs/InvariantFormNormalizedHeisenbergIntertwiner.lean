import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
/- English proof (translation)
Establish `hAA` using `_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A) (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)`. Establish `hcomp` using `_root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx (by rw [hAA.2]; simp) e he`. Take `⟨hsym, hback⟩` from `_root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx`. Establish `hlin : ∀ (c : ℂ) (v : M), _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v`. Introduce `c v`.

Unfold `_root_.GlobalTheory.FinWeil.sumOp`. Simplify using `only [map_smul]`. Rewrite using `[smul_finsum]`. Unfold `_root_.GlobalTheory.FinWeil.normOp at hcomp`. Rewrite `hcomp` using `[hAA.1, hAA.2, hsym, hlin, hback e he]`.

Simplify using `only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique, Finset.sum_singleton, hW.zero, smul_smul] at hcomp`. Establish `hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0` using `hlam.1 _ hidx`. Establish `hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0`. Rewrite using `[sub_smul, one_smul, mul_assoc, hcomp, sub_self]`. Establish `h1` using `(smul_eq_zero.1 hz).resolve_right he0`.

Clear denominators, using `at h1` for the nonvanishing conditions. Take the linear combination `-h1`.
-/
private lemma lam_idx_sq_eq_idx_of_fixed_ne_zero (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (lam : ℕ →* ℂ) (hlam : _root_.GlobalTheory.FinWeil.GoodNorm σ lam) {A A' : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (hA' : _root_.GlobalTheory.FinWeil.SelfDual γ A')
    (hidx : _root_.GlobalTheory.FinWeil.idx A A' ≠ 0) {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he0 : e ≠ 0) :
    lam (_root_.GlobalTheory.FinWeil.idx A A') ^ 2 = _root_.GlobalTheory.FinWeil.idx A A' := by
  have hAA := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A)
    (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)
  have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx
    (by rw [hAA.2]; simp) e he
  obtain ⟨hsym, hback⟩ := _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx
  have hlin : ∀ (c : ℂ) (v : M),
      _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v := by
    intro c v
    unfold _root_.GlobalTheory.FinWeil.sumOp
    simp only [map_smul]
    rw [smul_finsum]
  unfold _root_.GlobalTheory.FinWeil.normOp at hcomp
  rw [hAA.1, hAA.2, hsym, hlin, hback e he] at hcomp
  simp only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton, hW.zero, smul_smul] at hcomp
  have hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0 := hlam.1 _ hidx
  have hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ *
      (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_assoc, hcomp, sub_self]
  have h1 := (smul_eq_zero.1 hz).resolve_right he0
  field_simp at h1
  linear_combination -h1

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
/- English proof (translation)
Establish `hn : ‖c‖ ^ 2 = n` using `by rw [← norm_pow, h, Complex.norm_natCast]`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private lemma mul_conj_eq_natCast_of_sq_eq (c : ℂ) (n : ℕ) (h : c ^ 2 = n) :
    c * starRingEnd ℂ c = n := by
  have hn : ‖c‖ ^ 2 = n := by rw [← norm_pow, h, Complex.norm_natCast]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  push_cast
  rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hz ((hA z).2 h)`. Establish `haz : γ a z ≠ 1` using `fun h => hza (hW.swap_eq_one h)`.

Establish `key` using `hB a (W z e) e'`. Rewrite `key` using `[hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Establish `: (γ a z - 1) * B (W z e) e' = 0` using `by rw [sub_mul, key, one_mul, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)`.
-/
private lemma invariantForm_translate_vacuum_eq_zero
    (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x u v, B (W x u) (W x v) = B u v) {e e' : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he' : _root_.GlobalTheory.FinWeil.Fixes W A e') {z : X} (hz : z ∉ A) : B (W z e) e' = 0 := by
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hz ((hA z).2 h)
  have haz : γ a z ≠ 1 := fun h => hza (hW.swap_eq_one h)
  have key := hB a (W z e) e'
  rw [hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  have : (γ a z - 1) * B (W z e) e' = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
/- English proof (translation)
Rewrite using `[← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma invariantForm_translate_pair_eq (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hB : ∀ x u v, B (W x u) (W x v) = B u v) (x y : X) (e e' : M) :
    B (W x e) (W y e') = γ (w • -y) x * (starRingEnd ℂ) (γ (w • -y) y) * B (W (-y + x) e) e' := by
  rw [← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]
  simp
  ring

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
/- English proof (translation)
Establish `htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' → B₁ (W z e) e' = B₂ (W z e) e'`. Introduce `z e e' he he'`. Distinguish the cases in `hz : z ∈ A`. Rewrite using `[he z hz]`. Conclude with `hvac e e' he he'`.

Rewrite using `[invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz, invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]`. Establish `hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t`. Introduce and unpack `s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩`. Rewrite using `[invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂, htr _ e e' he he']`. Establish `hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s` using `fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)`.

Establish `hflip : B₁.flip v = B₂.flip v` using `LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])`. Simplify using `using LinearMap.congr_fun hflip u`.
-/
private lemma invariantForms_eq_of_eq_on_vacua (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤)
    (B₁ B₂ : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (h₁ : ∀ x u v, B₁ (W x u) (W x v) = B₁ u v)
    (h₂ : ∀ x u v, B₂ (W x u) (W x v) = B₂ u v)
    (hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ e e' = B₂ e e')
    (u v : M) : B₁ u v = B₂ u v := by
  have htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ (W z e) e' = B₂ (W z e) e' := by
    intro z e e' he he'
    by_cases hz : z ∈ A
    · rw [he z hz]
      exact hvac e e' he he'
    · rw [invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz,
        invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]
  have hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e},
      ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t := by
    rintro s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩
    rw [invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂,
      htr _ e e' he he']
  have hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s :=
    fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)
  have hflip : B₁.flip v = B₂.flip v :=
    LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])
  simpa using LinearMap.congr_fun hflip u

open Classical in
open scoped BigOperators in

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v`. Take `⟨n, f, hfB, hfu⟩` from `_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx`. Establish `hsum` using `fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) => _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu`. Establish `hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' → B (T e) (T e') = B e e'`. Introduce `e e' he he'`.

Distinguish the cases in `he0 : e = 0`. Substitute `he0` using the available equality. Simplify using the standard rewrite rules. Establish `hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n` using `by simpa using (hsum e he).2`. Establish `hc2` using `lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0`.

Rewrite `hc2` using `[hn]`. Establish `hcn` using `mul_conj_eq_natCast_of_sq_eq _ _ hc2`. Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (hn ▸ hidx)`. Establish `hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e`. Introduce `e he`.

Rewrite using `[hTe e he]`. Unfold `_root_.GlobalTheory.FinWeil.normOp`. Rewrite using `[hn, (hsum e he).1]`. Establish `hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0`. Introduce `i j`.

Rewrite using `[← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel, hW.zero]`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Rewrite using `[neg_add_cancel, hW.zero]`. Apply `invariantForm_translate_vacuum_eq_zero hW hA B hB he he'` to reduce the goal to its premises.

Introduce `hmem`. Apply `hij` to reduce the goal to its premises. Take `⟨k, -, hk⟩` from `hfu (f i) (hfB i)`. Rewrite using `[hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]`. Rewrite using `[hT' e he, hT' e' he']`.

Simplify using `only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply, smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]`. Establish `hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1`. Rewrite using `[← mul_inv, hcn, inv_mul_cancel₀ hn0]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Take the linear combination `B e e' * hinv`.

Establish `key` using `invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v`. Simplify using `using key`.
-/
theorem _root_.GlobalTheory.FinWeil.invForm_intertwiner : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam →
    ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → _root_.GlobalTheory.FinWeil.SelfDual γ (A.map φ) →
    _root_.GlobalTheory.FinWeil.idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) →
    (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map φ) e) →
    ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) →
    ∀ u v, B (T u) (T v) = B u v := by
  intro R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v
  obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx
  have hsum := fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu
  have hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B (T e) (T e') = B e e' := by
    intro e e' he he'
    by_cases he0 : e = 0
    · subst he0
      simp
    have hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n := by simpa using (hsum e he).2
    have hc2 := lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0
    rw [hn] at hc2
    have hcn := mul_conj_eq_natCast_of_sq_eq _ _ hc2
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hn ▸ hidx)
    have hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e := by
      intro e he
      rw [hTe e he]
      unfold _root_.GlobalTheory.FinWeil.normOp
      rw [hn, (hsum e he).1]
    have hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0 := by
      intro i j
      rw [← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i),
        hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel,
        hW.zero]
      split_ifs with hij
      · subst hij
        rw [neg_add_cancel, hW.zero]
      · apply invariantForm_translate_vacuum_eq_zero hW hA B hB he he'
        intro hmem
        apply hij
        obtain ⟨k, -, hk⟩ := hfu (f i) (hfB i)
        rw [hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]
    rw [hT' e he, hT' e' he']
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply,
      smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]
    have hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1 := by
      rw [← mul_inv, hcn, inv_mul_cancel₀ hn0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination B e e' * hinv
  have key := invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B
    (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v
  simpa using key

end GlobalTheory.FinWeil
