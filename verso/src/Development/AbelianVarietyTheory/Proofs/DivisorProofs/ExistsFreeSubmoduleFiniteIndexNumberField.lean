import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X`. Use `set r := Module.finrank (𝓞 E) X`. Take `⟨e, he⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)`. Set `f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X` to `Fintype.linearCombination (𝓞 E) e`. Establish `hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i` using `fun c => by`.

Simplify using `[f, Fintype.linearCombination_apply]`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Rewrite `hc` using `[hfv']`.

Conclude with `funext ((Fintype.linearIndependent_iff.mp he) c hc)`. Establish `key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f`. Introduce `x`. Establish `hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X)`. Introduce `h`.

Use `h.fintype_card_le_finrank` as an intermediate fact. Simplify using `[r] at this`. Rewrite `hdep` using `[Fintype.not_linearIndependent_iff]`. Take `⟨g, hg, i, hi⟩` from `hdep`. Rewrite `hg` using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hg`. Establish `ha : g 0 ≠ 0`. Introduce `h0`. Rewrite `hg` using `[h0, zero_smul, zero_add]`. Establish `hz` using `(Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg`.

Use `hi ?_` and prove the remaining obligations. Use `Fin.cases h0 (fun j => hz j) i` and prove the remaining obligations. Establish `hax : g 0 • x ∈ LinearMap.range f`. Use `⟨fun j => - g j.succ, ?_⟩` and prove the remaining obligations. Rewrite using `[hfv']`.

Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Conclude with `(neg_eq_of_add_eq_zero_left hg)`. Establish `hI : Ideal.span {g 0} ≠ ⊥` using `by simpa using ha`. Establish `hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]` and apply the resulting hypothesis.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))`. Use `⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hax`. Use `choose N hNpos hNmem using key`.

Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := ℤ) (M := X)`. Use `⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩` and prove the remaining obligations. Establish `hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f`. Introduce `s hs`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem N hs`.

Rewrite using `[hk, mul_comm, mul_smul]`. Conclude with `AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ (S : Set X)` using `by rw [hS]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact hgen y hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy`.

Rewrite using `[smul_comm]`. Conclude with `zsmul_mem hy a`.
-/
theorem latt_free_sub_full_rank {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧
      Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  classical
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)
  let f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) e
  have hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i := fun c => by
    simp [f, Fintype.linearCombination_apply]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hfv'] at hc
    exact funext ((Fintype.linearIndependent_iff.mp he) c hc)

  have key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f := by
    intro x
    have hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X) := by
      intro h
      have := h.fintype_card_le_finrank
      simp [r] at this
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have ha : g 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hg
      have hz := (Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg
      refine hi ?_
      refine Fin.cases h0 (fun j => hz j) i
    have hax : g 0 • x ∈ LinearMap.range f := by
      refine ⟨fun j => - g j.succ, ?_⟩
      rw [hfv']
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact (neg_eq_of_add_eq_zero_left hg)
    have hI : Ideal.span {g 0} ≠ ⊥ := by simpa using ha
    have hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))
    refine ⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
    exact Submodule.smul_mem _ _ hax
  choose N hNpos hNmem using key
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩
  have hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f := by
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem N hs
    rw [hk, mul_comm, mul_smul]
    exact AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k
  intro x
  have hx : x ∈ Submodule.span ℤ (S : Set X) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact zsmul_mem hy a

end GlobalTheory
