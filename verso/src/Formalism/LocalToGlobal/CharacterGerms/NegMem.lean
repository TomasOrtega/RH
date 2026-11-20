import Formalism.LocalToGlobal.CharacterGerms.ValNonnegLeadingCoeffOfMemTySet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [tyS, PowerSeries.coeff_mk, map_add, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tyS_add {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) : tyS l (fun s => a s + b s) = tyS l a + tyS l b := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AddCvSt (V : VF C) : Prop :=
  ∀ γ γ' : κ → PowerSeries C, IsCv V γ → IsCv V γ' →
    ∃ γ'' : κ → PowerSeries C, IsCv V γ'' ∧
      (∀ i, alongCv γ'' (X.lg i) = alongCv γ (X.lg i) + alongCv γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        PowerSeries.constantCoeff (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)) = 0 ∧
        ∀ n, V.Ge 0 (PowerSeries.coeff n (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)))

/- English proof (translation)
Unfold `VF.Ge at *`. Conclude with `le_trans (le_min ha hb) (V.v.map_add a b)`.
-/
private theorem ge_add_lemma (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.Ge 0 (a + b) := by
  unfold VF.Ge at *
  exact le_trans (le_min ha hb) (V.v.map_add a b)

/- English proof (translation)
Establish `hl2` using `V.l_prime.two_le`. Take `⟨γ, lam, hγ, hlam, h1, h2⟩` from `hx`. Take `⟨γ', lam', hγ', hlam', h1', h2'⟩` from `hy`. Take `⟨γ'', hγ'', hL, hS⟩` from `hA γ γ' hγ hγ'`. Establish `hty : ∀ n, tyS V.l (fun s => (x + y) s n) = tyS V.l (fun s => x s n) + tyS V.l (fun s => y s n)` using `fun n => tyS_add hl2 _ _`.

Use `⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) - alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨c0, cI⟩` from `hS (X.u (1 - g) q) (hu (1 - g) q)`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, (hlam q).1, (hlam' q).1, c0]`.

Simplify using the standard rewrite rules. Rewrite using `[map_add, map_add]`. Conclude with `(((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)`. Introduce `i`. Rewrite using `[hL i, h1 i, h1' i, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hty, smul_add]`. Introduce `q`. Establish `hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (x + y) s (Sum.inl c)) else 0) = (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) + (if X.ty g c = X.ty (1 - g) q …`. Introduce `c`.

Rewrite using `[hty]`. Use `split_ifs`. Rewrite using `[smul_add]`. Rewrite using `[add_zero]`. Simplify using `only [hs]`.

Rewrite using `[Finset.sum_add_distrib, hty, h2 q, h2' q]`. Normalize the expressions using the abelian group laws.
-/
theorem add_mem (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    (x y : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (hy : y ∈ X.TySet V g) : x + y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, tyS V.l (fun s => (x + y) s n) = tyS V.l (fun s => x s n) + tyS V.l (fun s => y s n) :=
    fun n => tyS_add hl2 _ _
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add, map_add, (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add, map_add]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (x + y) s (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => y s (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem powerSeries_rescale_smul (a c : C) (f : PowerSeries C) :
    PowerSeries.rescale a (c • f) = c • PowerSeries.rescale a f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `only [PowerSeries.rescale_eq_subst]`. Conclude with `alongCv_repar hγ (by simp) f`.
-/
private theorem alongCv_rescale_eq_rescale_alongCv {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (a : C) (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.rescale a (γ i)) f = PowerSeries.rescale a (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[← h, (hl.pow).neg_one_pow]`.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tyS_neg_eq_rescale_neg_one_of_odd {l : ℕ} (hl : Odd l) (a : ℕ → C) :
    tyS l (fun s => -a s) = PowerSeries.rescale (-1) (tyS l a) := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [← h, (hl.pow).neg_one_pow]
    ring
  · ring

/- English proof (translation)
Introduce `i`. Use `show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧ ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(h i).1`.

Establish `h2` using `(h i).2 n`. Rewrite using `[PowerSeries.coeff_rescale]`. Break down `neg_one_pow_eq_or C n with e | e` into its components or cases. Rewrite using `[e, one_mul]`. Conclude with `h2`.

Rewrite using `[e, neg_one_mul]`. Unfold `VF.Ge at h2 ⊢`. Rewrite using `[V.v.map_neg]`. Conclude with `h2`.
-/
private theorem isCv_rescale_neg_one (V : VF C) {σ : Type} {γ : σ → PowerSeries C} (h : IsCv V γ) :
    IsCv V (fun i => PowerSeries.rescale (-1 : C) (γ i)) := by
  intro i
  show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧
    ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (h i).1
  · have h2 := (h i).2 n
    rw [PowerSeries.coeff_rescale]
    rcases neg_one_pow_eq_or C n with e | e
    · rw [e, one_mul]
      exact h2
    · rw [e, neg_one_mul]
      unfold VF.Ge at h2 ⊢
      rw [V.v.map_neg]
      exact h2

/- English proof (translation)
Establish `hl : Odd V.l` using `V.l_prime.odd_of_ne_two hodd`. Unfold `RawChart.TySet at hx ⊢`. Take `⟨γ, lam, hγ, hlam, hlg, hq⟩` from `hx`. Establish `hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0` using `fun i => (hγ i).1`. Rewrite using `[Set.mem_setOf_eq]`.

Use `⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q), isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Simplify using `only [Pi.neg_apply]`. Rewrite using `[alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]`. Introduce `q`. Simplify using `only [Pi.neg_apply]`. Rewrite using `[tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]`. Simplify using `only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add, map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero, powerSeries_rescale_smul]`.
-/
theorem neg_mem (V : VF C) (g : Fin 2) (hodd : V.l ≠ 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    -x ∈ X.TySet V g := by
  have hl : Odd V.l := V.l_prime.odd_of_ne_two hodd
  unfold RawChart.TySet at hx ⊢
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  rw [Set.mem_setOf_eq]
  refine ⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q),
    isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]
    rw [alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]
  · intro q
    simp only [Pi.neg_apply]
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]
    simp only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add, map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero,
      powerSeries_rescale_smul]

/- English proof (translation)
Use `revert hf`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.sum_empty]`. Conclude with `h0`.

Introduce `a s ha ih hf`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem sum_mem (V : VF C) (g : Fin 2) (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g) {ι : Type} (s : Finset ι)
    (f : ι → ℕ → I g ⊕ JJ I g → C) (hf : ∀ i ∈ s, f i ∈ X.TySet V g) : ∑ i ∈ s, f i ∈ X.TySet V g := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact h0
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end RawChart

end Formalism.L2.FormalSeriesBounds
