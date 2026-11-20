import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop

open Formalism.BasicNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.GoodIdemReal

open GlobalTheory.SeriesSupportTest

/- English proof (translation)
Introduce `D hS γ`. Establish `: ∀ k, Fact (D.host.g k).Prime` using `fun k => ⟨D.host.g_prime k⟩`. Establish `: ∀ k, NeZero (D.host.g k)` using `fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Set `ψ : ∀ k : Fin 2, (Fin D.R.r → ZMod (D.host.g k)) → (Fin D.R.r → ZMod (D.host.g k))` to `fun k a => if (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 then fun i => (dl (Formalism.CyclotomicNorms.monicOf a)).coeff i else a`. Establish `hlab : ∀ k (a : Fin D.R.r → ZMod (D.host.g k)), (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = D.R.r ∧ (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0` using `fun k a ha => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf a, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf a, ha⟩`.

Establish `hψm : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → Formalism.CyclotomicNorms.monicOf (ψ k a) = dl (Formalism.CyclotomicNorms.monicOf a)`. Introduce `k a ha`. Establish `hd` using `dl_lab (hlab k a ha)`. Simplify using `only [ψ, if_pos ha]`. Conclude with `Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ hd.1 hd.2.1`.

Establish `hψ0 : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0 → ψ k a = a`. Introduce `k a ha`. Simplify using `only [ψ, ha, ne_eq, not_true_eq_false, if_false]`. Establish `hψc : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf (ψ k a)).coeff 0 ≠ 0`. Introduce `k a ha`.

Rewrite using `[hψm k a ha, (dl_lab (hlab k a ha)).2.2]`. Conclude with `inv_ne_zero ha`. Establish `hψinv : ∀ k, Function.Involutive (ψ k)`. Introduce `k a`. Distinguish the cases in `ha : (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0`.

Rewrite using `[hψ0 k a ha, hψ0 k a ha]`. Use function extensionality and compare the values at `i`. Rewrite using `[← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (ψ k (ψ k a)) i, hψm k _ (hψc k a ha), hψm k a ha, dl_dl (hlab k a ha), Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]`. Set `Φ : Equiv.Perm (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1))` to `Function.Involutive.toPerm (fun a kv => ψ kv.1 (a kv)) (fun a => funext fun kv => hψinv kv.1 (a kv))`. Establish `hΦ : ∀ a kv, Φ a kv = ψ kv.1 (a kv)` using `fun _ _ => rfl`.

Set `good : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → Prop` to `fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))`. Set `T : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ` to `fun a => if good a then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0`. Establish `he : D.ntypes.e0.coeff γ = ∑ᶠ a, T a` using `rfl`. Establish `hgood : ∀ a, (∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0) → good a → good (Φ a)`. Introduce `a ha h`.

Simplify using `only [good] at h ⊢`. Unfold `NTypes.goodTuple at h ⊢`. Introduce `k`. Establish `hf : (fun v => Formalism.CyclotomicNorms.monicOf (Φ a ⟨k, v⟩)) = fun v => dl (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))`. Use function extensionality and compare the values at `fun v => hψm k _ (ha ⟨k, v⟩)`.

Establish `h1` using `good_dl _ _ (h k).1`. Establish `h2` using `good_dl _ _ (h k).2`. Simplify using `only [inv_inv] at h1 h2`. Simplify using `only [hf]`. Conclude with `⟨h2, h1⟩`.

Establish `hzero : ∀ a, ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 = 0 → T a = 0`. Introduce `a kv h0`. Simplify using `only [T]`. Use `split_ifs`. Use `Finset.prod_eq_zero (Finset.mem_univ kv) ?_` and prove the remaining obligations.

Rewrite using `[D.ntypes.eSer_zero _ _ (fun h => h.2.2 h0)]`. Use `first`. Consider the case `rfl`. Consider the case `simp`. Both sides reduce to the same expression.

Establish `key : ∀ a, star (T a) = T (Φ a)`. Introduce `a`. Distinguish the cases in `hz : ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0`. Establish `hz' : ∀ kv, (Formalism.CyclotomicNorms.monicOf (Φ a kv)).coeff 0 ≠ 0` using `fun kv => hψc _ _ (hz kv)`. Establish `hiff : good (Φ a) ↔ good a`.

Use `⟨fun h => ?_, hgood a hz⟩` and prove the remaining obligations. Use `hgood (Φ a) hz' h` as an intermediate fact. Establish `e : Φ (Φ a) = a` using `funext fun kv => hψinv kv.1 (a kv)`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Simplify using `only [T, hiff]`.

Use `split_ifs`. Rewrite using `[star_prod]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[hS kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) (Formalism.CyclotomicNorms.Sqf.monic_monicOf _) (hz kv), hΦ, hψm _ _ (hz kv)]`. Both sides reduce to the same expression.

Conclude with `star_zero _`. Use `push_neg at hz`. Take `⟨kv, h0⟩` from `hz`. Rewrite using `[hzero a kv h0, hzero (Φ a) kv (by rw [hΦ, hψ0 _ _ h0]; exact h0), star_zero]`. Establish `hfin : (Function.support T).Finite` using `Set.toFinite _`.

Establish `hstar : star (∑ᶠ a, T a) = ∑ᶠ a, star (T a)`. Use `map_finsum (starAddEquiv (R := ℂ)) hfin` as an intermediate fact. Simplify `this` using `only [starAddEquiv_apply]`. Rewrite using `[he, hstar]`. Repeatedly rewrite using `[key]`.

Conclude with `finsum_comp_equiv Φ`.
-/
theorem star_coeff_of_reverse : ∀ D : D7, (∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), f.Monic → f.coeff 0 ≠ 0 →
      ∀ x, star ((D.ntypes.eSer k f).coeff x) = (D.ntypes.eSer k (C (f.coeff 0)⁻¹ * f.reverse)).coeff x) →
    (∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ) := by
  intro D hS γ
  classical
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩

  let ψ : ∀ k : Fin 2, (Fin D.R.r → ZMod (D.host.g k)) → (Fin D.R.r → ZMod (D.host.g k)) :=
    fun k a => if (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 then fun i => (dl (Formalism.CyclotomicNorms.monicOf a)).coeff i else a
  have hlab : ∀ k (a : Fin D.R.r → ZMod (D.host.g k)), (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 →
      (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = D.R.r ∧ (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 :=
    fun k a ha => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf a, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf a, ha⟩
  have hψm : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → Formalism.CyclotomicNorms.monicOf (ψ k a) = dl (Formalism.CyclotomicNorms.monicOf a) := by
    intro k a ha
    have hd := dl_lab (hlab k a ha)
    simp only [ψ, if_pos ha]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ hd.1 hd.2.1
  have hψ0 : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0 → ψ k a = a := by
    intro k a ha
    simp only [ψ, ha, ne_eq, not_true_eq_false, if_false]
  have hψc : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf (ψ k a)).coeff 0 ≠ 0 := by
    intro k a ha
    rw [hψm k a ha, (dl_lab (hlab k a ha)).2.2]
    exact inv_ne_zero ha
  have hψinv : ∀ k, Function.Involutive (ψ k) := by
    intro k a
    by_cases ha : (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0
    · rw [hψ0 k a ha, hψ0 k a ha]
    · funext i
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (ψ k (ψ k a)) i, hψm k _ (hψc k a ha), hψm k a ha,
        dl_dl (hlab k a ha), Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

  let Φ : Equiv.Perm (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) :=
    Function.Involutive.toPerm (fun a kv => ψ kv.1 (a kv)) (fun a => funext fun kv => hψinv kv.1 (a kv))
  have hΦ : ∀ a kv, Φ a kv = ψ kv.1 (a kv) := fun _ _ => rfl
  let good : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → Prop :=
    fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
  let T : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun a =>
    if good a then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)
    else 0
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a, T a := rfl

  have hgood : ∀ a, (∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0) → good a → good (Φ a) := by
    intro a ha h
    simp only [good] at h ⊢
    unfold NTypes.goodTuple at h ⊢
    intro k
    have hf : (fun v => Formalism.CyclotomicNorms.monicOf (Φ a ⟨k, v⟩)) = fun v => dl (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) :=
      funext fun v => hψm k _ (ha ⟨k, v⟩)
    have h1 := good_dl _ _ (h k).1
    have h2 := good_dl _ _ (h k).2
    simp only [inv_inv] at h1 h2
    simp only [hf]
    exact ⟨h2, h1⟩

  have hzero : ∀ a, ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 = 0 → T a = 0 := by
    intro a kv h0
    simp only [T]
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ kv) ?_
      rw [D.ntypes.eSer_zero _ _ (fun h => h.2.2 h0)]
      first
        | rfl
        | simp
    · rfl
  have key : ∀ a, star (T a) = T (Φ a) := by
    intro a
    by_cases hz : ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0
    · have hz' : ∀ kv, (Formalism.CyclotomicNorms.monicOf (Φ a kv)).coeff 0 ≠ 0 := fun kv => hψc _ _ (hz kv)
      have hiff : good (Φ a) ↔ good a := by
        refine ⟨fun h => ?_, hgood a hz⟩
        have := hgood (Φ a) hz' h
        have e : Φ (Φ a) = a := funext fun kv => hψinv kv.1 (a kv)
        rwa [e] at this
      simp only [T, hiff]
      split_ifs
      · rw [star_prod]
        refine Finset.prod_congr rfl fun kv _ => ?_
        rw [hS kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) (Formalism.CyclotomicNorms.Sqf.monic_monicOf _) (hz kv), hΦ, hψm _ _ (hz kv)]
        rfl
      · exact star_zero _
    · push_neg at hz
      obtain ⟨kv, h0⟩ := hz
      rw [hzero a kv h0, hzero (Φ a) kv (by rw [hΦ, hψ0 _ _ h0]; exact h0), star_zero]
  have hfin : (Function.support T).Finite := Set.toFinite _
  have hstar : star (∑ᶠ a, T a) = ∑ᶠ a, star (T a) := by
    have := map_finsum (starAddEquiv (R := ℂ)) hfin
    simpa only [starAddEquiv_apply] using this
  rw [he, hstar]
  simp_rw [key]
  exact finsum_comp_equiv Φ

end GlobalTheory.GoodIdemReal
