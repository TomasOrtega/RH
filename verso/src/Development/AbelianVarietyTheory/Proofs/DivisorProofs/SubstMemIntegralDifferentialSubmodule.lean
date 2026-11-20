import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hai : a ≠ i` using `by rintro rfl; exact ha hi`. Rewrite using `[Finset.erase_insert_of_ne hai, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]`.
-/
theorem derivation_prod_erase {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (S : Finset ι) :
    D (∏ s ∈ S, f s) = ∑ i ∈ S, (∏ s ∈ S.erase i, f s) * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := by rintro rfl; exact ha hi
    rw [Finset.erase_insert_of_ne hai,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]

/- English proof (translation)
Rewrite using `[derivation_prod_erase]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_pow, nsmul_eq_mul, mul_assoc, mul_left_comm]`.
-/
theorem pderiv_prod_pow {R τ σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ]
    (u : σ → MvPowerSeries τ R) (a : σ → ℕ) (j : τ) :
    pderiv R j (∏ s, u s ^ a s) =
      ∑ i, a i • ((∏ s ∈ Finset.univ.erase i, u s ^ a s) * (u i ^ (a i - 1) * pderiv R j (u i))) := by
  rw [derivation_prod_erase]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_pow, nsmul_eq_mul, mul_assoc, mul_left_comm]

/- English proof (translation)
Introduce `p _ k _ _ _ σ τ _ u f hu0 hu hf`. Establish `: Fintype σ` using `Fintype.ofFinite σ`. Use `set φ := algebraMap (WittVector p k) (Fr p k) with hφ`. Establish `ha : HasSubst u` using `hasSubst_of_constantCoeff_zero hu0`. Establish `hlift : ∀ i, ∃ v : MvPowerSeries τ (WittVector p k), MvPowerSeries.map φ v = u i`.

Introduce `i`. Establish `hui : ∀ α, ∃ w : WittVector p k, coeff α (u i) = φ (1 * w)` using `hu i`. Set `w0 : MvPowerSeries τ (WittVector p k)` to `fun α => (hui α).choose`. Use `⟨w0, ?_⟩` and prove the remaining obligations. Use extensionality with `α`.

Rewrite using `[coeff_map, (hui α).choose_spec, one_mul]`. Both sides reduce to the same expression. Use `choose v hv using hlift`. Introduce `γ j`. Rewrite using `[coeff_subst ha]`.

Establish `hP : ∀ α : σ →₀ ℕ, (α.prod fun s e => u s ^ e) = MvPowerSeries.map φ (∏ s, v s ^ α s)`. Introduce `α`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => by rw [map_pow, hv]`. Establish `hterm : ∀ α : σ →₀ ℕ, (γ j : Fr p k) * (coeff α f • coeff γ (α.prod fun s e => u s ^ e)) ∈ φ.range`.

Introduce `α`. Rewrite using `[hP, coeff_map, smul_eq_mul]`. Distinguish the cases in `hγ : γ j = 0`. Rewrite using `[hγ, Nat.cast_zero, zero_mul]`. Conclude with `zero_mem _`.

Establish `hle : Finsupp.single j 1 ≤ γ`. Introduce `t`. Distinguish the cases in `ht : t = j`. Substitute `ht` using the available equality. Simplify using `only [Finsupp.single_eq_same]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm ht)]`. Conclude with `Nat.zero_le _`. Use `set δ := γ - Finsupp.single j 1 with hδ`. Establish `hδγ : δ + Finsupp.single j 1 = γ` using `tsub_add_cancel_of_le hle`.

Establish `hδj : (δ j : Fr p k) + 1 = γ j`. Rewrite using `[← hδγ, Finsupp.add_apply, Finsupp.single_eq_same]`. Use `push_cast`. Both sides reduce to the same expression. Establish `key` using `coeff_pderiv (R := WittVector p k) (i := j) (∏ s, v s ^ α s) δ`.

Rewrite `key` using `[hδγ, pderiv_prod_pow, map_sum]`. Establish `hk : (γ j : Fr p k) * φ (coeff γ (∏ s, v s ^ α s)) = φ (∑ i, coeff δ (α i • ((∏ s ∈ Finset.univ.erase i, v s ^ α s) * (v i ^ (α i - 1) * pderiv (WittVector p k) j (v i)))))`. Rewrite using `[key, map_mul, map_add, map_natCast, map_one, ← hδj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_left_comm, hk, map_sum, Finset.mul_sum]`.

Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `(hf : ∀ (α : σ →₀ ℕ) (i : σ), ∃ w : WittVector p k, (α i : Fr p k) * coeff α f = φ w) α i`. Rewrite using `[map_nsmul, map_nsmul, nsmul_eq_mul, ← mul_assoc, mul_comm (coeff α f), hw, ← map_mul]`. Conclude with `⟨_, rfl⟩`. Establish `hfin` using `coeff_subst_finite ha f γ`.

Rewrite using `[finsum_eq_sum _ hfin, Finset.mul_sum]`. Establish `hmem : (γ j : Fr p k) * ∑ α ∈ hfin.toFinset, coeff α f • coeff γ (α.prod fun s e => u s ^ e) ∈ φ.range`. Rewrite using `[Finset.mul_sum]`. Conclude with `Subring.sum_mem _ fun α _ => hterm α`. Rewrite using `[← Finset.mul_sum]`.

Take `⟨w, hw⟩` from `hmem`. Conclude with `⟨w, hw.symm⟩`.
-/
theorem subst_mem_quasiInt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  intro p _ k _ _ _ σ τ _ u f hu0 hu hf
  classical
  have : Fintype σ := Fintype.ofFinite σ
  set φ := algebraMap (WittVector p k) (Fr p k) with hφ
  have ha : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hlift : ∀ i, ∃ v : MvPowerSeries τ (WittVector p k), MvPowerSeries.map φ v = u i := by
    intro i
    have hui : ∀ α, ∃ w : WittVector p k, coeff α (u i) = φ (1 * w) := hu i
    let w0 : MvPowerSeries τ (WittVector p k) := fun α => (hui α).choose
    refine ⟨w0, ?_⟩
    ext α
    rw [coeff_map, (hui α).choose_spec, one_mul]
    rfl
  choose v hv using hlift
  intro γ j
  rw [coeff_subst ha]
  have hP : ∀ α : σ →₀ ℕ, (α.prod fun s e => u s ^ e) =
      MvPowerSeries.map φ (∏ s, v s ^ α s) := by
    intro α
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_pow, hv]
  have hterm : ∀ α : σ →₀ ℕ,
      (γ j : Fr p k) * (coeff α f • coeff γ (α.prod fun s e => u s ^ e)) ∈ φ.range := by
    intro α
    rw [hP, coeff_map, smul_eq_mul]
    by_cases hγ : γ j = 0
    · rw [hγ, Nat.cast_zero, zero_mul]; exact zero_mem _
    have hle : Finsupp.single j 1 ≤ γ := by
      intro t
      by_cases ht : t = j
      · subst ht; simp only [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm ht)]; exact Nat.zero_le _
    set δ := γ - Finsupp.single j 1 with hδ
    have hδγ : δ + Finsupp.single j 1 = γ := tsub_add_cancel_of_le hle
    have hδj : (δ j : Fr p k) + 1 = γ j := by
      rw [← hδγ, Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; rfl
    have key := coeff_pderiv (R := WittVector p k) (i := j) (∏ s, v s ^ α s) δ
    rw [hδγ, pderiv_prod_pow, map_sum] at key
    have hk : (γ j : Fr p k) * φ (coeff γ (∏ s, v s ^ α s)) =
        φ (∑ i, coeff δ (α i • ((∏ s ∈ Finset.univ.erase i, v s ^ α s) *
          (v i ^ (α i - 1) * pderiv (WittVector p k) j (v i))))) := by
      rw [key, map_mul, map_add, map_natCast, map_one, ← hδj]
      ring
    rw [mul_left_comm, hk, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    obtain ⟨w, hw⟩ := (hf : ∀ (α : σ →₀ ℕ) (i : σ), ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = φ w) α i
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, ← mul_assoc, mul_comm (coeff α f), hw, ← map_mul]
    exact ⟨_, rfl⟩
  have hfin := coeff_subst_finite ha f γ
  rw [finsum_eq_sum _ hfin, Finset.mul_sum]
  have hmem : (γ j : Fr p k) * ∑ α ∈ hfin.toFinset, coeff α f • coeff γ (α.prod fun s e => u s ^ e)
      ∈ φ.range := by
    rw [Finset.mul_sum]; exact Subring.sum_mem _ fun α _ => hterm α
  rw [← Finset.mul_sum]
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw.symm⟩

end Katz

end GlobalTheory
