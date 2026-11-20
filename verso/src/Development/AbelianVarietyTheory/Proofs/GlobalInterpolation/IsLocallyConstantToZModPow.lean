import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.Riemann

variable {p : ℕ} [Fact p.Prime]

noncomputable def resid (r n : ℕ) (x : Fin r → ℤ_[p]) : Fin r → ℕ :=
  fun j => (PadicInt.toZModPow n (x j)).val

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ)` using `zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _`. Use `filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy`. Rewrite `hy` using `[Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `hy`.
-/
theorem isLocallyConstant_toZModPow (n : ℕ) :
    IsLocallyConstant fun x : ℤ_[p] => PadicInt.toZModPow n x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_continuous]`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `(((isLocallyConstant_toZModPow (p := p) n).comp ZMod.val).comp_continuous (continuous_apply j)).continuous`.
-/
theorem isLocallyConstant_resid (r n : ℕ) : IsLocallyConstant (resid (p := p) r n) := by
  rw [IsLocallyConstant.iff_continuous]
  refine continuous_pi fun j => ?_
  exact (((isLocallyConstant_toZModPow (p := p) n).comp ZMod.val).comp_continuous
    (continuous_apply j)).continuous

/- English proof (translation)
Use `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `j`. Conclude with `Finset.mem_range.2 (ZMod.val_lt _)`.
-/
theorem resid_mem (r n : ℕ) (x : Fin r → ℤ_[p]) :
    resid r n x ∈ Fintype.piFinset fun _ : Fin r => Finset.range (p ^ n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Fintype.mem_piFinset]
  intro j
  exact Finset.mem_range.2 (ZMod.val_lt _)

/- English proof (translation)
Use `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Establish `hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ)` using `zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _`. Rewrite using `[dist_pi_le_iff hp.le]`. Introduce `j`. Rewrite using `[dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`.

Simplify using `[resid]`.
-/
theorem dist_resid (r n : ℕ) (x : Fin r → ℤ_[p]) :
    dist x (fun j => ((resid r n x j : ℕ) : ℤ_[p])) ≤ (p : ℝ) ^ (-n : ℤ) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [dist_pi_le_iff hp.le]
  intro j
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
  simp [resid]

noncomputable def ind (r n : ℕ) (a : Fin r → ℕ) : C(Fin r → ℤ_[p], ℂ_[p]) :=
  ⟨fun x => if resid r n x = a then 1 else 0,
    ((isLocallyConstant_resid (p := p) r n).comp fun b => if b = a then (1 : ℂ_[p]) else 0).continuous⟩

/- English proof (translation)
Rewrite using `[ContinuousMap.norm_le _ zero_le_one]`. Introduce `x`. Use `show ‖if resid r n x = a then (1 : ℂ_[p]) else 0‖ ≤ 1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_ind_le (r n : ℕ) (a : Fin r → ℕ) : ‖ind (p := p) r n a‖ ≤ 1 := by
  rw [ContinuousMap.norm_le _ zero_le_one]
  intro x
  show ‖if resid r n x = a then (1 : ℂ_[p]) else 0‖ ≤ 1
  split_ifs <;> simp

/- English proof (translation)
Introduce `p r _ μ I g hμ F _ ε hε`. Establish `hμ' : ∀ f, ‖μ f‖ ≤ ‖f‖` using `fun f => (μ.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _) hμ)`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hev : ∀ i, ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : Fin r → ℤ_[p], dist x y ≤ (p : ℝ) ^ (-n : ℤ) → dist (g i x) (g i y) < ε / 2`. Introduce `i`.

Take `⟨δ, hδ, h⟩` from `Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous (g i).continuous) (ε / 2) (half_pos hε)`. Establish `ht : Filter.Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)`. Use `filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn x y hxy`. Use `h (hxy.trans_lt ?_)` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`.

Conclude with `hn`. Take `⟨n, hn⟩` from `((Filter.eventually_all_finset F).2 fun i _ => hev i).exists`. Use `set S : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range (p ^ n) with hS`. Use `⟨Finsupp.onFinset S (fun a => if a ∈ S then μ (ind r n a) else 0) (fun a ha => by by_contra h; simp [h] at ha), Set.subset_univ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Rewrite using `[Finsupp.onFinset_apply]`. Use `split_ifs`. Conclude with `(hμ' _).trans (norm_ind_le r n a)`. Simplify using the standard rewrite rules. Introduce `i hi`.

Rewrite using `[Finsupp.onFinset_sum _ (by simp)]`. Establish `h1 : (∑ a ∈ S, (if a ∈ S then μ (ind r n a) else 0) * g i fun j => (a j : ℤ_[p])) = μ (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[if_pos ha, map_smul, smul_eq_mul, mul_comm]`.

Use `beta_reduce`. Rewrite using `[h1, ← map_sub]`. Use `(hμ' _).trans_lt (lt_of_le_of_lt ?_ (half_lt_self hε))` and prove the remaining obligations. Rewrite using `[ContinuousMap.norm_le _ (half_pos hε).le]`. Introduce `x`.

Establish `h2 : (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a) x = g i fun j => ((resid r n x j : ℕ) : ℤ_[p])`. Rewrite using `[ContinuousMap.sum_apply, Finset.sum_eq_single (resid r n x)]`. Simplify using `[ind]`. Introduce `b _ hb`. Simplify using `[ind, Ne.symm hb]`.

Introduce `h`. Conclude with `absurd (resid_mem r n x) h`. Rewrite using `[ContinuousMap.sub_apply, h2, ← dist_eq_norm]`. Conclude with `(hn i hi _ _ (dist_resid r n x)).le`.
-/
theorem riemann_sums : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]) (I : Type) (g : I → C(Fin r → ℤ_[p], ℂ_[p])), ‖μ‖ ≤ 1 → InIntClosure (Set.univ : Set (Fin r → ℕ)) (fun a i => g i fun j => (a j : ℤ_[p])) Set.univ fun i => μ (g i) := by
  intro p r _ μ I g hμ F _ ε hε
  classical
  have hμ' : ∀ f, ‖μ f‖ ≤ ‖f‖ := fun f =>
    (μ.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _) hμ)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hev : ∀ i, ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : Fin r → ℤ_[p],
      dist x y ≤ (p : ℝ) ^ (-n : ℤ) → dist (g i x) (g i y) < ε / 2 := by
    intro i
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous (g i).continuous) (ε / 2) (half_pos hε)
    have ht : Filter.Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn x y hxy
    refine h (hxy.trans_lt ?_)
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hn
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset F).2 fun i _ => hev i).exists
  set S : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range (p ^ n) with hS
  refine ⟨Finsupp.onFinset S (fun a => if a ∈ S then μ (ind r n a) else 0)
    (fun a ha => by by_contra h; simp [h] at ha), Set.subset_univ _, ?_, ?_⟩
  · intro a
    rw [Finsupp.onFinset_apply]
    split_ifs
    · exact (hμ' _).trans (norm_ind_le r n a)
    · simp
  · intro i hi
    rw [Finsupp.onFinset_sum _ (by simp)]
    have h1 : (∑ a ∈ S, (if a ∈ S then μ (ind r n a) else 0) * g i fun j => (a j : ℤ_[p]))
        = μ (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos ha, map_smul, smul_eq_mul, mul_comm]
    beta_reduce
    rw [h1, ← map_sub]
    refine (hμ' _).trans_lt (lt_of_le_of_lt ?_ (half_lt_self hε))
    rw [ContinuousMap.norm_le _ (half_pos hε).le]
    intro x
    have h2 : (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a) x
        = g i fun j => ((resid r n x j : ℕ) : ℤ_[p]) := by
      rw [ContinuousMap.sum_apply, Finset.sum_eq_single (resid r n x)]
      · simp [ind]
      · intro b _ hb
        simp [ind, Ne.symm hb]
      · intro h
        exact absurd (resid_mem r n x) h
    rw [ContinuousMap.sub_apply, h2, ← dist_eq_norm]
    exact (hn i hi _ _ (dist_resid r n x)).le

end GlobalTheory.MomT.Riemann
