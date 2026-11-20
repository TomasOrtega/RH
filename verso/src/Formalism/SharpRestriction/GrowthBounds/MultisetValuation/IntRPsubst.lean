import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AllPlacesOfRestrictions
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.OmegaOfTraceDuality

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

section Gen

variable {K : Type} [Field K] {R : Subring K}

/- English proof (translation)
Introduce `n`. Rewrite using `[map_add]`. Conclude with `R.add_mem (hf n) (hg n)`.
-/
theorem IntR_add {ι : Type} {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f + g) := by
  intro n
  rw [map_add]
  exact R.add_mem (hf n) (hg n)

/- English proof (translation)
Introduce `n`. Rewrite using `[map_zero]`. Conclude with `R.zero_mem`.
-/
theorem IntR_zero {ι : Type} : IntR R (0 : MvPowerSeries ι K) := by
  intro n
  rw [map_zero]
  exact R.zero_mem

/- English proof (translation)
Introduce `n`. Rewrite using `[map_sum]`. Conclude with `R.sum_mem fun a ha => h a ha n`.
-/
theorem IntR_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∑ a ∈ s, f a) := by
  intro n
  rw [map_sum]
  exact R.sum_mem fun a ha => h a ha n

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.
-/
theorem IntR_X {ι : Type} (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf`. Unfold `IntR at hf`. Set `g : MvPowerSeries ι R` to `fun n => ⟨MvPowerSeries.coeff n f, hf n⟩`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_map]`. Both sides reduce to the same expression. Introduce and unpack `⟨g, rfl⟩ n`. Rewrite using `[MvPowerSeries.coeff_map]`.

Conclude with `(MvPowerSeries.coeff n g).2`.
-/
private theorem intR_iff_mem_range_map_subtype {ι : Type} {f : MvPowerSeries ι K} :
    IntR R f ↔ f ∈ (MvPowerSeries.map R.subtype).range := by
  constructor
  · intro hf
    unfold IntR at hf
    let g : MvPowerSeries ι R := fun n => ⟨MvPowerSeries.coeff n f, hf n⟩
    refine ⟨g, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Establish `hprod : ∀ d : σ →₀ ℕ, IntR R (d.prod fun s k => (a s) ^ k)`. Introduce `d`. Rewrite using `[intR_iff_mem_range_map_subtype, Finsupp.prod]`. Conclude with `Subring.prod_mem _ fun s _ => Subring.pow_mem _ (intR_iff_mem_range_map_subtype.1 (ha s)) _`.

Introduce `e`. Rewrite using `[MvPowerSeries.coeff_subst hs]`. Distinguish the cases in `hfin : (Function.support fun d : σ →₀ ℕ => MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s k => (a s) ^ k)).Finite`. Rewrite using `[finsum_eq_sum _ hfin]`. Conclude with `R.sum_mem fun d _ => by`.

Rewrite using `[smul_eq_mul]`. Conclude with `R.mul_mem (hf d) (hprod d e)`. Rewrite using `[finsum_of_infinite_support hfin]`. Conclude with `R.zero_mem`.
-/
theorem IntR_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntR R (a i)) {f : MvPowerSeries σ K}
    (hf : IntR R f) : IntR R (MvPowerSeries.subst a f) := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hprod : ∀ d : σ →₀ ℕ, IntR R (d.prod fun s k => (a s) ^ k) := by
    intro d
    rw [intR_iff_mem_range_map_subtype, Finsupp.prod]
    exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (intR_iff_mem_range_map_subtype.1 (ha s)) _
  intro e
  rw [MvPowerSeries.coeff_subst hs]
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s k => (a s) ^ k)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact R.sum_mem fun d _ => by
      rw [smul_eq_mul]
      exact R.mul_mem (hf d) (hprod d e)
  · rw [finsum_of_infinite_support hfin]
    exact R.zero_mem

/- English proof (translation)
Introduce `n`. Establish `hn : n = Finsupp.single () (n ())` using `Finsupp.unique_single n`. Rewrite using `[hn]`. Conclude with `hf (n ())`.
-/
theorem IntR_of_ps {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) :
    IntR R (f : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := Finsupp.unique_single n
  rw [hn]
  exact hf (n ())

/- English proof (translation)
The claim follows from `IntR_subst (fun _ : Unit => L) (fun _ => hL0) (fun _ => hL) (IntR_of_ps hf)`.
-/
theorem IntR_psubst {τ : Type} {L : MvPowerSeries τ K} (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : IntR R L)
    {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) : IntR R (PowerSeries.subst L f) :=
  IntR_subst (fun _ : Unit => L) (fun _ => hL0) (fun _ => hL) (IntR_of_ps hf)

end Gen

section Mu

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use polynomial arithmetic with `[Nat.mul_le_mul_right (b + 1) ih, Nat.zero_le (b * b * k)]`.
-/
private theorem mul_add_one_le_succ_pow (b j : ℕ) : b * j + 1 ≤ (b + 1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (b + 1) ih, Nat.zero_le (b * b * k)]

/- English proof (translation)
Establish `hvpR : vp ∈ Rp p K' vp`. Unfold `Rp`. Conclude with `Subring.subset_closure (Set.mem_union_right _ rfl)`. Simplify using `only [lamF, lgF, PowerSeries.coeff_mk, Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Establish `hp1 : 1 ≤ p ^ 2` using `Nat.one_le_pow _ _ hp.out.pos`. Establish `hle : (p ^ 2 - 1) * j + 1 ≤ (p ^ 2) ^ j`. Use `mul_add_one_le_succ_pow (p ^ 2 - 1) j` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hp1]`. Then use the resulting hypothesis.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, n - 1 = (p ^ 2 - 1) * j + m := by`. Use `⟨n - 1 - (p ^ 2 - 1) * j, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Generalize the expression as in `(p ^ 2 - 1) * j = A at hle ⊢`. Generalize the expression as in `(p ^ 2) ^ j = B at hle ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hm, pow_add, ← hvp, ← pow_mul]`. Distinguish the cases in `h0 : vp ^ ((p ^ 2 - 1) * j) = 0`. Rewrite using `[h0, zero_mul, zero_mul]`. Conclude with `(Rp p K' vp).zero_mem`.

Rewrite using `[mul_comm (vp ^ ((p ^ 2 - 1) * j)), mul_assoc, mul_inv_cancel₀ h0, mul_one]`. Conclude with `(Rp p K' vp).pow_mem hvpR m`. Rewrite using `[mul_zero]`. Conclude with `(Rp p K' vp).zero_mem`.
-/
theorem lamF_mem (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (n : ℕ) :
    PowerSeries.coeff n (lamF p vp) ∈ Rp p K' vp := by
  have hvpR : vp ∈ Rp p K' vp := by
    unfold Rp
    exact Subring.subset_closure (Set.mem_union_right _ rfl)
  simp only [lamF, lgF, PowerSeries.coeff_mk, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  split_ifs with h
  · have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have hle : (p ^ 2 - 1) * j + 1 ≤ (p ^ 2) ^ j := by
      have := mul_add_one_le_succ_pow (p ^ 2 - 1) j
      rwa [Nat.sub_add_cancel hp1] at this
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = (p ^ 2 - 1) * j + m := by
      refine ⟨n - 1 - (p ^ 2 - 1) * j, ?_⟩
      rw [h]
      generalize (p ^ 2 - 1) * j = A at hle ⊢
      generalize (p ^ 2) ^ j = B at hle ⊢
      omega
    rw [hm, pow_add, ← hvp, ← pow_mul]
    by_cases h0 : vp ^ ((p ^ 2 - 1) * j) = 0
    · rw [h0, zero_mul, zero_mul]
      exact (Rp p K' vp).zero_mem
    · rw [mul_comm (vp ^ ((p ^ 2 - 1) * j)), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      exact (Rp p K' vp).pow_mem hvpR m
  · rw [mul_zero]
    exact (Rp p K' vp).zero_mem

/- English proof (translation)
Set `l0 : PowerSeries (Rp p K' vp)` to `PowerSeries.mk fun n => ⟨_, lamF_mem p K' vp hvp n⟩`. Establish `hmap : PowerSeries.map (Rp p K' vp).subtype l0 = lamF p vp`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Both sides reduce to the same expression.

Establish `hc : PowerSeries.constantCoeff l0 = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lamF p vp` as an intermediate fact. Rewrite `this`, the goal using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[PowerSeries.coeff_mk]`.

Conclude with `this`. Establish `hu : IsUnit (PowerSeries.coeff 1 l0)`. Establish `: PowerSeries.coeff 1 l0 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[PowerSeries.coeff_mk]`.

Conclude with `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_one_lamF hp.out.two_le vp`. Rewrite using `[this]`. Conclude with `isUnit_one`. Establish `h1` using `PowerSeries.subst_substInvOfIsUnit_right l0 hc hu`. Use `⟨PowerSeries.map (Rp p K' vp).subtype (l0.substInvOfIsUnit hu), ?_, fun n => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_substInvOfIsUnit, map_zero]`. Rewrite using `[PowerSeries.coeff_map]`. Conclude with `Subtype.property _`. Establish `h2` using `congrArg (PowerSeries.map (Rp p K' vp).subtype) h1`. Rewrite `h2` using `[Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.ps_map_subst _ (PowerSeries.HasSubst.substInvOfIsUnit l0 hu), hmap, PowerSeries.map_X]`.

Conclude with `h2`.
-/
theorem exists_mu (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) :
    ∃ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 ∧ (∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp) ∧
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X := by
  let l0 : PowerSeries (Rp p K' vp) := PowerSeries.mk fun n => ⟨_, lamF_mem p K' vp hvp n⟩
  have hmap : PowerSeries.map (Rp p K' vp).subtype l0 = lamF p vp := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc : PowerSeries.constantCoeff l0 = 0 := by
    apply Subtype.ext
    have := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lamF p vp
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this ⊢
    rw [PowerSeries.coeff_mk]
    exact this
  have hu : IsUnit (PowerSeries.coeff 1 l0) := by
    have : PowerSeries.coeff 1 l0 = 1 := by
      apply Subtype.ext
      rw [PowerSeries.coeff_mk]
      exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_one_lamF hp.out.two_le vp
    rw [this]
    exact isUnit_one
  have h1 := PowerSeries.subst_substInvOfIsUnit_right l0 hc hu
  refine ⟨PowerSeries.map (Rp p K' vp).subtype (l0.substInvOfIsUnit hu), ?_, fun n => ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_substInvOfIsUnit, map_zero]
  · rw [PowerSeries.coeff_map]
    exact Subtype.property _
  · have h2 := congrArg (PowerSeries.map (Rp p K' vp).subtype) h1
    rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.ps_map_subst _ (PowerSeries.HasSubst.substInvOfIsUnit l0 hu), hmap, PowerSeries.map_X] at h2
    exact h2

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [PowerSeries.coeff_map, logF, lgF, PowerSeries.coeff_mk, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_logF : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := by
  ext n
  simp only [PowerSeries.coeff_map, logF, lgF, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]
  split_ifs <;> simp

end Mu

end Formalism.MainNotions.FormalGroupSystem.Pf
