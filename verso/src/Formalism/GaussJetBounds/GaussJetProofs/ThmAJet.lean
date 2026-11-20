import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementE
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight
import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight
import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity
import Formalism.IncomingBounds.WeightIdentities
import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.GaussJetBounds.GaussJetProofs.FrameCoeffMulLin
import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Collapse

variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)

def jetHom (n : σ →₀ ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ≠ 0 → m.mapDomain lt = n

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[MvPowerSeries.coeff_one]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
theorem jetHom_one : jetHom lt 0 (1 : MvPowerSeries ι K) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_one] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[MvPowerSeries.coeff_mul]`. Take `⟨p, hp, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hm`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h1 : MvPowerSeries.coeff p.1 f ≠ 0` using `left_ne_zero_of_mul hne`.

Establish `h2 : MvPowerSeries.coeff p.2 g ≠ 0` using `right_ne_zero_of_mul hne`. Rewrite using `[← hp, Finsupp.mapDomain_add, hf _ h1, hg _ h2]`.
-/
theorem jetHom_mul {n1 n2 : σ →₀ ℕ} {f g : MvPowerSeries ι K} (hf : jetHom lt n1 f)
    (hg : jetHom lt n2 g) : jetHom lt (n1 + n2) (f * g) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPowerSeries.coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : MvPowerSeries.coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  rw [← hp, Finsupp.mapDomain_add, hf _ h1, hg _ h2]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using jetHom_one (K := K) lt`. Consider the case `succ k ih => rw [pow_succ, succ_nsmul]`. Conclude with `jetHom_mul lt ih hf`.
-/
theorem jetHom_pow {n : σ →₀ ℕ} {f : MvPowerSeries ι K} (hf : jetHom lt n f) (k : ℕ) :
    jetHom lt (k • n) (f ^ k) := by
  induction k with
  | zero => simpa using jetHom_one (K := K) lt
  | succ k ih => rw [pow_succ, succ_nsmul]; exact jetHom_mul lt ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using jetHom_one (K := K) lt`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `jetHom_mul lt (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem jetHom_prod {α : Type*} (s : Finset α) (n : α → σ →₀ ℕ) (F : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, jetHom lt (n a) (F a)) : jetHom lt (∑ a ∈ s, n a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetHom_one (K := K) lt
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact jetHom_mul lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `m hm`. Simplify using `only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] at hm`. Take `⟨i, -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hm`. Use `split_ifs at hne with h`. Substitute `h` using the available equality.

Rewrite using `[Finsupp.mapDomain_single, hc i (left_ne_zero_of_mul hne)]`. Simplify using `at hne`.
-/
theorem jetHom_lin [Fintype ι] (c : ι → K) (t : σ) (hc : ∀ i, c i ≠ 0 → lt i = t) :
    jetHom lt (Finsupp.single t 1) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro m hm
  simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] at hm
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  split_ifs at hne with h
  · subst h; rw [Finsupp.mapDomain_single, hc i (left_ne_zero_of_mul hne)]
  · simp at hne

/- English proof (translation)
Establish `h` using `jetHom_prod lt n.support (fun s => n s • Finsupp.single s 1) (fun s => a s ^ n s) fun s _ => jetHom_pow lt (ha s) (n s)`. Establish `hd : ∑ s ∈ n.support, n s • Finsupp.single s 1 = n`. Repeatedly rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Conclude with `Finsupp.sum_single n`. Rewrite `h` using `[hd]`.

Simplify `h` using `[Finsupp.prod]`.
-/
theorem jetHom_substProd (a : σ → MvPowerSeries ι K)
    (ha : ∀ t, jetHom lt (Finsupp.single t 1) (a t)) (n : σ →₀ ℕ) :
    jetHom lt n (n.prod fun s e => a s ^ e) := by
  classical
  have h := jetHom_prod lt n.support (fun s => n s • Finsupp.single s 1) (fun s => a s ^ n s)
    fun s _ => jetHom_pow lt (ha s) (n s)
  have hd : ∑ s ∈ n.support, n s • Finsupp.single s 1 = n := by
    simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single n
  rw [hd] at h
  simpa [Finsupp.prod] using h

end Collapse

/- English proof (translation)
Unfold `bSum`. Rewrite using `[map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun ab _ => ?_` and prove the remaining obligations. Establish `hlin0 : ∀ s, MvPowerSeries.constantCoeff (linSub M (s, ab.1, ab.2)) = 0` using `fun s => by`. Simplify using `[linSub]`.

Establish `hs` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0`. Establish `hhom : ∀ t, jetHom lt (Finsupp.single t 1) (linSub M (t, ab.1, ab.2))` using `fun t => jetHom_lin lt _ t fun i hi => hMlt _ i hi`. Establish `hlinI : ∀ t, WtGe (1 : ℝ) (fun _ : ι => (0 : ℝ)) 0 (linSub M (t, ab.1, ab.2))`. Introduce `t`. Unfold `linSub`.

Use `wtGe_sum one_pos _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using wtGe_CX (K := K) one_pos (fun _ : ι => (0 : ℝ)) i (hM1 (t, ab.1, ab.2) i)`. Rewrite using `[MvPowerSeries.coeff_subst hs, finsum_eq_single _ (m.mapDomain lt)]`. Rewrite using `[smul_eq_mul, norm_mul]`. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations.

Establish `hp` using `wtGe_prod (K := K) one_pos (r := fun _ : ι => (0 : ℝ)) (m.mapDomain lt).support (fun s => ((m.mapDomain lt) s : ℝ) * 0) (fun s => linSub M (s, ab.1, ab.2) ^ (m.mapDomain lt) s) (fun s _ => wtGe_pow one_pos (hlinI s) _) m`. Rewrite `hp` using `[monoWtGe_iff, Real.one_rpow]`. Simplify `hp` using `[Finsupp.prod]`. Introduce `n hn`. Establish `h0 : MvPowerSeries.coeff m (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hn (jetHom_substProd lt (fun s => linSub M (s, ab.1, ab.2)) hhom n m h).symm`. Rewrite using `[h0, smul_zero]`.
-/
theorem jet_collapse {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type*}
    [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM1 : ∀ x i, ‖M x i‖ ≤ 1) (hMlt : ∀ x i, M x i ≠ 0 → lt i = x.1)
    (be : MvPowerSeries (ZMod d) K) (m : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff m (bSum M be)‖ ≤ ‖MvPowerSeries.coeff (m.mapDomain lt) be‖ := by
  classical
  unfold bSum
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun ab _ => ?_
  have hlin0 : ∀ s, MvPowerSeries.constantCoeff (linSub M (s, ab.1, ab.2)) = 0 := fun s => by
    simp [linSub]
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hhom : ∀ t, jetHom lt (Finsupp.single t 1) (linSub M (t, ab.1, ab.2)) := fun t =>
    jetHom_lin lt _ t fun i hi => hMlt _ i hi
  have hlinI : ∀ t, WtGe (1 : ℝ) (fun _ : ι => (0 : ℝ)) 0 (linSub M (t, ab.1, ab.2)) := by
    intro t
    unfold linSub
    refine wtGe_sum one_pos _ _ fun i _ => ?_
    simpa using wtGe_CX (K := K) one_pos (fun _ : ι => (0 : ℝ)) i (hM1 (t, ab.1, ab.2) i)
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (m.mapDomain lt)]
  · rw [smul_eq_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have hp := wtGe_prod (K := K) one_pos (r := fun _ : ι => (0 : ℝ)) (m.mapDomain lt).support
      (fun s => ((m.mapDomain lt) s : ℝ) * 0)
      (fun s => linSub M (s, ab.1, ab.2) ^ (m.mapDomain lt) s)
      (fun s _ => wtGe_pow one_pos (hlinI s) _) m
    rw [monoWtGe_iff, Real.one_rpow] at hp
    simpa [Finsupp.prod] using hp
  · intro n hn
    have h0 : MvPowerSeries.coeff m (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) = 0 := by
      by_contra h
      exact hn (jetHom_substProd lt (fun s => linSub M (s, ab.1, ab.2)) hhom n m h).symm
    rw [h0, smul_zero]

/- English proof (translation)
Establish `h' : ((s.val + α : ℕ) : ZMod d) = ((s'.val + β : ℕ) : ZMod d)` using `by push_cast; rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Rewrite `h'` using `[ZMod.natCast_eq_natCast_iff]`. Establish `h2` using `Nat.ModEq.of_dvd (even_iff_two_dvd.mp hde) h'`. Unfold `Nat.ModEq at h2`. Rewrite using `[Nat.odd_iff]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem jet_parity {d : ℕ} [NeZero d] (hde : Even d) {s s' : ZMod d} {α β : ℕ}
    (hs : s.val % 2 = 0) (hs' : s'.val % 2 = 1) (h : s + (α : ZMod d) = s' + (β : ZMod d)) :
    Odd (α + β) := by
  have h' : ((s.val + α : ℕ) : ZMod d) = ((s'.val + β : ℕ) : ZMod d) := by
    push_cast; rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := Nat.ModEq.of_dvd (even_iff_two_dvd.mp hde) h'
  unfold Nat.ModEq at h2
  rw [Nat.odd_iff]
  omega

/- English proof (translation)
Take `⟨s, s', α', β', hs, hs', -, heq, hn⟩` from `h`. Establish `hss : s ≠ s'` using `by rintro rfl; omega`. Establish `hpar` using `jet_parity hde hs hs' heq`. Establish `hpos : ∀ k : ℕ, l ^ k ≠ 0` using `fun k => pow_ne_zero _ (by omega)`. Establish `hinj : ∀ a b : ℕ, l ^ a = l ^ b → a = b` using `fun a b hab => Nat.pow_right_injective hl hab`.

Establish `F1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s = l ^ α'`. Rewrite using `[hn]`. Simplify using `[hss]`. Establish `F2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s' = l ^ β'`. Rewrite using `[hn]`.

Simplify using `[Ne.symm hss]`. Establish `F3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 → t = s ∨ t = s'`. Introduce `t ht`. Rewrite `ht` using `[hn]`. Assume the negation of the conclusion as `hc`.

Simplify using `only [not_or] at hc`. Apply `ht` to reduce the goal to its premises. Simplify using `[Ne.symm hc.1, Ne.symm hc.2]`. Establish `G3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 → t = t1 ∨ t = t2`. Introduce `t ht`.

Assume the negation of the conclusion as `hc`. Simplify using `only [not_or] at hc`. Apply `ht` to reduce the goal to its premises. Simplify using `[Ne.symm hc.1, Ne.symm hc.2]`. Establish `ht12 : t1 ≠ t2`.

Introduce and unpack `rfl`. Establish `a` using `G3 s (by rw [F1]; exact hpos _)`. Establish `b` using `G3 s' (by rw [F2]; exact hpos _)`. Simplify using `only [or_self] at a b`. Conclude with `hss (a.trans b.symm)`.

Establish `H1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t1 = l ^ α`. Simplify using `[ht12]`. Establish `H2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t2 = l ^ β`. Simplify using `[Ne.symm ht12]`. Use `⟨ht12, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rcases F3 t1 (by rw [H1]; exact hpos _) with h1 | h1 <;>`. Break down `F3 t2 (by rw [H2]; exact hpos _) with h2 | h2` into its components or cases. Conclude with `absurd (h1.trans h2.symm) ht12`. Substitute `h1 h2` using the available equality. Establish `e1` using `hinj _ _ (H1.symm.trans F1)`.

Establish `e2` using `hinj _ _ (H2.symm.trans F2)`. Substitute `e1 e2` using the available equality. Conclude with `⟨heq, hpar⟩`. Substitute `h1 h2` using the available equality. Establish `e1` using `hinj _ _ (H1.symm.trans F2)`.

Establish `e2` using `hinj _ _ (H2.symm.trans F1)`. Substitute `e1 e2` using the available equality. Conclude with `⟨heq.symm, by rwa [add_comm]⟩`. Conclude with `absurd (h1.trans h2.symm) ht12`.
-/
theorem jet_bipower {d : ℕ} [NeZero d] (hde : Even d) {l : ℕ} (hl : 2 ≤ l) {t1 t2 : ZMod d}
    {α β : ℕ} (h : IsBiPower l (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β))) :
    t1 ≠ t2 ∧ t1 + (α : ZMod d) = t2 + (β : ZMod d) ∧ Odd (α + β) := by
  classical
  obtain ⟨s, s', α', β', hs, hs', -, heq, hn⟩ := h
  have hss : s ≠ s' := by rintro rfl; omega
  have hpar := jet_parity hde hs hs' heq
  have hpos : ∀ k : ℕ, l ^ k ≠ 0 := fun k => pow_ne_zero _ (by omega)
  have hinj : ∀ a b : ℕ, l ^ a = l ^ b → a = b := fun a b hab =>
    Nat.pow_right_injective hl hab
  have F1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s = l ^ α' := by
    rw [hn]; simp [hss]
  have F2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s' = l ^ β' := by
    rw [hn]; simp [Ne.symm hss]
  have F3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = s ∨ t = s' := by
    intro t ht
    rw [hn] at ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have G3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = t1 ∨ t = t2 := by
    intro t ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have ht12 : t1 ≠ t2 := by
    rintro rfl
    have a := G3 s (by rw [F1]; exact hpos _)
    have b := G3 s' (by rw [F2]; exact hpos _)
    simp only [or_self] at a b
    exact hss (a.trans b.symm)
  have H1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t1 = l ^ α := by
    simp [ht12]
  have H2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t2 = l ^ β := by
    simp [Ne.symm ht12]
  refine ⟨ht12, ?_⟩
  rcases F3 t1 (by rw [H1]; exact hpos _) with h1 | h1 <;>
    rcases F3 t2 (by rw [H2]; exact hpos _) with h2 | h2
  · exact absurd (h1.trans h2.symm) ht12
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F1)
    have e2 := hinj _ _ (H2.symm.trans F2)
    subst e1 e2
    exact ⟨heq, hpar⟩
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F2)
    have e2 := hinj _ _ (H2.symm.trans F1)
    subst e1 e2
    exact ⟨heq.symm, by rwa [add_comm]⟩
  · exact absurd (h1.trans h2.symm) ht12

/- English proof (translation)
Unfold `rowRad`. Rewrite using `[if_neg (by simp [hi])]`. Break down `spec i with _ | ⟨s, j⟩` into its components or cases. Conclude with `le_rfl`. Simplify using `only split_ifs`.

Conclude with `le_max_left _ _`. Conclude with `le_max_left _ _`.
-/
theorem jet_rowRad_ge {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false) :
    sig (lt i) ≤ rowRad l sig eps lt isTop spec i := by
  unfold rowRad
  rw [if_neg (by simp [hi])]
  rcases spec i with _ | ⟨s, j⟩
  · exact le_rfl
  · dsimp only
    split_ifs
    · exact le_max_left _ _
    · exact le_max_left _ _

/- English proof (translation)
Consider the cases of `hi : isTop i`. Conclude with `(hs _).trans (jet_rowRad_ge l sig eps lt isTop spec i hi)`. Unfold `rowRad`. Rewrite using `[if_pos hi]`. Conclude with `he _`.
-/
theorem jet_rowRad_nonneg {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (hs : ∀ s, 0 ≤ sig s)
    (he : ∀ s, 0 ≤ eps s) (i : ι) : 0 ≤ rowRad l sig eps lt isTop spec i := by
  cases hi : isTop i
  · exact (hs _).trans (jet_rowRad_ge l sig eps lt isTop spec i hi)
  · unfold rowRad; rw [if_pos hi]; exact he _

/- English proof (translation)
Unfold `rowRad`. Rewrite using `[if_pos hi]`.
-/
theorem jet_rowRad_top {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = true) :
    rowRad l sig eps lt isTop spec i = eps (lt i) := by
  unfold rowRad; rw [if_pos hi]

/- English proof (translation)
Unfold `rowRad`. Rewrite using `[if_neg (by simp [hi]), hs]`.
-/
theorem jet_rowRad_spec {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false)
    {s0 : ZMod d} {j : ℤ} (hs : spec i = some (s0, j)) :
    rowRad l sig eps lt isTop spec i = if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s0)
      else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹ := by
  unfold rowRad
  rw [if_neg (by simp [hi]), hs]

end Formalism.DworkPowerSeriesWeights
