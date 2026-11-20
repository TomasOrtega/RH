import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.KernelLemma
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

/- English proof (translation)
Establish `h` using `lfD_cnt (fun c => ε c ≠ ε a) hab`. Establish `h1 : (univ.filter fun c => c = a ∧ ε c ≠ ε a).card = 0`. Rewrite using `[lfD_single]`. Simplify using the standard rewrite rules. Establish `h2 : (univ.filter fun c => c = b ∧ ε c ≠ ε a).card = 0`.

Rewrite using `[lfD_single]`. Simplify using `[he]`. Establish `h3 : (univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card = 0`. Rewrite using `[card_eq_zero, filter_eq_empty_iff]`. Introduce `c _ hc'`.

Conclude with `hc'.2.2 (hc c hc'.1 hc'.2.1)`. Simplify using `only [rhoN, ← he]`. Rewrite `h` using `[h1, h2, h3]`. Establish `h'` using `congrArg (Nat.cast : ℕ → ℝ) h`. Move the coercions through the operations in `at h'`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gb_rhoN_eq (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c = ε a) : rhoN ε a = rhoN ε b := by
  have h := lfD_cnt (fun c => ε c ≠ ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc'.2.2 (hc c hc'.1 hc'.2.1)
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

/- English proof (translation)
Establish `h` using `lfD_cnt (fun c => ε c = ε a) hab`. Establish `h1 : (univ.filter fun c => c = a ∧ ε c = ε a).card = 1`. Rewrite using `[lfD_single]`. Simplify using the standard rewrite rules. Establish `h2 : (univ.filter fun c => c = b ∧ ε c = ε a).card = 1`.

Rewrite using `[lfD_single]`. Simplify using `[he]`. Simplify using `only [rhoC, ← he]`. Rewrite `h` using `[h1, h2]`. Establish `h'` using `congrArg (Nat.cast : ℕ → ℝ) h`.

Move the coercions through the operations in `at h'`. Establish `: (0 : ℝ) ≤ ((univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gb_rhoC_ge (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h := lfD_cnt (fun c => ε c = ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp [he]
  simp only [rhoC, ← he]
  rw [h1, h2] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  have : (0 : ℝ) ≤ ((univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Unfold `phSum`. Rewrite using `[sum_root_apply]`. Establish `h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.2 = a).card : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : ((Ph.filter fun y => y.1 = a).card : ℝ) ≤ oppCount ε a` using `by exact_mod_cast card_fst_le ε Ph hnc a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gb_phSum_le (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : phSum Ph a ≤ oppCount ε a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.2 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.1 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_fst_le ε Ph hnc a
  linarith

/- English proof (translation)
Unfold `phSum`. Rewrite using `[sum_root_apply]`. Establish `h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.1 = a).card : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : ((Ph.filter fun y => y.2 = a).card : ℝ) ≤ oppCount ε a` using `by exact_mod_cast card_snd_le ε Ph hnc a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gb_phSum_ge (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : -(oppCount ε a : ℝ) ≤ phSum Ph a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.1 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.2 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_snd_le ε Ph hnc a
  linarith

/- English proof (translation)
Take `⟨hmono, h, hh, hn⟩` from `hg`. Establish `hF : Formalism.REAL.KRel ε E` using `fun a b c d _ _ => hE a b c d`. Establish `hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2` using `fun x hx => (hPh x hx).2`. Establish `hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W`. Establish `: lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph` using `by unfold lowK; abel`.

Rewrite using `[this]`. Conclude with `hW`. Introduce `a b hab he`. Simplify using `only [Pi.sub_apply]`. Distinguish the cases in `hc : ∃ c, a < c ∧ c < b ∧ ε c ≠ ε a`.

Take `⟨c, hac, hcb, hce⟩` from `hc`. Establish `g1` using `hh a c (Ne.symm hce)`. Establish `g2` using `hh c b (by rw [← he]; exact hce)`. Rewrite `g1` using `[abs_of_pos (sub_pos.mpr (hmono hac))]`. Rewrite `g2` using `[abs_of_pos (sub_pos.mpr (hmono hcb))]`.

Establish `pa` using `gb_phSum_le ε hnc a`. Establish `pb` using `gb_phSum_ge ε hnc b`. Establish `ob : oppCount ε b = oppCount ε a` using `by unfold oppCount; rw [he]`. Rewrite `pb` using `[ob]`. Establish `oc : 2 ≤ oppCount ε c`.

Unfold `oppCount`. Establish `hsub : ({a, b} : Finset (Fin n)) ⊆ univ.filter fun x => ε x ≠ ε c`. Introduce `x hx`. Simplify using `only [mem_insert, mem_singleton] at hx`. Simplify using `only [mem_filter, mem_univ, true_and]`.

Break down `hx with rfl | rfl` into its components or cases. Conclude with `Ne.symm hce`. Rewrite using `[← he]`. Conclude with `Ne.symm hce`. Use `Finset.card_le_card hsub` as an intermediate fact.

Rewrite `this` using `[Finset.card_pair hab.ne]`. Then use the resulting hypothesis. Establish `hsum` using `oppCount_add ε (Ne.symm hce)`. Establish `oc' : (2:ℝ) ≤ oppCount ε c` using `by exact_mod_cast oc`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hc`.

Take `⟨N, hN⟩` from `HW.kIrrHW_int ε hF hW' a b hab he`. Establish `hC` using `gb_rhoC_ge ε hab he`. Establish `hR` using `gb_rhoN_eq ε hab he hc`. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply] at hN`. Establish `: (0:ℝ) ≤ N` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dirac_block {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph) {W : Submodule ℂ M}
    (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W) : BlockAnti ε (lam - phSum Ph) := by
  classical
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  intro a b hab he
  simp only [Pi.sub_apply]
  by_cases hc : ∃ c, a < c ∧ c < b ∧ ε c ≠ ε a
  · obtain ⟨c, hac, hcb, hce⟩ := hc
    have g1 := hh a c (Ne.symm hce)
    have g2 := hh c b (by rw [← he]; exact hce)
    rw [abs_of_pos (sub_pos.mpr (hmono hac))] at g1
    rw [abs_of_pos (sub_pos.mpr (hmono hcb))] at g2
    have pa := gb_phSum_le ε hnc a
    have pb := gb_phSum_ge ε hnc b
    have ob : oppCount ε b = oppCount ε a := by unfold oppCount; rw [he]
    rw [ob] at pb
    have oc : 2 ≤ oppCount ε c := by
      unfold oppCount
      have hsub : ({a, b} : Finset (Fin n)) ⊆ univ.filter fun x => ε x ≠ ε c := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [mem_filter, mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact Ne.symm hce
        · rw [← he]; exact Ne.symm hce
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hab.ne] at this
    have hsum := oppCount_add ε (Ne.symm hce)
    have oc' : (2:ℝ) ≤ oppCount ε c := by exact_mod_cast oc
    linarith
  · push Not at hc
    obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW' a b hab he
    have hC := gb_rhoC_ge ε hab he
    have hR := gb_rhoN_eq ε hab he hc
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
    have : (0:ℝ) ≤ N := Nat.cast_nonneg _
    linarith

/- English proof (translation)
Establish `hb` using `dirac_block hg hE hPh hW`. Take `⟨hmono, h, hh, hn⟩` from `hg`. Establish `hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2` using `fun x hx => (hPh x hx).2`. Establish `hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W`. Establish `: lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph` using `by unfold lowK; abel`.

Rewrite using `[this]`. Conclude with `hW`. Take `⟨z, hzW, -, hz0, hzK⟩` from `exists_nonzero_physical_highestWeight_vector_tensFock ε hE hb hW'`. Establish `hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - phSum Ph - rhoC ε) + rhoHol ε) z` using `hzK`. Establish `hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z`.

Take `⟨z0, hz0eq⟩` from `LinearMap.mem_range.mp hzW`. Rewrite using `[ssh_casimir_eT, ← hz0eq]`. Use `clear hz0eq`. Proceed by induction on `z0 using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Establish `hD2` using `two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas`. Establish `hval : nsq (lam - phSum Ph - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam = nsq (lam - phSum Ph) - nsq lam`. Rewrite using `[sub_add_cancel]`.

Unfold `casVal`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x0, hx0⟩` from `hne`. Establish `hx0'` using `(hPh x0 hx0).1`. Establish `hn2 : (2 : ℝ) ≤ n`.

Use `x0.2.2` as an intermediate fact. Use `Fin.lt_def.mp hx0'` as an intermediate fact. Conclude with `(show 2 ≤ n by omega)` after adjusting the coercions. Establish `hpos : ∀ x ∈ Ph, h ≤ lam x.1 - lam x.2`. Introduce `x hx`.

Use `hh x.1 x.2 (hnc x hx)` as an intermediate fact. Rewrite `this` using `[abs_of_pos (sub_pos.mpr (hmono (hPh x hx).1))]`. Then use the resulting hypothesis. Establish `hker` using `kernel_lemma ε lam (h := h) (by linarith) Ph hnc hpos`. Establish `hcard : (1 : ℝ) ≤ Ph.card`. Conclude with `Finset.card_pos.mpr ⟨x0, hx0⟩` after adjusting the coercions.

Establish `hneg : nsq (lam - phSum Ph) - nsq lam < 0`. Establish `h2n : 0 < 2 * h - n` using `by linarith`. Establish `: 0 < (2 * h - n) * Ph.card` using `by positivity`. Unfold `phSum`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef`. Establish `key : tform z ((2 : ℂ) • (D * D) z) = ((nsq (lam - phSum Ph) - nsq lam : ℝ) : ℂ) * tform z z`. Rewrite using `[hD2, tform_smul_right, ← hval]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `key` using `[tform_smul_right, Module.End.mul_apply, ← tform_D hU]`. Establish `hre` using `congrArg Complex.re key`. Rewrite `hre` using `[Complex.re_ofReal_mul]`. Simplify using `only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre`. Establish `p1` using `tform_self_re_nonneg (D z)`.

Establish `p2` using `tform_self_re_pos hz0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dirac_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph)
    (hne : Ph.Nonempty) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hb := dirac_block hg hE hPh hW
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  obtain ⟨z, hzW, -, hz0, hzK⟩ := exists_nonzero_physical_highestWeight_vector_tensFock ε hE hb hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - phSum Ph - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - phSum Ph - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam =
      nsq (lam - phSum Ph) - nsq lam := by
    rw [sub_add_cancel]
    unfold casVal
    ring
  obtain ⟨x0, hx0⟩ := hne
  have hx0' := (hPh x0 hx0).1
  have hn2 : (2 : ℝ) ≤ n := by
    have := x0.2.2
    have := Fin.lt_def.mp hx0'
    exact_mod_cast (show 2 ≤ n by omega)
  have hpos : ∀ x ∈ Ph, h ≤ lam x.1 - lam x.2 := by
    intro x hx
    have := hh x.1 x.2 (hnc x hx)
    rwa [abs_of_pos (sub_pos.mpr (hmono (hPh x hx).1))] at this
  have hker := kernel_lemma ε lam (h := h) (by linarith) Ph hnc hpos
  have hcard : (1 : ℝ) ≤ Ph.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x0, hx0⟩
  have hneg : nsq (lam - phSum Ph) - nsq lam < 0 := by
    have h2n : 0 < 2 * h - n := by linarith
    have : 0 < (2 * h - n) * Ph.card := by positivity
    unfold phSum
    linarith
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((nsq (lam - phSum Ph) - nsq lam : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  nlinarith

/- English proof (translation)
Establish `hP : phSum {(a, b)} = root a b` using `by simp [phSum]`. Use `dirac_sharp hg hE hU (Ph := {(a, b)}) ?_ (singleton_nonempty _) (by rw [hP]; exact hW) hc` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[mem_singleton]`. Substitute `hx` using the available equality.

Conclude with `⟨hab, hε⟩`.
-/
theorem no_irreducible_at_noncompact_root_shift {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  have hP : phSum {(a, b)} = root a b := by simp [phSum]
  refine dirac_sharp hg hE hU (Ph := {(a, b)}) ?_ (singleton_nonempty _) (by rw [hP]; exact hW) hc
  intro x hx
  rw [mem_singleton] at hx
  subst hx
  exact ⟨hab, hε⟩

end ReciprocityTheory.ChartRestriction.DS.TRGap
