import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormalDegreeZeroMul

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg` using `hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Take `⟨Cg, hCg1, hg2⟩` from `symbol_space_at D CLa Ck Crk Cdeg h26`. Use `⟨max 1 |Cdeg|, max Cg |CLa|, lt_of_lt_of_le one_pos (le_max_left _ _), lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩` and prove the remaining obligations. Introduce `C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis`. Establish `c1 : Cg ≤ C` using `le_trans (le_max_left _ _) hC`.

Establish `c5 : |CLa| ≤ C` using `le_trans (le_max_right _ _) hC`. Establish `hBa` using `hyps_basic (C := C) (by linarith) H`. Establish `ha1 : (1 : ℝ) ≤ a` using `by linarith [hBa.two_le_a]`. Establish `hr2 : 2 ≤ r` using `H.2.1`. Establish `hn : Even n'` using `hSet.1.even`.

Establish `hTT` using `hF.1`. Substitute `hTT` using the available equality. Use `letI : Algebra (WF p n') O := algOfIdent j φ`. Introduce `FsB hFsB Θ hΘ`. Take `⟨-, hdeg⟩` from `hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF E' (fun t ht => (hE' t ht).1)`.

Use `set X : ℝ := Cdeg * (F.TT.card : ℝ) * (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX`. Establish `hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊` using `fun i mm hmm => Nat.le_floor (hdeg (B i) (Submodule.subset_span (hB i)) mm hmm)`. Establish `hXt : X ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a`. Establish `e1 : t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a = t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (r + K) a` using `by rw [hk]`. Rewrite using `[e1]`.

Conclude with `level_lower_bound_terms Cdeg CLa C (max 1 |Cdeg|) (le_max_right _ _) c5 p F.TT.card (orbitWindowCount r de h x) (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (r + K) (min_le_left _ _) (by have := H.1; omega) (by omega) a ha1`. Establish `ht0 : 0 ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a` using `initial_level_nonneg (le_trans (abs_nonneg _) c5) (le_trans zero_le_one (le_max_left _ _)) _ _ _ _ _ _ ha1`. Establish `hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a`. Distinguish the cases in `hX0 : 0 ≤ X`. Conclude with `le_trans (Nat.floor_le hX0) hXt`.

Rewrite using `[Nat.floor_of_nonpos (le_of_lt (not_le.1 hX0))]`. Simplify using `using ht0`. Establish `hw : algebraMap O (KK O) w ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero`. Establish `hbase : ∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) ∈ NDsub (KK O) n' (m + 1) r ⌊X⌋₊`. Introduce `b`.

Rewrite using `[hFsB b]`. Unfold `symB toK`. Rewrite using `[subst_SPtrue w F hF.2.1 hn (by omega) hrk hg]`. Establish `h1` using `nd_mul (nd_map (algebraMap O (KK O)) (nd_rename (n' := n') (R := O) hk (hT b))) (nd_map (algebraMap O (KK O)) (fixed_symbol_normal_degree_zero (R := O) p F hF.2.1 hn (by omega) hrk (cPrime n' r F.TT.card c0 cpp cStar) (p ^ goodG' r de h x)))`. Rewrite `h1` using `[add_zero]`.

Conclude with `h1`. Use `⟨⌊X⌋₊ + F.TT.card * c0, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `f hf mm hmm`.

Rewrite `hmm` using `[subst_eq_Lin]`. Use `mem_NDsub.1 (nd_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) r ⌊X⌋₊ F.TT c0 _ ?_ f hf) mm hmm` and prove the remaining obligations. Introduce `f0 hf0`. Proceed by induction on `hf0 using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, rfl⟩` from `hy`. Rewrite using `[← subst_eq_Lin]`. Conclude with `hbase b`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem restND_of_adm (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : RestND CLa := by
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max 1 |Cdeg|, max Cg |CLa|, lt_of_lt_of_le one_pos (le_max_left _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have c5 : |CLa| ≤ C := le_trans (le_max_right _ _) hC
  have hBa := hyps_basic (C := C) (by linarith) H
  have ha1 : (1 : ℝ) ≤ a := by linarith [hBa.two_le_a]
  have hr2 : 2 ≤ r := H.2.1
  have hn : Even n' := hSet.1.even
  have hTT := hF.1
  subst hTT
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  obtain ⟨-, hdeg⟩ := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF
    E' (fun t ht => (hE' t ht).1)
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hB i)) mm hmm)
  have hXt : X ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    have e1 : t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a =
        t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (r + K) a := by rw [hk]
    rw [e1]
    exact level_lower_bound_terms Cdeg CLa C (max 1 |Cdeg|) (le_max_right _ _) c5 p F.TT.card (orbitWindowCount r de h x)
      (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (r + K) (min_le_left _ _)
      (by have := H.1; omega) (by omega) a ha1
  have ht0 : 0 ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a :=
    initial_level_nonneg (le_trans (abs_nonneg _) c5) (le_trans zero_le_one (le_max_left _ _)) _ _ _ _ _ _ ha1
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    by_cases hX0 : 0 ≤ X
    · exact le_trans (Nat.floor_le hX0) hXt
    · rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hX0))]
      simpa using ht0
  have hw : algebraMap O (KK O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero
  have hbase : ∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) ∈
      NDsub (KK O) n' (m + 1) r ⌊X⌋₊ := by
    intro b
    rw [hFsB b]
    unfold symB toK
    rw [subst_SPtrue w F hF.2.1 hn (by omega) hrk hg]
    have h1 := nd_mul (nd_map (algebraMap O (KK O)) (nd_rename (n' := n') (R := O) hk (hT b)))
      (nd_map (algebraMap O (KK O)) (fixed_symbol_normal_degree_zero (R := O) p F hF.2.1 hn (by omega) hrk
        (cPrime n' r F.TT.card c0 cpp cStar) (p ^ goodG' r de h x)))
    rw [add_zero] at h1
    exact h1
  refine ⟨⌊X⌋₊ + F.TT.card * c0, ?_, ?_⟩
  · push_cast
    linarith
  · intro f hf mm hmm
    rw [subst_eq_Lin] at hmm
    refine mem_NDsub.1 (nd_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) r ⌊X⌋₊ F.TT c0 _
      ?_ f hf) mm hmm
    intro f0 hf0
    induction hf0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [← subst_eq_Lin]
      exact hbase b
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `hA h14b` and use `restXi_of D CLa Ck Crk Cdeg CH CE C6 C18 hN (restND_of_adm D CLa Ck Crk Cdeg hA) hA h14b`.
-/
theorem restXi_of_N (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  fun hA h14b => restXi_of D CLa Ck Crk Cdeg CH CE C6 C18 hN (restND_of_adm D CLa Ck Crk Cdeg hA) hA h14b

end Formalism.MainNotions.TestSideCounting
