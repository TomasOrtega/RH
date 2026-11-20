import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Introduce `p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8`. Take `⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩` from `h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8`. Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Establish `hm1 : 1 ≤ mm + 1` using `by omega`.

Establish `hloA : Antitone (lam - wtPQ (mm + 1) P Q)` using `caLo_anti mm ccl P Q lam hlam h0 hl hmid`. Establish `hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q))` using `cc_dualWt_anti _ hloA`. Establish `hmuA : Antitone (wtPQ (mm + 1) P Q)` using `wtPQ_anti _ _ _ hm1`. Establish `hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))` using `wtPQ_anti _ _ _ hm1`. Establish `hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl))` using `wtPQ_anti _ _ _ hm1`.

Establish `hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ)`. Rewrite using `[lo_val mm ccl P Q lam h0 hl, if_pos rfl]`. Establish `hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ)`. Rewrite using `[lo_val mm ccl P Q lam h0 hl, if_neg (caLast_ne_zero mm), if_pos rfl]`. Establish `hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ)`.

Unfold `dualWt`. Rewrite using `[Fin.rev_last, hlo0]`. Use `⟨abelian₂, hK, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `Λ ⟨g, hg, rfl⟩ v hv t ht`. Rewrite using `[mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]`.

Establish `hv0` using `(mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv`. Establish `ht0` using `(mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht`. Establish `hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam)` using `la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)`. Establish `htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))` using `la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)`. Establish `h3` using `hI _ hv0 _ ht0`.

Rewrite `h3` using `[map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero]`. Establish `he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1))`. Rewrite using `[hl, hloL', wtPQ_last]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h3` using `[he]`. Then use the resulting hypothesis. Introduce `g hg`. Establish `hgi : IsUnit (g⁻¹).det` using `Matrix.isUnit_nonsing_inv_det g hg`. Use `⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))), fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩` and prove the remaining obligations. Introduce `a' b F hF`.

Establish `hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q))` using `dualWeylRowStable R.Kf _ _ _ g F hF`. Establish `e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b)`. Rewrite using `[map_mul, rowAct_cancel_inv g hg, mul_smul_comm]`. Establish `hsK` using `intO_le (O := R.O) _ _ _ (hs b).1`. Establish `hsK'` using `intO_le (O := R.O) _ _ _ (hs' a').1`.

Establish `hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam)`. Establish `h4` using `dualWeyl_mul R.Kf _ _ _ _ hF0 hsK`. Rewrite `h4` using `[← nuOf_add _ _ hmuA hloA]`. Establish `e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam` using `by abel`. Rewrite `h4` using `[e]`. Then use the resulting hypothesis.

Use `show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) * blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _`. Rewrite using `[e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]`. Use `split_ifs`. Rewrite using `[map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_zero, smul_zero]`. Introduce `c hc`. Establish `hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det`. Rewrite using `[Matrix.det_mul]`.

Conclude with `hg.mul (lb_D_det _ 1 c hc)`. Establish `hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl)`. Apply the tactic sequence `have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)`. Establish `h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl`. Unfold `nuOf`.

Rewrite using `[wtPQ_zero, wtPQ_last]`. Use linear arithmetic over natural numbers and integers. Rewrite `h5` using `[h6]`. Then use the resulting hypothesis. Establish `hcz` using `core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]`. Conclude with `hw_int _ _ (nuOf_anti _ hzeA)`. Introduce and unpack `⟨z', hz', he⟩`. Establish `h7` using `(mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'`. Rewrite `h7` using `[wtPQ_last]`.

Apply `hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))` to reduce the goal to its premises. Use `⟨_, h7, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]`. Introduce `b`. Establish `hR : Row0 (s b) (ccl + ccl)` using `by rw [← two_mul]; exact (hs b).2`.

Rewrite using `[mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]`. Conclude with `(hs b).1`. Introduce `a'`. Establish `hR : Row0 (s' a') (ccl + ccl)` using `by rw [← two_mul]; exact (hs' a').2`. Rewrite using `[mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]`.

Conclude with `(hs' a').1`.
-/
theorem cloudOne_of (h : ContractionStandardLattice) : CloudOne := by
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  obtain ⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩ := h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hm1 : 1 ≤ mm + 1 := by omega
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := cc_dualWt_anti _ hloA
  have hmuA : Antitone (wtPQ (mm + 1) P Q) := wtPQ_anti _ _ _ hm1
  have hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, if_pos rfl]
  have hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, if_neg (caLast_ne_zero mm), if_pos rfl]
  have hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    unfold dualWt
    rw [Fin.rev_last, hlo0]
  refine ⟨abelian₂, hK, ?_, ?_⟩
  · rintro Λ ⟨g, hg, rfl⟩ v hv t ht
    rw [mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]
    have hv0 := (mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv
    have ht0 := (mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht
    have hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) :=
      la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)
    have htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
      la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)
    have h3 := hI _ hv0 _ ht0
    rw [map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero] at h3
    have he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) =
        wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1)) := by
      rw [hl, hloL', wtPQ_last]
      push_cast
      ring
    rwa [he] at h3
  · intro g hg
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))),
      fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩
    · intro a' b F hF
      have hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)) :=
        dualWeylRowStable R.Kf _ _ _ g F hF
      have e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b) := by
        rw [map_mul, rowAct_cancel_inv g hg, mul_smul_comm]
      have hsK := intO_le (O := R.O) _ _ _ (hs b).1
      have hsK' := intO_le (O := R.O) _ _ _ (hs' a').1
      have hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) := by
        have h4 := dualWeyl_mul R.Kf _ _ _ _ hF0 hsK
        rw [← nuOf_add _ _ hmuA hloA] at h4
        have e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam := by abel
        rwa [e] at h4
      show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) *
        blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _
      rw [e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]
      split_ifs
      · rw [map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]
        congr 1
        ring
      · rw [map_zero, smul_zero]
    · intro c hc
      have hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det := by
        rw [Matrix.det_mul]
        exact hg.mul (lb_D_det _ 1 c hc)
      have hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl) := by
        have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)
        have h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl := by
          unfold nuOf
          rw [wtPQ_zero, wtPQ_last]
          omega
        rwa [h6] at h5
      have hcz := core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]
        exact hw_int _ _ (nuOf_anti _ hzeA)
      · rintro ⟨z', hz', he⟩
        have h7 := (mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'
        rw [wtPQ_last] at h7
        apply hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))
        refine ⟨_, h7, ?_⟩
        rw [← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]
      · intro b
        have hR : Row0 (s b) (ccl + ccl) := by rw [← two_mul]; exact (hs b).2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]
        exact (hs b).1
      · intro a'
        have hR : Row0 (s' a') (ccl + ccl) := by rw [← two_mul]; exact (hs' a').2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]
        exact (hs' a').1

end Formalism.MainNotions.flipOneThree.Pf

end
