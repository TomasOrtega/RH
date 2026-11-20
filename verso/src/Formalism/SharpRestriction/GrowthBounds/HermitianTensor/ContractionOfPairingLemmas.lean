import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Introduce `p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8`. Establish `hfr` using `R.std.1.frac_O`. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Use `R.charZero` as an intermediate fact. Establish `: Infinite R.Kf` using `inferInstance`.

Establish `hloA : Antitone (lam - wtPQ (mm + 1) P Q)` using `caLo_anti mm ccl P Q lam hlam h0 hl hmid`. Establish `hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q))` using `qsDualWt_anti _ hloA`. Establish `hαZ` using `nuOf_lam_mid mm ccl Q lam hl hmid`. Establish `hβZ` using `nuOf_lo_mid mm ccl P Q lam h0 hl hmid`. Establish `hβ'Z` using `nuOf_lo'_mid mm ccl P Q lam h0 hl hmid`.

Establish `hbd` using `lam_mid_bd mm ccl lam hmid`. Establish `hαA : Antitone (fun j => nuOf lam (midI mm j))` using `fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)`. Establish `hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl`. Introduce `i`. Use `show nuOf lam (midI mm i) ≤ Q + 2 * ccl`.

Use `hαZ i` as an intermediate fact. Use `hbd i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl`. Introduce `i j`.

Use `show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl`. Use `hαZ i` as an intermediate fact. Use `hαZ j` as an intermediate fact. Use `hbd i` as an intermediate fact. Use `hbd j` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩` from `hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8`. Establish `hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) = fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)`. Use function extensionality and compare the values at `j`. Use `show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _`.

Establish `h1` using `hβ'Z j`. Establish `h2` using `hαZ j.rev`. Establish `h3` using `hbd j.rev`. Use linear arithmetic over natural numbers and integers. Rewrite `hInv`, `hInt`, `hu'` using `[hα']`.

Establish `hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q`. Use function extensionality and compare the values at `j`. Use `hαZ j` as an intermediate fact. Use `hβZ j` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b))` using `fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))`. Establish `hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam), ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))), lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P …` using `hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _) (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega) (fu …`. Use `⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv t ht`. Use `hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_` and prove the remaining obligations.

Introduce `x`. Take `⟨v0, hv0, rfl⟩` from `hv`. Take `⟨t0, ht0, rfl⟩` from `ht`. Establish `e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0` using `rfl`. Establish `e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0` using `rfl`.

Rewrite using `[hLC, e1, e2, hSM, hSM]`. Establish `: (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x, L (blockEmb R.Kf true (coeff y.1 (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0))) * blockEmb R.Kf false (coeff y.2 (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0))))) ∈ (algebraMap R.O R.Kf).range`. Use `sum_mem fun y _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_map]`. Conclude with `hInt _ ⟨coeff y.1 (subY R.O mm v0), hSC R.O mm _ v0 hv0 _, rfl⟩ _ ⟨coeff y.2 (subY R.O mm t0), hSC R.O mm _ t0 ht0 _, rfl⟩`.

Conclude with `this`. Establish `hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j))` using `fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)`. Establish `hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl`. Introduce `j`. Use `show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl`.

Use `hβZ j` as an intermediate fact. Use `hbd j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j))` using `fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)`. Establish `hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl`.

Introduce `j`. Use `show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl`. Use `hβ'Z j` as an intermediate fact. Use `hbd j.rev` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)), RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b`. Introduce `b`. Take `⟨f, hf, hfe⟩` from `hu b`. Rewrite `hf` using `[hαβ]`. Take `⟨w0, hw0, rfl⟩` from `hDD R.O mm Q _ hmm hβA f hf`.

Take `⟨s0, hs0, hr0, hrl, hres⟩` from `hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0`. Rewrite `hs0` using `[shapeC_lo mm ccl P Q lam h0 hl]`. Conclude with `⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩`. Establish `hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))), RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a'`. Introduce `a'`.

Take `⟨f, hf, hfe⟩` from `hu' a'`. Take `⟨s0, hs0, hr0, hrl, hres⟩` from `hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf`. Rewrite `hs0` using `[shapeC_lo' mm ccl P Q lam h0 hl]`. Conclude with `⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩`. Use `choose s0 hs0 hs0r hs0l hs0e using hS`.

Use `choose t0 ht0 ht0r ht0l ht0e using hS'`. Use `⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka, fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩` and prove the remaining obligations. Establish `e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl)`. Use function extensionality and compare the values at `j`. Rewrite using `[hαZ j]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hnb, e]`. Conclude with `weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)`. Introduce `a' b F hF`. Establish `e1` using `hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) (hMu p n' R mm hmm P Q F hF)`.

Establish `hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q))` using `hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)`. Establish `hF0sub` using `hMu p n' R mm hmm 0 Q _ hF0`. Establish `e2` using `hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub`. Establish `hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q))` using `dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)`. Establish `hTK : map (algebraMap R.O R.Kf) (t0 a') ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))` using `dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')`.

Establish `hInv' : PhInv R.Kf mm (Q + 2 * ccl) (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L`. Establish `e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) = fun j => nuOf lam (midI mm j)`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.add_apply, nuOf_wt_mid]`. Use `hαZ j` as an intermediate fact.

Use `hβZ j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `hInv`. Establish `hΨmem` using `hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _) (by rw [nuOf_wt_zero, Pi.add_ …`.

Establish `hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q`. Establish `h` using `rowA_hw R.Kf _ _ (hwA 0 Q) 0`. Rewrite `h` using `[nuOf_wt_zero, zero_add]`. Then use the resulting hypothesis. Establish `hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0`. Establish `h` using `rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))`.

Rewrite `h` using `[nuOf_last]`. Then use the resulting hypothesis. Establish `hΨ0` using `rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _ (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b))) (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))`. Establish `hΨl` using `rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _ (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b))) (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))`. Establish `ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl)` using `by omega`. Rewrite `hΨ0` using `[ed]`.

Establish `hΨ` using `hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl`. Establish `hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q`. Unfold `resY`. Rewrite using `[hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]`. Establish `hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1)) (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) * map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) = if a' = b then (p : R.Kf) ^ ka b el …`.

Establish `hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b))`. Rewrite using `[← hs0e b, map_mul, map_pow, detY_map]`. Rewrite using `[hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]`. Establish `hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) = nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q)`. Use `nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q` as an intermediate fact.

Rewrite `this` using `[add_zero, add_comm (2 * ccl) Q]`. Then use the resulting hypothesis. Rewrite `hΨ` using `[hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1]`. Establish `hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0` using `hwNe R.Kf _ _ le_rfl _`. Establish `hΦ` using `mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (by rw [← e2, hΨ]; ring)`. Rewrite using `[e1, hΦ]`.

Use `split_ifs`. Rewrite using `[smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[C_0, zero_mul, mul_zero]`.
-/
theorem contraction_of_pairing_lemmas (hPh : QPh) (hSC : SubCoeffP) (hSM : SubMapP) (hSR : SubRowP) (hLC : LamCoeffP) (hLE : LamEquivP)
    (hLM : LamMulP) (hLV : LamEvalP) (hMem : LamMemP) (hMu : SubMuP) (hTop : TopLineP) (hLift : LiftP) (hDD : DetDivP)
    (hIC : IntCapP) (hHw : HwMulP) : ContractionStandardLattice := by
  classical
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have := R.charZero
  have : Infinite R.Kf := inferInstance
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := qsDualWt_anti _ hloA
  have hαZ := nuOf_lam_mid mm ccl Q lam hl hmid
  have hβZ := nuOf_lo_mid mm ccl P Q lam h0 hl hmid
  have hβ'Z := nuOf_lo'_mid mm ccl P Q lam h0 hl hmid
  have hbd := lam_mid_bd mm ccl lam hmid
  have hαA : Antitone (fun j => nuOf lam (midI mm j)) := fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)
  have hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl := by
    intro i
    show nuOf lam (midI mm i) ≤ Q + 2 * ccl
    have := hαZ i; have := hbd i; omega
  have hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl := by
    intro i j
    show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl
    have := hαZ i; have := hαZ j; have := hbd i; have := hbd j; omega
  obtain ⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩ :=
    hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8
  have hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) =
      fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) := by
    funext j
    show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _
    have h1 := hβ'Z j; have h2 := hαZ j.rev; have h3 := hbd j.rev; omega
  rw [hα'] at hInv hInt hu'
  have hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q := by
    funext j
    have := hαZ j; have := hβZ j; omega
  have hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b)) := fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))
  have hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
      ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) :=
    hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))
      (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _)
      (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
      (fun j => nuOf_wt_mid mm _ _ j) hInv
  refine ⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩
  · intro v hv t ht
    refine hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_
    intro x
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := ht
    have e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0 := rfl
    have e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0 := rfl
    rw [hLC, e1, e2, hSM, hSM]
    have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x,
        L (blockEmb R.Kf true (coeff y.1 (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0))) *
          blockEmb R.Kf false (coeff y.2 (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0))))) ∈
        (algebraMap R.O R.Kf).range := by
      refine sum_mem fun y _ => ?_
      rw [coeff_map, coeff_map]
      exact hInt _ ⟨coeff y.1 (subY R.O mm v0), hSC R.O mm _ v0 hv0 _, rfl⟩ _
        ⟨coeff y.2 (subY R.O mm t0), hSC R.O mm _ t0 ht0 _, rfl⟩
    exact this
  · have hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)
    have hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl
      have := hβZ j; have := hbd j; omega
    have hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)
    have hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl
      have := hβ'Z j; have := hbd j.rev; omega
    have hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧
          map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b := by
      intro b
      obtain ⟨f, hf, hfe⟩ := hu b
      rw [hαβ] at hf
      obtain ⟨w0, hw0, rfl⟩ := hDD R.O mm Q _ hmm hβA f hf
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0
      rw [shapeC_lo mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    have hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a' := by
      intro a'
      obtain ⟨f, hf, hfe⟩ := hu' a'
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf
      rw [shapeC_lo' mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    choose s0 hs0 hs0r hs0l hs0e using hS
    choose t0 ht0 ht0r ht0l ht0e using hS'
    refine ⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka,
      fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩
    · have e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl) := by
        funext j
        rw [hαZ j]; ring
      rw [hnb, e]
      exact weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)
    · intro a' b F hF
      have e1 := hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a'))
        (hMu p n' R mm hmm P Q F hF)
      have hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q)) := hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)
      have hF0sub := hMu p n' R mm hmm 0 Q _ hF0
      have e2 := hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub
      have hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)
      have hTK : map (algebraMap R.O R.Kf) (t0 a') ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')
      have hInv' : PhInv R.Kf mm (Q + 2 * ccl)
          (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j))
          (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L := by
        have e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
            fun j => nuOf lam (midI mm j) := by
          funext j
          rw [Pi.add_apply, nuOf_wt_mid]
          have := hαZ j; have := hβZ j; omega
        rw [e]; exact hInv
      have hΨmem := hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q))
        (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L
        (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _)
        (by rw [nuOf_wt_zero, Pi.add_apply, nuOf_wt_zero, nuOf_lo_zero mm ccl P Q lam h0 hl,
              nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
        (fun j => nuOf_wt_mid mm _ _ j) hInv' _ (dualWeyl_mul R.Kf _ _ _ _ hF0 hSK) _ hTK
      have hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) 0
        rwa [nuOf_wt_zero, zero_add] at h
      have hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0 := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))
        rwa [nuOf_last] at h
      have hΨ0 := rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _
        (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b)))
        (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))
      have hΨl := rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _
        (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b)))
        (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))
      have ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl) := by omega
      rw [ed] at hΨ0
      have hΨ := hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl
      have hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q := by
        unfold resY
        rw [hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]
      have hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1))
          (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) *
            map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) =
          if a' = b then (p : R.Kf) ^ ka b else 0 := by
        have hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b)) := by
          rw [← hs0e b, map_mul, map_pow, detY_map]
        rw [hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]
      have hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) =
          nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q) := by
        have := nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q
        rwa [add_zero, add_comm (2 * ccl) Q] at this
      rw [hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1] at hΨ
      have hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0 := hwNe R.Kf _ _ le_rfl _
      have hΦ := mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)))
        (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))))
        (by rw [← e2, hΨ]; ring)
      rw [e1, hΦ]
      split_ifs
      · rw [smul_eq_C_mul]; ring
      · rw [C_0, zero_mul, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
