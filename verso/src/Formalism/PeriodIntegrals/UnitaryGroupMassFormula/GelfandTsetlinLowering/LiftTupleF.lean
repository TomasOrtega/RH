import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleE

noncomputable section

namespace PI.WGL.LTF

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

/- English proof (translation)
Unfold `gmin`. Rewrite using `[Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Use `Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`.

Establish `hp` using `IsWeightedHomogeneous.prod Finset.univ (fun p => (X (ρ (σ p), κ p) : MvPolynomial (Fin r × Fin c) ℤ)) (fun p => rowW r c (ρ (σ p), κ p)) (fun p _ => isWeightedHomogeneous_X ℤ _ _)`. Establish `hsum : ∑ p, rowW r c (ρ (σ p), κ p) = ∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)`. Simplify using `only [rowW]`. Conclude with `Equiv.sum_comp σ (fun p => (Pi.single (ρ p) 1 : Fin r → ℕ))`. Rewrite `hp` using `[hsum]`.

Simplify `hp` using `[Matrix.of_apply]`.
-/
theorem gmin_rowW {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    IsWeightedHomogeneous (rowW r c) (gmin ρ κ) (∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)) := by
  classical
  unfold gmin
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun p => (X (ρ (σ p), κ p) : MvPolynomial (Fin r × Fin c) ℤ))
    (fun p => rowW r c (ρ (σ p), κ p)) (fun p _ => isWeightedHomogeneous_X ℤ _ _)
  have hsum : ∑ p, rowW r c (ρ (σ p), κ p) = ∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ) := by
    simp only [rowW]
    exact Equiv.sum_comp σ (fun p => (Pi.single (ρ p) 1 : Fin r → ℕ))
  rw [hsum] at hp
  simpa [Matrix.of_apply] using hp

/- English proof (translation)
Unfold `bideterminant`. Establish `hp` using `IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k)) (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))`. Use `hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Simplify using `only [tupCnt, Finset.sum_apply, Pi.single_apply]`.

Simplify using `[eq_comm]`.
-/
theorem bidet_rowW {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I) := by
  unfold bideterminant
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k))
    (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))
  convert hp using 1
  funext a
  simp only [tupCnt, Finset.sum_apply, Pi.single_apply]
  simp [eq_comm]

def w0r {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Fin N → ℕ :=
  ∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))

/- English proof (translation)
Use `split_ifs`. Conclude with `hf.pow e`. Simplify using `using isWeightedHomogeneous_one ℤ (rowW N N)`.
-/
theorem ite_pow_rowW {N : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ) (w : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f w) (e : ℕ) :
    IsWeightedHomogeneous (rowW N N) (if c then f ^ e else 1) ((if c then e else 0) • w) := by
  split_ifs
  · exact hf.pow e
  · simpa using isWeightedHomogeneous_one ℤ (rowW N N)

/- English proof (translation)
Establish `hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (initW N s)`. Introduce `s hr hc`. Establish `hg : IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ))` using `gmin_rowW (Fin.castLE hr) (Fin.castLE hc)`. Establish `hw : (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) = initW N s`. Use function extensionality and compare the values at `t`.

Simplify using `only [Finset.sum_apply, Pi.single_apply, initW, Fin.ext_iff, Fin.coe_castLE]`. Rewrite using `[show (∑ p : Fin s, if (t : ℕ) = (p : ℕ) then 1 else 0) = ∑ p : Fin s, if (p : ℕ) = t.1 then 1 else 0 from Finset.sum_congr rfl (fun p _ => by simp only [eq_comm])]`. Rewrite using `[sum_ite_val (fun _ => 1) t.1]`. Simplify using the standard rewrite rules. Rewrite `hg` using `[hw]`.

Conclude with `hg`. Unfold `C0 w0r`. Use `IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ => ?_` and prove the remaining obligations. Use `IsWeightedHomogeneous.mul ?_ ?_` and prove the remaining obligations. Conclude with `ite_pow_rowW _ _ _ (hlp _ _ _) _`.

Conclude with `ite_pow_rowW _ _ _ (gmin_rowW (rowsZ h i) (Fin.castLE _)) _`.
-/
theorem constant_weighted_homogeneous {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    IsWeightedHomogeneous (rowW N N) (C0 h lam sg) (w0r h lam sg) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N),
      IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (initW N s) := by
    intro s hr hc
    have hg : IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc)
        (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) := gmin_rowW (Fin.castLE hr) (Fin.castLE hc)
    have hw : (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) = initW N s := by
      funext t
      simp only [Finset.sum_apply, Pi.single_apply, initW, Fin.ext_iff, Fin.coe_castLE]
      rw [show (∑ p : Fin s, if (t : ℕ) = (p : ℕ) then 1 else 0) = ∑ p : Fin s, if (p : ℕ) = t.1 then 1 else 0 from
        Finset.sum_congr rfl (fun p _ => by simp only [eq_comm])]
      rw [sum_ite_val (fun _ => 1) t.1]
      simp
    rw [hw] at hg
    exact hg
  unfold C0 w0r
  refine IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ => ?_
  refine IsWeightedHomogeneous.mul ?_ ?_
  · exact ite_pow_rowW _ _ _ (hlp _ _ _) _
  · exact ite_pow_rowW _ _ _ (gmin_rowW (rowsZ h i) (Fin.castLE _)) _

def wk {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (lifted : Prop) [Decidable lifted] : Fin N → ℕ :=
  (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) +
    (if lifted then (Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 : Fin N → ℕ) else 0)

/- English proof (translation)
Unfold `wk`. Use `split_ifs with hk`. Unfold `lif`. Establish `hg : IsWeightedHomogeneous (rowW N N) (initMinor ℤ (liftRows h ρ) (by have` using `hsz k; omega : sz k + 1 ≤ N)) (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) := gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))`. Establish `hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) = (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1`.

Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[liftRows]`. Rewrite `hg` using `[hw]`. Conclude with `hg`. Unfold `unl`.

Establish `hg : IsWeightedHomogeneous (rowW N N) (initMinor ℤ (eRow h ∘ ρ) (by have` using `hsz k; omega : sz k ≤ N)) (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) := gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))`. Rewrite using `[add_zero]`. Conclude with `hg`.
-/
theorem G_rowW {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) (ρ : Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N)
      (if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (wk h ρ (k ∈ L)) := by
  unfold wk
  split_ifs with hk
  · unfold lif
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (liftRows h ρ) (by have := hsz k; omega : sz k + 1 ≤ N))
        (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) :=
      gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))
    have hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) =
        (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 := by
      rw [Fin.sum_univ_castSucc]
      simp [liftRows]
    rw [hw] at hg
    exact hg
  · unfold unl
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (eRow h ∘ ρ) (by have := hsz k; omega : sz k ≤ N))
        (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) :=
      gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))
    rw [add_zero]
    exact hg

/- English proof (translation)
Unfold `w0r`. Establish `key : ∀ i : Fin n, (((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) + (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ))) ⟨av, hav⟩) = (if i.1 = n - 1 then (aa h lam sg i).toNat * (if av < n then 1 else 0) else …`. Introduce `i`. Establish `hi2` using `i.2`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Use `congr 1`. Distinguish the cases in `hi : i.1 + 1 = n`. Rewrite using `[if_pos hi, if_pos (by omega)]`. Simplify using `only [initW, hi]`. Rewrite using `[if_neg hi, if_neg (by omega), zero_mul]`.

Distinguish the cases in `hi : i.1 = 0`. Rewrite using `[if_pos hi, if_pos hi]`. Use `congr 1`. Rewrite using `[Finset.sum_apply]`. Establish `e : ∀ p : Fin (i.1 + 1), (Pi.single (rowsZ h i p) 1 : Fin N → ℕ) ⟨av, hav⟩ = if av = n then 1 else 0`.

Introduce `p`. Establish `hp` using `p.2`. Establish `hr : rowsZ h i p = ⟨N - 1, by omega⟩`. Simplify using `only [rowsZ]`. Rewrite using `[if_pos (by omega)]`.

Rewrite using `[hr, Pi.single_apply]`. Distinguish the cases in `hav' : av = n`. Rewrite using `[if_pos (Fin.ext (by simp only; omega)), if_pos hav']`. Rewrite using `[if_neg (fun he => hav' (by have := congrArg Fin.val he; simp only at this; omega)), if_neg hav']`. Rewrite using `[Finset.sum_congr rfl (fun p _ => e p), Finset.sum_const, Finset.card_univ, Fintype.card_fin, hi, smul_eq_mul, zero_add, one_mul]`.

Rewrite using `[if_neg hi, if_neg hi, zero_mul]`. Rewrite using `[Finset.sum_apply, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, sum_ite_val, sum_ite_val]`.
-/
theorem constant_weight_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (av : ℕ) (hav : av < N) :
    w0r h lam sg ⟨av, hav⟩ =
      (if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * (if av < n then 1 else 0) else 0) +
      (if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * (if av = n then 1 else 0) else 0) := by
  unfold w0r
  have key : ∀ i : Fin n, (((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
      (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))
        ⟨av, hav⟩) =
      (if i.1 = n - 1 then (aa h lam sg i).toNat * (if av < n then 1 else 0) else 0) +
      (if i.1 = 0 then (bb h lam sg i).toNat * (if av = n then 1 else 0) else 0) := by
    intro i
    have hi2 := i.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · by_cases hi : i.1 + 1 = n
      · rw [if_pos hi, if_pos (by omega)]
        simp only [initW, hi]
      · rw [if_neg hi, if_neg (by omega), zero_mul]
    · by_cases hi : i.1 = 0
      · rw [if_pos hi, if_pos hi]
        congr 1
        rw [Finset.sum_apply]
        have e : ∀ p : Fin (i.1 + 1), (Pi.single (rowsZ h i p) 1 : Fin N → ℕ) ⟨av, hav⟩ =
            if av = n then 1 else 0 := by
          intro p
          have hp := p.2
          have hr : rowsZ h i p = ⟨N - 1, by omega⟩ := by
            simp only [rowsZ]
            rw [if_pos (by omega)]
          rw [hr, Pi.single_apply]
          by_cases hav' : av = n
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hav']
          · rw [if_neg (fun he => hav' (by have := congrArg Fin.val he; simp only at this; omega)), if_neg hav']
        rw [Finset.sum_congr rfl (fun p _ => e p), Finset.sum_const, Finset.card_univ, Fintype.card_fin, hi,
          smul_eq_mul, zero_add, one_mul]
      · rw [if_neg hi, if_neg hi, zero_mul]
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, sum_ite_val,
    sum_ite_val]

/- English proof (translation)
Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]`. Rewrite using `[Finset.sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hL.2 i]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `[Finset.mem_filter]`. Introduce `k hk`. Rewrite using `[Finset.mem_coe, Finset.mem_range]`. Use `replace hk := Finset.mem_coe.mp hk`.

Break down `sz_lt sg sz hsz hshape k with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))`.
-/
theorem cardL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) :
    L.card = ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL.2 i]
    congr 1
    ext k
    simp [Finset.mem_filter]
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range]
    replace hk := Finset.mem_coe.mp hk
    rcases sz_lt sg sz hsz hshape k with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))

/- English proof (translation)
Substitute `h` using the available equality. Establish `hb : ∀ i : Fin n, (((bb rfl lam sg i).toNat : ℕ) : ℤ) = lam.w (Fin.castSucc i) - sg.w i` using `fun i => b_val rfl lam sg hI i.1 i.2`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_sub_distrib]`. Unfold `degZ wsum`.

Rewrite using `[Fin.sum_univ_castSucc (f := lam.w), lam_detShift rfl lam, show (Fin.last n) = (⟨n, by omega⟩ : Fin (n + 1)) from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sumB {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    ((∑ i : Fin n, (bb h lam sg i).toNat : ℕ) : ℤ) = degZ lam sg - lam.detShift := by
  subst h
  have hb : ∀ i : Fin n, (((bb rfl lam sg i).toNat : ℕ) : ℤ) = lam.w (Fin.castSucc i) - sg.w i :=
    fun i => b_val rfl lam sg hI i.1 i.2
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_sub_distrib]
  unfold degZ wsum
  rw [Fin.sum_univ_castSucc (f := lam.w), lam_detShift rfl lam,
    show (Fin.last n) = (⟨n, by omega⟩ : Fin (n + 1)) from rfl]
  ring

end PI.WGL.LTF
