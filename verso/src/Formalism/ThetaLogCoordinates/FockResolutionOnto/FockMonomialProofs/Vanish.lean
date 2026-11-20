import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

/- English proof (translation)
The claim follows from `|wt LL K c m| ≤ ∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ) := by unfold wt refine (Finset.abs_sum_le_sum_abs _ _).trans ?_ refine Finset.sum_le_sum fun i _ => ?_ by_cases hi : i = Fin.last K · subst hi simp · rw [if_neg hi] have h2 : ∑ c', m (i, c') = LL.deg …`.
-/
theorem abs_wt_early {K r : ℕ} (LL : Letters (K + 1)) (o : ℕ) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ)
    (hm : MultiDeg (setLast LL o) m) :
    |wt LL K c m| ≤ ∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ) := by
  unfold wt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i = Fin.last K
  · subst hi
    simp
  · rw [if_neg hi]
    have h2 : ∑ c', m (i, c') = LL.deg i := by
      have := hm i
      simpa [setLast, Function.update_of_ne hi] using this
    have h1 : (m (i, c) : ℤ) ≤ (LL.deg i : ℤ) := by
      rw [← h2]
      exact_mod_cast Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    have h0 : (0 : ℤ) ≤ (m (i, c) : ℤ) := Int.natCast_nonneg _
    split_ifs
    · rw [abs_of_nonneg h0]; exact h1
    · rw [abs_neg, abs_of_nonneg h0]; exact h1
    · rw [abs_zero]; exact h0.trans h1

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1` using `ih (by omega)`. Establish `h2` using `h k hk`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem strip_sum (t b : ℕ → ℤ) (n : ℕ) (h : ∀ i, i + 1 < n → t (i + 1) ≤ t i - b i) :
    ∀ k, k < n → ∑ i ∈ range (k + 1), b i ≤ t 0 - (t k - b k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ]
    have h1 := ih (by omega)
    have h2 := h k hk
    linarith

/- English proof (translation)
Introduce `p _ K r _ LL ρ c o hr hρ hv hco`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).mp hne`. Establish `h0ρ : (0 : Fin r) ∈ univ.erase ρ`. Use `Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩` and prove the remaining obligations.

Use `congrArg Fin.val he` as an intermediate fact. Rewrite `this` using `[Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := Pol p r (setLast LL o) ⊓ FreeOf p (Fin.last K, ρ) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) with hS`. Establish `hmem : ∀ z, z ∈ S ↔ (z ∈ Pol p r (setLast LL o) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧ z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)`.

Introduce `z`. Simplify using `only [hS, Submodule.mem_inf]`. Establish `hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL o) (K + 1) s t z ∈ S`. Introduce `s hs t ht z hz`. Rewrite `hz`, the goal using `[hmem]`.

Take `⟨⟨h1, h2⟩, h3⟩` from `hz`. Use `⟨⟨glAct_pol (setLast LL o) (K + 1) s t z h1, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2`. Conclude with `typesLE_glStable LL (K + 1) _ _ s t hs ht z h3`. Take `⟨h, hhS, hh0, th, hhw⟩` from `exists_hwC (setLast LL o) (K + 1) (univ.erase ρ) S (fun z hz => ((hmem z).mp hz).1.1) hstab x hx hx0`.

Rewrite `hhw` using `[hWC_setLast]`. Take `⟨⟨hP, hF⟩, hT⟩` from `(hmem h).mp hhS`. Establish `hth0 : th 0 ≤ c`. Use `first_weight_le_of_support LL (K + 1) (univ.erase ρ) h0ρ ((c : ℤ) : WithTop ℤ) th h hh0 (ycondC_le_supp LL (K + 1) _ _ (typesLE_le_ycondC LL (K + 1) _ h0ρ _ hT)) (Submodule.mem_inf.mp hhw).1` as an intermediate fact. Conclude with `WithTop.coe_le_coe.mp this`.

Take `⟨β, hy, htop, m, hm, hmβ⟩` from `exists_top h hh0`. Establish `hβ : ∀ a, 0 ≤ β a` using `fun a => by rw [← hmβ]; exact Int.natCast_nonneg _`. Establish `hβρ : β ρ = 0`. Rewrite `hF` using `[FreeOf, mem_restrictSupport_iff]`. Use `hF (Finset.mem_coe.mpr hm)` as an intermediate fact.

Simplify using `only [Set.mem_ofPred_eq] at this`. Rewrite using `[← hmβ]`. Simplify using `only [wp, this]`. Both sides reduce to the same expression. Rewrite `hP` using `[Pol, mem_restrictSupport_iff]`.

Establish `hmd : MultiDeg (setLast LL o) m` using `hP (Finset.mem_coe.mpr hm)`. Establish `hsum : ∑ a, β a = o`. Establish `h1` using `hmd (Fin.last K)`. Establish `h2 : (setLast LL o).deg (Fin.last K) = o` using `by simp [setLast]`. Rewrite `h1` using `[h2]`.

Rewrite using `[← hmβ]`. Simplify using `only [wp]`. Conclude with `h1` after adjusting the coercions. Establish `hstrip : ∀ a ∈ univ.erase ρ, ∀ a' ∈ univ.erase ρ, a < a' → th a' ≤ th a - β a` using `fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa`. Establish `hwt : ∀ a ∈ univ.erase ρ, wt LL K a m = th a - β a`.

Introduce `a ha`. Establish `h1` using `eig_supp LL K a _ _ (eJ_cw_diag LL hv _ th h hhw a ha β)`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Use `h1 (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))` and prove the remaining obligations. Rewrite using `[cw, coeff_compL, if_pos hmβ]`.

Conclude with `mem_support_iff.mp hm`. Set `tN : ℕ → ℤ` to `fun i => if h : i < r then th ⟨i, h⟩ else 0`. Set `bN : ℕ → ℤ` to `fun i => if h : i < r then β ⟨i, h⟩ else 0`. Establish `htN : ∀ a : Fin r, tN (a : ℕ) = th a` using `fun a => by simp only [tN, dif_pos a.isLt, Fin.eta]`. Establish `hbN : ∀ a : Fin r, bN (a : ℕ) = β a` using `fun a => by simp only [bN, dif_pos a.isLt, Fin.eta]`.

Establish `hCs : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ`. Introduce `i h`. Use `Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩` and prove the remaining obligations. Use `congrArg Fin.val he` as an intermediate fact. Simplify using `only at this`.

Use linear arithmetic over natural numbers and integers. Establish `hSb : ∑ a ∈ range (r - 1), bN a = o`. Rewrite using `[← sum_erase_last ρ hρ bN, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), hβρ, zero_add]`. Conclude with `Finset.sum_congr rfl fun a _ => hbN a`. Establish `key` using `strip_sum tN bN (r - 1) (by`.

Introduce `i hi`. Establish `h1` using `hstrip ⟨i, by omega⟩ (hCs i (by omega)) ⟨i + 1, by omega⟩ (hCs (i + 1) hi) (by simp only [Fin.lt_def]; omega)`. Establish `h2` using `htN ⟨i, by omega⟩`. Establish `h3` using `htN ⟨i + 1, by omega⟩`. Establish `h4` using `hbN ⟨i, by omega⟩`.

Simplify using `only at h2 h3 h4`. Rewrite using `[h2, h3, h4]`. Conclude with `h1) (r - 2) (by omega)`. Establish `e1 : r - 2 + 1 = r - 1` using `by omega`. Rewrite `key` using `[e1, hSb]`.

Establish `h5` using `htN ⟨r - 2, by omega⟩`. Establish `h6` using `hbN ⟨r - 2, by omega⟩`. Establish `h7` using `htN 0`. Rewrite `h7` using `[Fin.val_zero]`. Simplify using `only at h5 h6`.

Rewrite `key` using `[h5, h6, h7, ← hwt _ (hCs (r - 2) (by omega))]`. Establish `h8` using `(abs_le.mp (abs_wt_early LL o (⟨r - 2, by omega⟩ : Fin r) m hmd)).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem space_vanishing_holds : XVanish := by
  intro p _ K r _ LL ρ c o hr hρ hv hco
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  have h0ρ : (0 : Fin r) ∈ univ.erase ρ := by
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    rw [Fin.val_zero] at this
    omega
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    Pol p r (setLast LL o) ⊓ FreeOf p (Fin.last K, ρ) ⊓
      TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) with hS
  have hmem : ∀ z, z ∈ S ↔ (z ∈ Pol p r (setLast LL o) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧
      z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) := by
    intro z
    simp only [hS, Submodule.mem_inf]
  have hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL o) (K + 1) s t z ∈ S := by
    intro s hs t ht z hz
    rw [hmem] at hz ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    refine ⟨⟨glAct_pol (setLast LL o) (K + 1) s t z h1, ?_⟩, ?_⟩
    · exact glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2
    · exact typesLE_glStable LL (K + 1) _ _ s t hs ht z h3
  obtain ⟨h, hhS, hh0, th, hhw⟩ := exists_hwC (setLast LL o) (K + 1) (univ.erase ρ) S
    (fun z hz => ((hmem z).mp hz).1.1) hstab x hx hx0
  rw [hWC_setLast] at hhw
  obtain ⟨⟨hP, hF⟩, hT⟩ := (hmem h).mp hhS
  have hth0 : th 0 ≤ c := by
    have := first_weight_le_of_support LL (K + 1) (univ.erase ρ) h0ρ ((c : ℤ) : WithTop ℤ) th h hh0
      (ycondC_le_supp LL (K + 1) _ _ (typesLE_le_ycondC LL (K + 1) _ h0ρ _ hT)) (Submodule.mem_inf.mp hhw).1
    exact WithTop.coe_le_coe.mp this
  obtain ⟨β, hy, htop, m, hm, hmβ⟩ := exists_top h hh0
  have hβ : ∀ a, 0 ≤ β a := fun a => by rw [← hmβ]; exact Int.natCast_nonneg _
  have hβρ : β ρ = 0 := by
    rw [FreeOf, mem_restrictSupport_iff] at hF
    have := hF (Finset.mem_coe.mpr hm)
    simp only [Set.mem_ofPred_eq] at this
    rw [← hmβ]; simp only [wp, this]; rfl
  rw [Pol, mem_restrictSupport_iff] at hP
  have hmd : MultiDeg (setLast LL o) m := hP (Finset.mem_coe.mpr hm)
  have hsum : ∑ a, β a = o := by
    have h1 := hmd (Fin.last K)
    have h2 : (setLast LL o).deg (Fin.last K) = o := by simp [setLast]
    rw [h2] at h1
    rw [← hmβ]
    simp only [wp]
    exact_mod_cast h1
  have hstrip : ∀ a ∈ univ.erase ρ, ∀ a' ∈ univ.erase ρ, a < a' → th a' ≤ th a - β a :=
    fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa

  have hwt : ∀ a ∈ univ.erase ρ, wt LL K a m = th a - β a := by
    intro a ha
    have h1 := eig_supp LL K a _ _ (eJ_cw_diag LL hv _ th h hhw a ha β)
    rw [mem_restrictSupport_iff] at h1
    refine h1 (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
    rw [cw, coeff_compL, if_pos hmβ]
    exact mem_support_iff.mp hm

  let tN : ℕ → ℤ := fun i => if h : i < r then th ⟨i, h⟩ else 0
  let bN : ℕ → ℤ := fun i => if h : i < r then β ⟨i, h⟩ else 0
  have htN : ∀ a : Fin r, tN (a : ℕ) = th a := fun a => by simp only [tN, dif_pos a.isLt, Fin.eta]
  have hbN : ∀ a : Fin r, bN (a : ℕ) = β a := fun a => by simp only [bN, dif_pos a.isLt, Fin.eta]
  have hCs : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ := by
    intro i h
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    simp only at this
    omega
  have hSb : ∑ a ∈ range (r - 1), bN a = o := by
    rw [← sum_erase_last ρ hρ bN, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), hβρ, zero_add]
    exact Finset.sum_congr rfl fun a _ => hbN a
  have key := strip_sum tN bN (r - 1) (by
    intro i hi
    have h1 := hstrip ⟨i, by omega⟩ (hCs i (by omega)) ⟨i + 1, by omega⟩ (hCs (i + 1) hi)
      (by simp only [Fin.lt_def]; omega)
    have h2 := htN ⟨i, by omega⟩
    have h3 := htN ⟨i + 1, by omega⟩
    have h4 := hbN ⟨i, by omega⟩
    simp only at h2 h3 h4
    rw [h2, h3, h4]
    exact h1) (r - 2) (by omega)
  have e1 : r - 2 + 1 = r - 1 := by omega
  rw [e1, hSb] at key
  have h5 := htN ⟨r - 2, by omega⟩
  have h6 := hbN ⟨r - 2, by omega⟩
  have h7 := htN 0
  rw [Fin.val_zero] at h7
  simp only at h5 h6
  rw [h5, h6, h7, ← hwt _ (hCs (r - 2) (by omega))] at key
  have h8 := (abs_le.mp (abs_wt_early LL o (⟨r - 2, by omega⟩ : Fin r) m hmd)).1
  linarith

end Formalism.InvariantFactorPaths.L4
