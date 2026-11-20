import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM

noncomputable section

namespace PI.WGL.LTB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

/- English proof (translation)
Unfold `initMinor`. Use `first`. Consider the case `(rw [zsmul_eq_mul, ← Matrix.det_permute]; rfl)`. Consider the case `(rw [← Units.smul_def, ← Matrix.det_permute]; rfl)`.
-/
theorem initMinor_perm {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (σ : Equiv.Perm (Fin s)) :
    initMinor R (n := m) (I ∘ σ) hs = (Equiv.Perm.sign σ : ℤ) • initMinor R (n := m) I hs := by
  unfold initMinor
  first
  | (rw [zsmul_eq_mul, ← Matrix.det_permute]; rfl)
  | (rw [← Units.smul_def, ← Matrix.det_permute]; rfl)

/- English proof (translation)
Unfold `initMinor`. Unfold `Function.Injective at hI`. Use `push_neg at hI`. Take `⟨i, j, hij, hne⟩` from `hI`. Conclude with `Matrix.det_zero_of_row_eq hne (by ext q; simp [hij])`.
-/
theorem initMinor_not_inj {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (hI : ¬ Function.Injective I) : initMinor R (n := m) I hs = 0 := by
  unfold initMinor
  unfold Function.Injective at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq hne (by ext q; simp [hij])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem initMinor_std {R : Type*} [CommRing R] {r m s : ℕ} (hr : s ≤ r) (hs : s ≤ m) :
    initMinor R (n := m) (fun p : Fin s => (⟨p.1, lt_of_lt_of_le p.2 hr⟩ : Fin r)) hs = lpMinor R s hr hs := by
  rfl

/- English proof (translation)
Unfold `unl`. Conclude with `initMinor_perm (eRow h ∘ ρ) hm σ`.
-/
theorem unl_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) (σ : Equiv.Perm (Fin m)) :
    unl h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • unl h ρ hm := by
  unfold unl
  exact initMinor_perm (eRow h ∘ ρ) hm σ

/- English proof (translation)
Use function extensionality and compare the values at `p`. Proceed by induction on `p using Fin.lastCases with`. Consider the case `last`. Establish `hnot : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1))`. Introduce and unpack `⟨y, hy⟩`.

Establish `h1 : y.val = m`. Use `congrArg Fin.val hy` as an intermediate fact. Conclude with `this`. Establish `h2` using `y.2`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Function.comp_apply]`. Use `first`. Consider the case `rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hnot]`. Consider the case `rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnot]`. Consider the case `rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range hnot]`.

Consider the case `rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range hnot]`. Simplify using `[liftRows]`. Consider the case `cast i`. Rewrite using `[Function.comp_apply]`. Establish `e` using `Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i`.

Rewrite using `[show Fin.castSucc i = (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i from rfl, e]`. Simplify using `[liftRows]`.
-/
theorem liftRows_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) :
    liftRows h (ρ ∘ σ) = liftRows h ρ ∘ (σ.viaFintypeEmbedding Fin.castSuccEmb) := by
  funext p
  induction p using Fin.lastCases with
  | last =>
    have hnot : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
      rintro ⟨y, hy⟩
      have h1 : y.val = m := by
        have := congrArg Fin.val hy
        exact this
      have h2 := y.2
      omega
    rw [Function.comp_apply]
    first
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range hnot]
    simp [liftRows]
  | cast i =>
    rw [Function.comp_apply]
    have e := Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i
    rw [show Fin.castSucc i = (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i from rfl, e]
    simp [liftRows]

/- English proof (translation)
Unfold `lif`. Rewrite using `[liftRows_perm, initMinor_perm]`. Rewrite using `[show Equiv.Perm.sign (σ.viaFintypeEmbedding Fin.castSuccEmb) = Equiv.Perm.sign σ from Equiv.Perm.sign_extendDomain σ _]`.
-/
theorem lif_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (σ : Equiv.Perm (Fin m)) :
    lif h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • lif h ρ hm := by
  unfold lif
  rw [liftRows_perm, initMinor_perm]
  rw [show Equiv.Perm.sign (σ.viaFintypeEmbedding Fin.castSuccEmb) = Equiv.Perm.sign σ from
    Equiv.Perm.sign_extendDomain σ _]

/- English proof (translation)
Unfold `unl`. Conclude with `initMinor_not_inj _ hm (fun hinj => hρ hinj.of_comp)`.
-/
theorem unl_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N)
    (hρ : ¬ Function.Injective ρ) : unl h ρ hm = 0 := by
  unfold unl
  exact initMinor_not_inj _ hm (fun hinj => hρ hinj.of_comp)

/- English proof (translation)
Unfold `lif`. Use `initMinor_not_inj _ hm (fun hinj => hρ (fun a b hab => ?_))` and prove the remaining obligations. Establish `h2 : liftRows h ρ (Fin.castSucc a) = liftRows h ρ (Fin.castSucc b)`. Simplify using `[liftRows, hab]`. Conclude with `Fin.castSucc_inj.mp (hinj h2)`.
-/
theorem lif_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (hρ : ¬ Function.Injective ρ) : lif h ρ hm = 0 := by
  unfold lif
  refine initMinor_not_inj _ hm (fun hinj => hρ (fun a b hab => ?_))
  have h2 : liftRows h ρ (Fin.castSucc a) = liftRows h ρ (Fin.castSucc b) := by
    simp [liftRows, hab]
  exact Fin.castSucc_inj.mp (hinj h2)

/- English proof (translation)
Unfold `tupCnt`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := J k) (t := Finset.univ.filter fun a : Fin n => a.1 < t) (by intro p hp; simpa using hp)]`. Use `Finset.sum_congr rfl (fun a ha => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun hp => hp.2`. Introduce `hp`. Conclude with `⟨by rw [hp]; exact ha, hp⟩`.
-/
theorem sum_cnt_lt {n K : ℕ} {sz : Fin K → ℕ} (J : ∀ k, Fin (sz k) → Fin n) (t : ℕ) :
    ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), tupCnt J a := by
  unfold tupCnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := J k) (t := Finset.univ.filter fun a : Fin n => a.1 < t)
    (by intro p hp; simpa using hp)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨by rw [hp]; exact ha, hp⟩

/- English proof (translation)
Establish `e : (Finset.univ.filter fun a : Fin n => a.1 < c).card = (Finset.range c).card`. Apply `Finset.card_bij (fun a _ => a.1)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `using ha`. Introduce `a _ b _ hab`.

Conclude with `Fin.ext hab`. Introduce `b hb`. Establish `hb' : b < c` using `by simpa using hb`. Conclude with `⟨⟨b, by omega⟩, by simpa using hb', rfl⟩`. Rewrite using `[e, Finset.card_range]`.
-/
private theorem card_filter_fin_val_lt' {n c : ℕ} (hc : c ≤ n) :
    (Finset.univ.filter fun a : Fin n => a.1 < c).card = c := by
  have e : (Finset.univ.filter fun a : Fin n => a.1 < c).card = (Finset.range c).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simpa using ha
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      have hb' : b < c := by simpa using hb
      exact ⟨⟨b, by omega⟩, by simpa using hb', rfl⟩
  rw [e, Finset.card_range]

/- English proof (translation)
Unfold `shapeDeg`. Establish `e : ∀ k : Fin K, min t (sz k) = (Finset.univ.filter fun a : Fin n => a.1 < t ∧ a.1 < sz k).card`. Introduce `k`. Rewrite using `[← card_filter_fin_val_lt' (n := n) (c := min t (sz k)) (le_trans (min_le_left _ _) ht)]`. Apply `congrArg Finset.card` to reduce the goal to its premises.

Use extensionality with `a`. Simplify using `[lt_min_iff]`. Simplify using `only [e]`. Simplify using `only [Finset.card_eq_sum_ones, Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases ha : a.1 < t <;> simp [ha]`.
-/
theorem sum_shape_lt {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (t : ℕ) (ht : t ≤ n) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), shapeDeg sz a = ∑ k, min t (sz k) := by
  unfold shapeDeg
  have e : ∀ k : Fin K, min t (sz k) = (Finset.univ.filter fun a : Fin n => a.1 < t ∧ a.1 < sz k).card := by
    intro k
    rw [← card_filter_fin_val_lt' (n := n) (c := min t (sz k)) (le_trans (min_le_left _ _) ht)]
    apply congrArg Finset.card
    ext a
    simp [lt_min_iff]
  simp only [e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a.1 < t <;> simp [ha]

/- English proof (translation)
Introduce `k p`. Establish `key : ∀ t, t ≤ n → ∀ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = min t (sz k)`. Introduce `t ht`. Establish `hle : ∀ k ∈ Finset.univ, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card ≤ min t (sz k)`. Introduce `k _`.

Use `le_min ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `(Finset.card_filter_le _ _).trans (by simp)`. Establish `hsum : ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = ∑ k, min t (sz k)`. Rewrite using `[sum_cnt_lt J t, hc, sum_shape_lt sz hsz t ht]`.

Conclude with `fun k => (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_univ _)`. Establish `h1` using `key (sz k) (hsz k) k`. Rewrite `h1` using `[min_self]`. Establish `h2 : (Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k) = Finset.univ`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `h3 : p ∈ Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k`. Rewrite using `[h2]`. Conclude with `Finset.mem_univ _`.

Simplify using `using h3`.
-/
theorem top_entries {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hc : tupCnt J = shapeDeg sz) : ∀ k p, (J k p).1 < sz k := by
  intro k p
  have key : ∀ t, t ≤ n → ∀ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = min t (sz k) := by
    intro t ht
    have hle : ∀ k ∈ Finset.univ, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card ≤ min t (sz k) := by
      intro k _
      refine le_min ?_ ?_
      · calc _ ≤ (Finset.univ.filter fun a : Fin n => a.1 < t).card :=
              Finset.card_le_card_of_injOn (J k) (by intro p hp; simpa using hp)
                (by intro a _ b _ hab; exact hinj k hab)
          _ = t := card_filter_fin_val_lt' ht
      · exact (Finset.card_filter_le _ _).trans (by simp)
    have hsum : ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = ∑ k, min t (sz k) := by
      rw [sum_cnt_lt J t, hc, sum_shape_lt sz hsz t ht]
    exact fun k => (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_univ _)
  have h1 := key (sz k) (hsz k) k
  rw [min_self] at h1
  have h2 : (Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h1]
    simp
  have h3 : p ∈ Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k := by
    rw [h2]
    exact Finset.mem_univ _
  simpa using h3

/- English proof (translation)
Introduce `k`. Set `f : Fin (sz k) → Fin (sz k)` to `fun p => ⟨(J k p).1, hlt k p⟩`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Apply `hinj k` to reduce the goal to its premises.

Conclude with `Fin.ext (by simpa [f] using congrArg Fin.val hab)`. Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Conclude with `Fin.ext rfl`.
-/
theorem top_perm {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hlt : ∀ k p, (J k p).1 < sz k) :
    ∀ k, ∃ σ : Equiv.Perm (Fin (sz k)), J k = stdT sz hsz k ∘ σ := by
  intro k
  let f : Fin (sz k) → Fin (sz k) := fun p => ⟨(J k p).1, hlt k p⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj k
    exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  funext p
  exact Fin.ext rfl

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Finset.card_eq_one]`. Use `⟨⟨a.1, h⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `p`. Simplify using `[Fin.ext_iff]`.

Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `p _ hp`. Conclude with `h (by have := p.2; omega)`.
-/
theorem card_eq_val {m n : ℕ} (a : Fin n) :
    (Finset.univ.filter fun p : Fin m => p.1 = a.1).card = if a.1 < m then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨a.1, h⟩, ?_⟩
    ext p
    simp [Fin.ext_iff]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    exact h (by have := p.2; omega)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Unfold `tupCnt shapeDeg`. Rewrite using `[Finset.card_filter (fun k : Fin K => a.1 < sz k)]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← card_eq_val (m := sz k) a]`.

Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `p`. Simplify using `[stdT, Fin.ext_iff]`.
-/
theorem tupCnt_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : tupCnt (stdT sz hsz) = shapeDeg sz := by
  funext a
  unfold tupCnt shapeDeg
  rw [Finset.card_filter (fun k : Fin K => a.1 < sz k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← card_eq_val (m := sz k) a]
  apply congrArg Finset.card
  ext p
  simp [stdT, Fin.ext_iff]

/- English proof (translation)
Rewrite using `[Finset.prod_comp F sz]`. Apply `Finset.prod_subset` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_image]`. Take `⟨k, hk, rfl⟩` from `hy`.

Conclude with `Finset.mem_range.mpr (hb k hk)`. Introduce `y _ hy`. Rewrite `hy` using `[Finset.mem_image]`. Establish `e : s.filter (fun k => sz k = y) = ∅`. Rewrite using `[Finset.filter_eq_empty_iff]`.

Introduce `k hk hky`. Conclude with `hy ⟨k, hk, hky⟩`. Rewrite using `[e, Finset.card_empty, pow_zero]`.
-/
theorem prod_sz {M : Type*} [CommMonoid M] {K : ℕ} (sz : Fin K → ℕ) (s : Finset (Fin K)) (bnd : ℕ)
    (hb : ∀ k ∈ s, sz k < bnd) (F : ℕ → M) :
    ∏ k ∈ s, F (sz k) = ∏ y ∈ Finset.range bnd, F y ^ (s.filter fun k => sz k = y).card := by
  rw [Finset.prod_comp F sz]
  apply Finset.prod_subset
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Finset.mem_range.mpr (hb k hk)
  · intro y _ hy
    rw [Finset.mem_image] at hy
    have e : s.filter (fun k => sz k = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk hky
      exact hy ⟨k, hk, hky⟩
    rw [e, Finset.card_empty, pow_zero]

/- English proof (translation)
Unfold `nuNext shapeDeg`. Use `split_ifs with h`. Apply the tactic sequence `try simp only [Fin.val_mk]`. Establish `hsub : (Finset.univ.filter fun k : Fin K => s.1 + 1 < sz k) ⊆ Finset.univ.filter fun k : Fin K => s.1 < sz k`. Introduce `k hk`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Use linear arithmetic over natural numbers and integers. Use `first`. Consider the case `rw [← Finset.card_sdiff_of_subset hsub]`. Consider the case `rw [← Finset.card_sdiff hsub]`.

Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.sub_zero]`.

Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Establish `h1` using `hsz k`. Establish `h2` using `s.2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem count_succ {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (s : Fin n) :
    (Finset.univ.filter fun k => sz k = s.1 + 1).card = shapeDeg sz s - nuNext (shapeDeg sz) s := by
  unfold nuNext shapeDeg
  split_ifs with h
  · try simp only [Fin.val_mk]
    have hsub : (Finset.univ.filter fun k : Fin K => s.1 + 1 < sz k) ⊆ Finset.univ.filter fun k : Fin K => s.1 < sz k := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    first
    | rw [← Finset.card_sdiff_of_subset hsub]
    | rw [← Finset.card_sdiff hsub]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  · rw [Nat.sub_zero]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hsz k
    have h2 := s.2
    omega

/- English proof (translation)
Substitute `hsh` using the available equality. Unfold `bideterminant hw`. Set `F : ℕ → MvPolynomial (Fin n × Fin n) ℤ` to `fun y => if hy : y ≤ n then lpMinor ℤ y hy hy else 1`. Establish `h1 : ∀ k, initMinor ℤ (stdT sz hsz k) (hsz k) = F (sz k)`. Introduce `k`.

Establish `e : F (sz k) = lpMinor ℤ (sz k) (hsz k) (hsz k)` using `dif_pos (hsz k)`. Rewrite using `[e]`. Conclude with `initMinor_std (hsz k) (hsz k)`. Simplify using `only [h1]`. Rewrite using `[prod_sz sz Finset.univ (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) F, Finset.prod_range_succ']`.

Establish `h0 : F 0 = 1`. Establish `e : F 0 = lpMinor ℤ 0 (Nat.zero_le n) (Nat.zero_le n)` using `dif_pos (Nat.zero_le n)`. Rewrite using `[e]`. Simplify using `[lpMinor]`. Rewrite using `[h0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range]`.

Use `Finset.prod_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[count_succ sz hsz s]`. Establish `e : F (s.1 + 1) = lpMinor ℤ (s.1 + 1) (by have` using `s.2; omega) (by have := s.2; omega) := dif_pos (by have := s.2; omega)`. Rewrite using `[e]`.
-/
theorem bidet_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (ν : Fin n → ℕ) (hsh : shapeDeg sz = ν) :
    bideterminant ℤ sz hsz (stdT sz hsz) = hw ℤ (r := n) le_rfl ν := by
  subst hsh
  unfold bideterminant hw
  let F : ℕ → MvPolynomial (Fin n × Fin n) ℤ := fun y => if hy : y ≤ n then lpMinor ℤ y hy hy else 1
  have h1 : ∀ k, initMinor ℤ (stdT sz hsz k) (hsz k) = F (sz k) := by
    intro k
    have e : F (sz k) = lpMinor ℤ (sz k) (hsz k) (hsz k) := dif_pos (hsz k)
    rw [e]
    exact initMinor_std (hsz k) (hsz k)
  simp only [h1]
  rw [prod_sz sz Finset.univ (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) F, Finset.prod_range_succ']
  have h0 : F 0 = 1 := by
    have e : F 0 = lpMinor ℤ 0 (Nat.zero_le n) (Nat.zero_le n) := dif_pos (Nat.zero_le n)
    rw [e]
    simp [lpMinor]
  rw [h0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [count_succ sz hsz s]
  have e : F (s.1 + 1) = lpMinor ℤ (s.1 + 1) (by have := s.2; omega) (by have := s.2; omega) :=
    dif_pos (by have := s.2; omega)
  rw [e]

/- English proof (translation)
Simplify using `only [zsmul_eq_mul, Finset.prod_mul_distrib, Int.cast_prod]`.
-/
theorem prod_zsmul' {R : Type*} [CommRing R] {K : ℕ} (a : Fin K → ℤ) (x : Fin K → R) :
    ∏ k, (a k • x k) = (∏ k, a k) • ∏ k, x k := by
  simp only [zsmul_eq_mul, Finset.prod_mul_distrib, Int.cast_prod]

/- English proof (translation)
Simplify using `[Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, hn]`.
-/
theorem natW_last {n : ℕ} (sg : DomWeight n) (hn : 0 < n) : sg.natW ⟨n - 1, by omega⟩ = 0 := by
  simp [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, hn]

/- English proof (translation)
Establish `hn : 0 < n` using `lt_of_le_of_lt (Nat.zero_le _) i.2`. Establish `hle : sg.detShift ≤ sg.w i`. Unfold `Formalism.BasicNotions.DomWeight.detShift`. Rewrite using `[dif_pos hn]`. Conclude with `sg.anti (Fin.le_iff_val_le_val.mpr (by show i.1 ≤ n - 1; have := i.2; omega))`.

Simplify using `only [Formalism.BasicNotions.DomWeight.natW]`. Rewrite using `[Int.toNat_of_nonneg (sub_nonneg.mpr hle)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natW_add {n : ℕ} (sg : DomWeight n) (i : Fin n) : ((sg.natW i : ℕ) : ℤ) + sg.detShift = sg.w i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hle : sg.detShift ≤ sg.w i := by
    unfold Formalism.BasicNotions.DomWeight.detShift
    rw [dif_pos hn]
    exact sg.anti (Fin.le_iff_val_le_val.mpr (by show i.1 ≤ n - 1; have := i.2; omega))
  simp only [Formalism.BasicNotions.DomWeight.natW]
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
  ring

/- English proof (translation)
Establish `hn : 0 < n` using `lt_of_lt_of_le hk (hsz k)`. Assume the negation of the conclusion as `hcon`. Establish `heq : sz k = n` using `le_antisymm (hsz k) (not_lt.mp hcon)`. Establish `h1` using `congrFun hsh ⟨n - 1, by omega⟩`. Rewrite `h1` using `[natW_last sg hn]`.

Unfold `shapeDeg at h1`. Rewrite `h1` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `h1 (Finset.mem_univ k) (by simp; omega)`.
-/
theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (k : Fin K) (hk : 0 < sz k) : sz k < n := by
  have hn : 0 < n := lt_of_lt_of_le hk (hsz k)
  by_contra hcon
  have heq : sz k = n := le_antisymm (hsz k) (not_lt.mp hcon)
  have h1 := congrFun hsh ⟨n - 1, by omega⟩
  rw [natW_last sg hn] at h1
  unfold shapeDeg at h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ k) (by simp; omega)

/- English proof (translation)
Unfold `lif`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `[liftRows, rowsZ, stdT, eRow]`. Establish `hp` using `p.2`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem lif_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hk : sz k < n) (hm : sz k + 1 ≤ N) :
    lif h (stdT sz hsz k) hm = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk⟩) hm := by
  unfold lif
  congr 1
  funext p
  simp [liftRows, rowsZ, stdT, eRow]
  have hp := p.2
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `unl`. Conclude with `initMinor_std hm hm`.
-/
theorem unl_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hm : sz k ≤ N) : unl h (stdT sz hsz k) hm = lpMinor ℤ (r := N) (n := N) (sz k) hm hm := by
  unfold unl
  exact initMinor_std hm hm

/- English proof (translation)
Unfold `Interlace at hI`. Unfold `GoodL at hL`. Establish `hs0` using `s.2`. Establish `e1 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => k ∈ L) = Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1`. Use extensionality with `k`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `and_comm`. Establish `e2 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => ¬ k ∈ L) = Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `and_comm`. Establish `htot : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card + (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card = (Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).card`. Rewrite using `[← e1, ← e2]`. Use `first`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`.

Consider the case `exact Finset.card_filter_add_card_filter_not _`. Establish `hc` using `count_succ sz hsz s`. Rewrite `hc` using `[hsh]`. Unfold `nuNext at hc`. Use `split_ifs with hs`.

Rewrite `hc` using `[dif_neg (show ¬ (s.1 + 1 < n) by omega)]`. Establish `hlast : sg.natW s = 0`. Establish `e : s = ⟨n - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e]`. Conclude with `natW_last sg (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `hs' : s.1 + 1 < n` using `by omega`. Establish `hL1 : s.1 + 1 < N` using `by omega`. Rewrite `hc` using `[dif_pos hs']`. Establish `hb : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card = (lam.w ⟨s.1 + 1, hL1⟩ - sg.w ⟨s.1 + 1, hs'⟩).toNat`.

Use `hL.2 ⟨s.1 + 1, hs'⟩` as an intermediate fact. Rewrite `this` using `[if_neg (show ¬ (((⟨s.1 + 1, hs'⟩ : Fin n) : ℕ) = 0) by simp)]`. Conclude with `this`. Establish `hI1 : lam.w ⟨s.1 + 1, hL1⟩ ≤ sg.w s` using `(hI s).2`. Establish `hI2 : sg.w ⟨s.1 + 1, hs'⟩ ≤ lam.w ⟨s.1 + 1, hL1⟩` using `(hI ⟨s.1 + 1, hs'⟩).1`.

Establish `ha : ((sg.natW s : ℕ) : ℤ) + sg.detShift = sg.w s` using `natW_add sg s`. Establish `hb2 : ((sg.natW ⟨s.1 + 1, hs'⟩ : ℕ) : ℤ) + sg.detShift = sg.w ⟨s.1 + 1, hs'⟩` using `natW_add sg _`. Establish `hX` using `Int.toNat_of_nonneg (sub_nonneg.mpr hI1)`. Establish `hY` using `Int.toNat_of_nonneg (sub_nonneg.mpr hI2)`. Use `show _ = (sg.w s - lam.w ⟨s.1 + 1, hL1⟩).toNat`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem card_filter_not_mem_sz_eq_succ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) (s : Fin n) :
    (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      if s.1 + 1 = n then 0 else (aa h lam sg s).toNat := by
  unfold Interlace at hI
  unfold GoodL at hL
  have hs0 := s.2
  have e1 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => k ∈ L) =
      Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have e2 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => ¬ k ∈ L) =
      Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have htot : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card +
      (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      (Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).card := by
    rw [← e1, ← e2]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_not _
  have hc := count_succ sz hsz s
  rw [hsh] at hc
  unfold nuNext at hc
  split_ifs with hs
  · rw [dif_neg (show ¬ (s.1 + 1 < n) by omega)] at hc
    have hlast : sg.natW s = 0 := by
      have e : s = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      exact natW_last sg (by omega)
    omega
  · have hs' : s.1 + 1 < n := by omega
    have hL1 : s.1 + 1 < N := by omega
    rw [dif_pos hs'] at hc
    have hb : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card =
        (lam.w ⟨s.1 + 1, hL1⟩ - sg.w ⟨s.1 + 1, hs'⟩).toNat := by
      have := hL.2 ⟨s.1 + 1, hs'⟩
      rw [if_neg (show ¬ (((⟨s.1 + 1, hs'⟩ : Fin n) : ℕ) = 0) by simp)] at this
      exact this
    have hI1 : lam.w ⟨s.1 + 1, hL1⟩ ≤ sg.w s := (hI s).2
    have hI2 : sg.w ⟨s.1 + 1, hs'⟩ ≤ lam.w ⟨s.1 + 1, hL1⟩ := (hI ⟨s.1 + 1, hs'⟩).1
    have ha : ((sg.natW s : ℕ) : ℤ) + sg.detShift = sg.w s := natW_add sg s
    have hb2 : ((sg.natW ⟨s.1 + 1, hs'⟩ : ℕ) : ℤ) + sg.detShift = sg.w ⟨s.1 + 1, hs'⟩ := natW_add sg _
    have hX := Int.toNat_of_nonneg (sub_nonneg.mpr hI1)
    have hY := Int.toNat_of_nonneg (sub_nonneg.mpr hI2)
    show _ = (sg.w s - lam.w ⟨s.1 + 1, hL1⟩).toNat
    omega

/- English proof (translation)
Establish `hL'` using `hL`. Unfold `GoodL at hL'`. Establish `hN : ∀ k, sz k + 1 ≤ N` using `fun k => by have := hsz k; omega`. Unfold `Mlift xi`. Rewrite using `[Finset.prod_ite]`.

Set `A : ℕ → MvPolynomial (Fin N × Fin N) ℤ` to `fun j => if hj : j < n then initMinor ℤ (n := N) (rowsZ h ⟨j, hj⟩) (by show j + 1 ≤ N; omega) else 1`. Set `B : ℕ → MvPolynomial (Fin N × Fin N) ℤ` to `fun j => if hj : j ≤ N then lpMinor ℤ (r := N) (n := N) j hj hj else 1`. Establish `hA : ∀ k ∈ Finset.univ.filter (fun k => k ∈ L), lif h (stdT sz hsz k) (hN k) = A (sz k)`. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk`.

Establish `hk' : sz k < n` using `sz_lt sg sz hsz hsh k (hL'.1 k hk)`. Rewrite using `[lif_std h sz hsz k hk' (hN k)]`. Establish `e : A (sz k) = initMinor ℤ (n` using `N) (rowsZ h ⟨sz k, hk'⟩) (hN k) := dif_pos hk'`. Rewrite using `[e]`. Establish `hB : ∀ k ∈ Finset.univ.filter (fun k => ¬ k ∈ L), unl h (stdT sz hsz k) (by have` using `hsz k; omega) = B (sz k) := by`.

Introduce `k _`. Establish `hk' : sz k ≤ N` using `by have := hsz k; omega`. Rewrite using `[unl_std h sz hsz k hk']`. Establish `e : B (sz k) = lpMinor ℤ (r` using `N) (n := N) (sz k) hk' hk' := dif_pos hk'`. Rewrite using `[e]`.

Rewrite using `[Finset.prod_congr rfl hA, Finset.prod_congr rfl hB]`. Rewrite using `[prod_sz sz (Finset.univ.filter fun k => k ∈ L) n (fun k hk => sz_lt sg sz hsz hsh k (hL'.1 k (by simpa using hk))) A]`. Rewrite using `[prod_sz sz (Finset.univ.filter fun k => ¬ k ∈ L) (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) B, Finset.prod_range_succ']`. Establish `hB0 : B 0 = 1`. Establish `e : B 0 = lpMinor ℤ (r` using `N) (n := N) 0 (Nat.zero_le N) (Nat.zero_le N) := dif_pos (Nat.zero_le N)`.

Rewrite using `[e]`. Simplify using `[lpMinor]`. Rewrite using `[hB0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]`. Unfold `C0`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hi` using `i.2`. Establish `cL : ((Finset.univ.filter fun k => k ∈ L).filter fun k => sz k = i.1).card = if i.1 = 0 then 0 else (bb h lam sg i).toNat`. Rewrite using `[Finset.filter_filter]`. Conclude with `hL'.2 i`.

Establish `cN : ((Finset.univ.filter fun k => ¬ k ∈ L).filter fun k => sz k = i.1 + 1).card = if i.1 + 1 = n then 0 else (aa h lam sg i).toNat`. Rewrite using `[Finset.filter_filter]`. Conclude with `card_filter_not_mem_sz_eq_succ h lam sg hI sz hsz hsh L hL i`. Establish `eA : A i.1 = initMinor ℤ (n` using `N) (rowsZ h i) (by omega) := dif_pos hi`. Establish `eB : B (i.1 + 1) = lpMinor ℤ (r` using `N) (n := N) (i.1 + 1) (by omega) (by omega) := dif_pos (by omega)`.

Rewrite using `[cL, cN, eA, eB]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem mlift_std {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg := by
  have hL' := hL
  unfold GoodL at hL'
  have hN : ∀ k, sz k + 1 ≤ N := fun k => by have := hsz k; omega
  unfold Mlift xi
  rw [Finset.prod_ite]
  let A : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j < n then initMinor ℤ (n := N) (rowsZ h ⟨j, hj⟩) (by show j + 1 ≤ N; omega) else 1
  let B : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j ≤ N then lpMinor ℤ (r := N) (n := N) j hj hj else 1
  have hA : ∀ k ∈ Finset.univ.filter (fun k => k ∈ L), lif h (stdT sz hsz k) (hN k) = A (sz k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hk' : sz k < n := sz_lt sg sz hsz hsh k (hL'.1 k hk)
    rw [lif_std h sz hsz k hk' (hN k)]
    have e : A (sz k) = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk'⟩) (hN k) := dif_pos hk'
    rw [e]
  have hB : ∀ k ∈ Finset.univ.filter (fun k => ¬ k ∈ L),
      unl h (stdT sz hsz k) (by have := hsz k; omega) = B (sz k) := by
    intro k _
    have hk' : sz k ≤ N := by have := hsz k; omega
    rw [unl_std h sz hsz k hk']
    have e : B (sz k) = lpMinor ℤ (r := N) (n := N) (sz k) hk' hk' := dif_pos hk'
    rw [e]
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB]
  rw [prod_sz sz (Finset.univ.filter fun k => k ∈ L) n
    (fun k hk => sz_lt sg sz hsz hsh k (hL'.1 k (by simpa using hk))) A]
  rw [prod_sz sz (Finset.univ.filter fun k => ¬ k ∈ L) (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) B,
    Finset.prod_range_succ']
  have hB0 : B 0 = 1 := by
    have e : B 0 = lpMinor ℤ (r := N) (n := N) 0 (Nat.zero_le N) (Nat.zero_le N) := dif_pos (Nat.zero_le N)
    rw [e]
    simp [lpMinor]
  rw [hB0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  unfold C0
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi := i.2
  have cL : ((Finset.univ.filter fun k => k ∈ L).filter fun k => sz k = i.1).card =
      if i.1 = 0 then 0 else (bb h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact hL'.2 i
  have cN : ((Finset.univ.filter fun k => ¬ k ∈ L).filter fun k => sz k = i.1 + 1).card =
      if i.1 + 1 = n then 0 else (aa h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact card_filter_not_mem_sz_eq_succ h lam sg hI sz hsz hsh L hL i
  have eA : A i.1 = initMinor ℤ (n := N) (rowsZ h i) (by omega) := dif_pos hi
  have eB : B (i.1 + 1) = lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := dif_pos (by omega)
  rw [cL, cN, eA, eB]
  split_ifs <;> ring

/- English proof (translation)
Introduce `n N h lam sg hI K sz hsz hsh L hL`. Establish `hext : bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg`. Rewrite using `[bidet_std sz hsz _ hsh]`. Unfold `extremal`. Both sides reduce to the same expression.

Use `⟨?_, (tupCnt_std sz hsz).trans hsh, hext, mlift_std h lam sg hI sz hsz hsh L hL⟩` and prove the remaining obligations. Introduce `J hJ`. Distinguish the cases in `hinj : ∀ k, Function.Injective (J k)`. Establish `hlt` using `top_entries sz hsz J hinj (hJ.trans hsh.symm) choose σ hσ using top_perm sz hsz J hinj hlt`. Use `⟨∏ k, (Equiv.Perm.sign (σ k) : ℤ), ?_, ?_⟩` and prove the remaining obligations.

Establish `e1 : bideterminant ℤ sz hsz J = (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • bideterminant ℤ sz hsz (stdT sz hsz)`. Unfold `bideterminant`. Rewrite using `[← prod_zsmul']`. Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[hσ k, initMinor_perm]`.

Rewrite using `[e1, hext]`. Establish `e2 : Mlift h lam sg sz hsz L J = (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • Mlift h lam sg sz hsz L (stdT sz hsz)`. Unfold `Mlift`. Rewrite using `[← mul_smul_comm, ← prod_zsmul']`. Use `congr 1`.

Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[hσ k]`. Use `split_ifs`. Conclude with `lif_perm h _ _ _`. Conclude with `unl_perm h _ _ _`.

Rewrite using `[e2, mlift_std h lam sg hI sz hsz hsh L hL]`. Take `⟨k0, hk0⟩` from `not_forall.mp hinj`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul]`. Unfold `bideterminant`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ k0) (initMinor_not_inj _ _ hk0)`. Rewrite using `[zero_smul]`. Unfold `Mlift`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (Finset.mem_univ k0)` to reduce the goal to its premises.

Apply the tactic sequence `try dsimp only`. Use `split_ifs`. Conclude with `lif_not_inj h _ _ hk0`. Conclude with `unl_not_inj h _ _ hk0`.
-/
theorem top_component_formula : TopPart := by
  intro n N h lam sg hI K sz hsz hsh L hL
  have hext : bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg := by
    rw [bidet_std sz hsz _ hsh]
    unfold extremal
    rfl
  refine ⟨?_, (tupCnt_std sz hsz).trans hsh, hext, mlift_std h lam sg hI sz hsz hsh L hL⟩
  intro J hJ
  by_cases hinj : ∀ k, Function.Injective (J k)
  · have hlt := top_entries sz hsz J hinj (hJ.trans hsh.symm)
    choose σ hσ using top_perm sz hsz J hinj hlt
    refine ⟨∏ k, (Equiv.Perm.sign (σ k) : ℤ), ?_, ?_⟩
    · have e1 : bideterminant ℤ sz hsz J = (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • bideterminant ℤ sz hsz (stdT sz hsz) := by
        unfold bideterminant
        rw [← prod_zsmul']
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k, initMinor_perm]
      rw [e1, hext]
    · have e2 : Mlift h lam sg sz hsz L J =
          (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • Mlift h lam sg sz hsz L (stdT sz hsz) := by
        unfold Mlift
        rw [← mul_smul_comm, ← prod_zsmul']
        congr 1
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k]
        split_ifs
        · exact lif_perm h _ _ _
        · exact unl_perm h _ _ _
      rw [e2, mlift_std h lam sg hI sz hsz hsh L hL]
  · obtain ⟨k0, hk0⟩ := not_forall.mp hinj
    refine ⟨0, ?_, ?_⟩
    · rw [zero_smul]
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (initMinor_not_inj _ _ hk0)
    · rw [zero_smul]
      unfold Mlift
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ k0)
      try dsimp only
      split_ifs
      · exact lif_not_inj h _ _ hk0
      · exact unl_not_inj h _ _ hk0

end PI.WGL.LTB
