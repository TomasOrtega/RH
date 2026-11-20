import Formalism.PeriodIntegrals.TwNormLat

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {K : Type} [Field K] {n : ℕ}

def Zab (k : ℕ) (v : Fin n → K) : Prop := ∀ l : Fin n, k ≤ l.1 → v l = 0

def UT (b : Fin n → Fin n → K) : Prop := ∀ l k : Fin n, l < k → b l k = 0

/- English proof (translation)
Introduce `l hl`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : k0 ≤ i.1`. Rewrite using `[hw i hi, zero_mul]`.

Establish `hil : i < l` using `Fin.lt_def.2 (by omega)`. Rewrite using `[hb i l hil, mul_zero]`.
-/
theorem comb_zab {b : Fin n → Fin n → K} (hb : UT b) (w : Fin n → K) (k0 : ℕ) (hw : Zab k0 w) :
    Zab k0 (∑ i, w i • b i) := by
  intro l hl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : k0 ≤ i.1
  · rw [hw i hi, zero_mul]
  · have hil : i < l := Fin.lt_def.2 (by omega)
    rw [hb i l hil, mul_zero]

/- English proof (translation)
Establish `key : ∀ d : ℕ, ∀ l : Fin n, n - l.1 ≤ d → k0 ≤ l.1 → w l = 0`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro l hl _`. Use `l.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Consider the case `succ d ih`. Introduce `l hl hk`. Establish `hs` using `h l hk`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs`.

Rewrite `hs` using `[Finset.sum_eq_single l]`. Conclude with `(mul_eq_zero.1 hs).resolve_right (hd l)`. Introduce `i _ hil`. Break down `lt_or_gt_of_ne hil with hlt | hgt` into its components or cases. Rewrite using `[hb i l hlt, mul_zero]`.

Establish `h2` using `Fin.lt_def.1 hgt`. Establish `h3` using `i.2`. Rewrite using `[ih i (by omega) (by omega), zero_mul]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ l) h'`.

Introduce `l hl`. Conclude with `key (n - l.1) l le_rfl hl`.
-/
theorem comb_reflect {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) (k0 : ℕ)
    (h : Zab k0 (∑ i, w i • b i)) : Zab k0 w := by
  have key : ∀ d : ℕ, ∀ l : Fin n, n - l.1 ≤ d → k0 ≤ l.1 → w l = 0 := by
    intro d
    induction d with
    | zero => intro l hl _; have := l.2; omega
    | succ d ih =>
      intro l hl hk
      have hs := h l hk
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
      rw [Finset.sum_eq_single l] at hs
      · exact (mul_eq_zero.1 hs).resolve_right (hd l)
      · intro i _ hil
        rcases lt_or_gt_of_ne hil with hlt | hgt
        · rw [hb i l hlt, mul_zero]
        · have h2 := Fin.lt_def.1 hgt
          have h3 := i.2
          rw [ih i (by omega) (by omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ l) h'
  intro l hl
  exact key (n - l.1) l le_rfl hl

def combL (b : Fin n → Fin n → K) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun w := ∑ i, w i • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.smul_sum, mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem combL_apply (b : Fin n → Fin n → K) (w : Fin n → K) : combL b w = ∑ i, w i • b i := rfl

/- English proof (translation)
Rewrite using `[combL_apply, Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul]) (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, one_smul]`.
-/
theorem combL_single (b : Fin n → Fin n → K) (l : Fin n) : combL b (Pi.single l 1) = b l := by
  rw [combL_apply, Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, one_smul]

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun w hw => ?_` and prove the remaining obligations. Establish `hz : Zab 0 (∑ i, w i • b i)`. Introduce `l _`. Rewrite using `[← combL_apply, hw]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `l`. Conclude with `comb_reflect hb hd w 0 hz l (Nat.zero_le _)`.
-/
theorem combL_inj {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : Function.Injective (combL b) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have hz : Zab 0 (∑ i, w i • b i) := by
    intro l _
    rw [← combL_apply, hw]
    rfl
  funext l
  exact comb_reflect hb hd w 0 hz l (Nat.zero_le _)

def combE {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofInjectiveEndo (combL b) (combL_inj hb hd)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem combE_apply {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) :
    combE hb hd w = ∑ i, w i • b i := rfl

/- English proof (translation)
Establish `h` using `combE_apply hb hd ((combE hb hd).symm v)`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`. Use `comb_reflect hb hd _ k0 ?_` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `hv`.
-/
theorem combE_symm_zab {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (k0 : ℕ) (v : Fin n → K)
    (hv : Zab k0 v) : Zab k0 ((combE hb hd).symm v) := by
  have h := combE_apply hb hd ((combE hb hd).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  refine comb_reflect hb hd _ k0 ?_
  rw [← h]
  exact hv

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[Loc.eN, Pi.single_apply, Fin.ext_iff]`.
-/
theorem eN_eq_single (l : Fin n) : Loc.eN K n l.1 = Pi.single l 1 := by
  funext m
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Use `m.2` as an intermediate fact. Simplify using `only [Loc.eN, Pi.zero_apply]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem eN_eq_zero {i : ℕ} (hi : n ≤ i) : Loc.eN K n i = 0 := by
  funext m
  have := m.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

/- English proof (translation)
Use `show (∀ l : Fin (N + c), l.1 ∉ {l : ℕ | l < N + i} → v l = 0) ↔ ∀ l : Fin (N + c), N + i ≤ l.1 → v l = 0`. Simplify using `only [Set.mem_ofPred_eq, not_lt]`.
-/
theorem mem_Ufl_iff {N c i : ℕ} (v : Fin (N + c) → K) : v ∈ Loc.Ufl K N c i ↔ Zab (N + i) v := by
  show (∀ l : Fin (N + c), l.1 ∉ {l : ℕ | l < N + i} → v l = 0) ↔ ∀ l : Fin (N + c), N + i ≤ l.1 → v l = 0
  simp only [Set.mem_ofPred_eq, not_lt]

/- English proof (translation)
Use `⟨fun i v hv => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[mem_Ufl_iff]`. Rewrite using `[combE_apply]`. Conclude with `comb_zab hb v _ hv`. Distinguish the cases in `hN : N < N + c`.

Establish `he : Loc.eN K (N + c) N = Pi.single (⟨N, hN⟩ : Fin (N + c)) 1` using `eN_eq_single (⟨N, hN⟩ : Fin (N + c))`. Rewrite using `[he]`. Express the relevant statement in the definitionally equal form `combL b (Pi.single _ 1) = _`. Rewrite using `[combL_single, ha hN]`. Establish `he : Loc.eN K (N + c) N = 0` using `eN_eq_zero (by omega)`.

Rewrite using `[he, map_zero]`. Rewrite using `[mem_Ufl_iff]`. Distinguish the cases in `hi : N + i < N + c`. Establish `he : Loc.eN K (N + c) (N + i) = Pi.single (⟨N + i, hi⟩ : Fin (N + c)) 1` using `eN_eq_single (⟨N + i, hi⟩ : Fin (N + c))`. Rewrite using `[he]`.

Express the relevant statement in the definitionally equal form `Zab (N + i) (combL b (Pi.single _ 1) - _)`. Rewrite using `[combL_single]`. Introduce `m hm`. Simplify using `only [Pi.sub_apply]`. Break down `lt_or_eq_of_le hm with hlt | heq` into its components or cases.

Establish `hne : m ≠ ⟨N + i, hi⟩`. Introduce `h`. Substitute `h` using the available equality. Conclude with `lt_irrefl _ hlt`. Rewrite using `[hb _ _ (Fin.lt_def.2 hlt), Pi.single_eq_of_ne hne, sub_zero]`.

Establish `hm' : m = ⟨N + i, hi⟩` using `Fin.ext heq.symm`. Substitute `hm'` using the available equality. Rewrite using `[Pi.single_eq_same, h1 _ (Nat.le_add_right N i), sub_self]`. Establish `he : Loc.eN K (N + c) (N + i) = 0` using `eN_eq_zero (by omega)`. Rewrite using `[he, map_zero, sub_zero]`.

Introduce `m _`. Both sides reduce to the same expression.
-/
private theorem R1cond_combE {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd) := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl_iff] at hv ⊢
    rw [combE_apply]
    exact comb_zab hb v _ hv
  · by_cases hN : N < N + c
    · have he : Loc.eN K (N + c) N = Pi.single (⟨N, hN⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N, hN⟩ : Fin (N + c))
      rw [he]
      change combL b (Pi.single _ 1) = _
      rw [combL_single, ha hN]
    · have he : Loc.eN K (N + c) N = 0 := eN_eq_zero (by omega)
      rw [he, map_zero]
  · rw [mem_Ufl_iff]
    by_cases hi : N + i < N + c
    · have he : Loc.eN K (N + c) (N + i) = Pi.single (⟨N + i, hi⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N + i, hi⟩ : Fin (N + c))
      rw [he]
      change Zab (N + i) (combL b (Pi.single _ 1) - _)
      rw [combL_single]
      intro m hm
      simp only [Pi.sub_apply]
      rcases lt_or_eq_of_le hm with hlt | heq
      · have hne : m ≠ ⟨N + i, hi⟩ := by
          intro h
          subst h
          exact lt_irrefl _ hlt
        rw [hb _ _ (Fin.lt_def.2 hlt), Pi.single_eq_of_ne hne, sub_zero]
      · have hm' : m = ⟨N + i, hi⟩ := Fin.ext heq.symm
        subst hm'
        rw [Pi.single_eq_same, h1 _ (Nat.le_add_right N i), sub_self]
    · have he : Loc.eN K (N + c) (N + i) = 0 := eN_eq_zero (by omega)
      rw [he, map_zero, sub_zero]
      intro m _
      rfl

/- English proof (translation)
Establish `hT` using `R1cond_combE hb hd h1 ha`. Establish `hs : ∀ i, ∀ v ∈ Loc.Ufl K N c i, (combE hb hd).symm v ∈ Loc.Ufl K N c i` using `fun i v hv => (mem_Ufl_iff _).2 (combE_symm_zab hb hd _ v ((mem_Ufl_iff _).1 hv))`. Use `⟨hs, (LinearEquiv.symm_apply_eq _).2 hT.2.1.symm, fun i => ?_⟩` and prove the remaining obligations. Establish `h3` using `hs i _ (hT.2.2 i)`. Rewrite `h3` using `[map_sub, LinearEquiv.symm_apply_apply]`.

Establish `h4` using `(Loc.Ufl K N c i).neg_mem h3`. Rewrite `h4` using `[neg_sub]`. Then use the resulting hypothesis.
-/
private theorem R1cond_combE_symm {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd).symm := by
  have hT := R1cond_combE hb hd h1 ha
  have hs : ∀ i, ∀ v ∈ Loc.Ufl K N c i, (combE hb hd).symm v ∈ Loc.Ufl K N c i := fun i v hv =>
    (mem_Ufl_iff _).2 (combE_symm_zab hb hd _ v ((mem_Ufl_iff _).1 hv))
  refine ⟨hs, (LinearEquiv.symm_apply_eq _).2 hT.2.1.symm, fun i => ?_⟩
  have h3 := hs i _ (hT.2.2 i)
  rw [map_sub, LinearEquiv.symm_apply_apply] at h3
  have h4 := (Loc.Ufl K N c i).neg_mem h3
  rwa [neg_sub] at h4

/- English proof (translation)
Use `show Loc.R1cond K N c (combE hb hd)⁻¹ ∧ Loc.R1cond K N c (combE hb hd)⁻¹⁻¹`. Rewrite using `[inv_inv]`. Conclude with `⟨R1cond_combE_symm hb hd h1 ha, R1cond_combE hb hd h1 ha⟩`.
-/
theorem combinationEquiv_inv_mem_unipotentFlagGroup {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    (combE hb hd)⁻¹ ∈ Loc.R1 K N c := by
  show Loc.R1cond K N c (combE hb hd)⁻¹ ∧ Loc.R1cond K N c (combE hb hd)⁻¹⁻¹
  rw [inv_inv]
  exact ⟨R1cond_combE_symm hb hd h1 ha, R1cond_combE hb hd h1 ha⟩

end PI.TwNormLat.W
