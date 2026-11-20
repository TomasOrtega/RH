import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

/- English proof (translation)
Establish `hsl : Function.support (fun x => g x * φv x) ⊆ (S : Set X)` using `fun x hx => hS x (left_ne_zero_of_mul hx)`. Establish `hin : ∀ y, (∑ᶠ x, if P y x then g x else 0) = ∑ x ∈ S, if P y x then g x else 0`. Introduce `y`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `x hx`.

Distinguish the cases in `hP : P y x`. Conclude with `hS x (by simpa [hP] using hx)`. Conclude with `absurd (by simp [hP]) hx`. Establish `hTfin : (⋃ x ∈ (S : Set X), {y | P y x}).Finite` using `S.finite_toSet.biUnion fun x _ => Set.Subsingleton.finite fun y hy y' hy' => huniq x y y' hy hy'`. Establish `hout : (∑ᶠ y, c y * ∑ x ∈ S, if P y x then g x else 0) = ∑ y ∈ hTfin.toFinset, c y * ∑ x ∈ S, if P y x then g x else 0`.

Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[Set.Finite.coe_toFinset]`. Establish `hne : (∑ x ∈ S, if P y x then g x else 0) ≠ 0` using `right_ne_zero_of_mul hy`. Take `⟨x, hxS, hx⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`.

Use `Set.mem_biUnion (Finset.mem_coe.mpr hxS) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hP`. Conclude with `hx (if_neg hP)`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsl]`. Simplify using `only [hin]`.

Rewrite using `[hout, Finset.sum_mul]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x hxS => ?_` and prove the remaining obligations. Distinguish the cases in `hex : ∃ y, P y x`.

Take `⟨y0, hy0⟩` from `hex`. Establish `hy0T : y0 ∈ hTfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr hxS) hy0`. Rewrite using `[Finset.sum_eq_single y0, if_pos hy0, hφ x y0 hy0]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `y _ hy`. Rewrite using `[if_neg (fun h => hy (huniq x y y0 h hy0))]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Conclude with `absurd hy0T h`. Use `push_neg at hex`. Rewrite using `[hnone x hex, mul_zero]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `y _`. Rewrite using `[if_neg (hex y)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finsum_mul_eq_sum_over_classes {X Y : Type} (S : Finset X) (g φv : X → ℂ) (c : Y → ℂ) (φ1 : ℂ)
    (P : Y → X → Prop) {_ : ∀ y x, Decidable (P y x)}
    (hS : ∀ x, g x ≠ 0 → x ∈ S) (huniq : ∀ x y y', P y x → P y' x → y = y')
    (hφ : ∀ x y, P y x → φv x = c y * φ1) (hnone : ∀ x, (∀ y, ¬ P y x) → φv x = 0) :
    ∑ᶠ x, g x * φv x = (∑ᶠ y, c y * ∑ᶠ x, if P y x then g x else 0) * φ1 := by
  classical
  have hsl : Function.support (fun x => g x * φv x) ⊆ (S : Set X) :=
    fun x hx => hS x (left_ne_zero_of_mul hx)
  have hin : ∀ y, (∑ᶠ x, if P y x then g x else 0) = ∑ x ∈ S, if P y x then g x else 0 := by
    intro y
    apply finsum_eq_sum_of_support_subset
    intro x hx
    by_cases hP : P y x
    · exact hS x (by simpa [hP] using hx)
    · exact absurd (by simp [hP]) hx
  have hTfin : (⋃ x ∈ (S : Set X), {y | P y x}).Finite :=
    S.finite_toSet.biUnion fun x _ => Set.Subsingleton.finite fun y hy y' hy' => huniq x y y' hy hy'
  have hout : (∑ᶠ y, c y * ∑ x ∈ S, if P y x then g x else 0) =
      ∑ y ∈ hTfin.toFinset, c y * ∑ x ∈ S, if P y x then g x else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro y hy
    rw [Set.Finite.coe_toFinset]
    have hne : (∑ x ∈ S, if P y x then g x else 0) ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine Set.mem_biUnion (Finset.mem_coe.mpr hxS) ?_
    by_contra hP
    exact hx (if_neg hP)
  rw [finsum_eq_sum_of_support_subset _ hsl]
  simp only [hin]
  rw [hout, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hxS => ?_
  by_cases hex : ∃ y, P y x
  · obtain ⟨y0, hy0⟩ := hex
    have hy0T : y0 ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) hy0
    rw [Finset.sum_eq_single y0, if_pos hy0, hφ x y0 hy0]
    · ring
    · intro y _ hy
      rw [if_neg (fun h => hy (huniq x y y0 h hy0))]
      ring
    · intro h
      exact absurd hy0T h
  · push_neg at hex
    rw [hnone x hex, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (hex y)]
    ring

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Unfold `chiDeltaU`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[fSatake_ord_one]`. Both sides reduce to the same expression.
-/
theorem fSatake_chiDelta_one {q m : ℕ} (α : Fin m → ℂ) :
    chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · simp [fSatake_ord_one]
  · rfl

/- English proof (translation)
Establish `hfin` using `finite_supp (KU σ n) (isCommensurated_integral_unitary_of_unramified hU n) h hh`. Unfold `SatU`. Conclude with `finsum_mul_eq_sum_over_classes (S := hfin.toFinset) (g := fun x => h x.out) (φv := fun x => φ x.out) (c := fun a : Fin m → ℤ => ∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) (φ1 := φ 1) (P := fun a x => ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, (( …`. Introduce and unpack `⟨b, k, hb, hk, e⟩`. Take `⟨a, u, hu, k', hk', e'⟩` from `fSatake_cell_exists hU hm hm' hb hk`.

Conclude with `hx a ⟨u, hu, k', hk', e ▸ e'⟩))`.
-/
theorem fSatake_key (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) {φ : GU σ n → ℂ}
    (hφ : IsSphericalU q α φ) :
    ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out * φ x.out = SatU ϖ q h α * φ 1 := by
  classical
  have hfin := finite_supp (KU σ n) (isCommensurated_integral_unitary_of_unramified hU n) h hh
  unfold SatU
  exact finsum_mul_eq_sum_over_classes (S := hfin.toFinset) (g := fun x => h x.out) (φv := fun x => φ x.out)
    (c := fun a : Fin m → ℤ =>
      ∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))))
    (φ1 := φ 1)
    (P := fun a x => ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
    (fun x hx => hfin.mem_toFinset.mpr hx)
    (fun x a a' ⟨u, hu, k, hk, e⟩ ⟨u', hu', k', hk', e'⟩ =>
      fSatake_cell_unique hU hm hu hu' hk hk' (e.symm.trans e'))
    (fun x a ⟨u, hu, k, hk, e⟩ => fSatake_phi_cell hU hm hφ hu hk e)
    (fun x hx => fSatake_vanish hSph hU hm hm' hα hφ x.out (by
      rintro ⟨b, k, hb, hk, e⟩
      obtain ⟨a, u, hu, k', hk', e'⟩ := fSatake_cell_exists hU hm hm' hb hk
      exact hx a ⟨u, hu, k', hk', e ▸ e'⟩))

/- English proof (translation)
Introduce `b g k hb hk`. Establish `hb1 : IsBorelU (1 : GU σ n)` using `fun i j hij => by`. Simplify using `[Matrix.one_apply_ne (ne_of_lt hij).symm]`. Establish `hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y` using `fun y κ hκ => by`. Use `hφ 1 y κ hb1 hκ` as an intermediate fact.

Simplify `this` using `[fSatake_chiDelta_one]`. Establish `hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y` using `fun y => by`. Use `hφ b y 1 hb (KU σ n).one_mem` as an intermediate fact. Simplify using `using this`. Take `⟨hbi, -⟩` from `hh`.

Unfold `hAct`. Combine the equalities or inequalities in the displayed calculation. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) := (mul_finsum _ _).symm`. Use `_ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by`. Use `congr 1`. Use `symm`. Rewrite using `[← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]`.

Use `finsum_congr fun x => ?_` and prove the remaining obligations. Take `⟨κ, hκ⟩` from `out_smul (KU σ n) k x`. Simplify using `only [MulAction.toPerm_apply]`. Rewrite using `[hκ]`. Establish `e1 : h (k * x.out * κ) = h x.out` using `hbi ⟨k, hk⟩ κ x.out`.

Rewrite using `[e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]`.
-/
theorem fSatake_hAct_sph {q m : ℕ} {α : Fin m → ℂ} {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) : IsSphericalU q α (hAct (KU σ n) h φ) := by
  intro b g k hb hk
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y := fun y κ hκ => by
    have := hφ 1 y κ hb1 hκ
    simpa [fSatake_chiDelta_one] using this
  have hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y := fun y => by
    have := hφ b y 1 hb (KU σ n).one_mem
    simpa using this
  obtain ⟨hbi, -⟩ := hh
  unfold hAct
  calc ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (b * g * k * x.out)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, chiDeltaU q α b * (h x.out • φ (g * (k * x.out))) := by
        refine finsum_congr fun x => ?_
        rw [show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]
        ring
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) :=
        (mul_finsum _ _).symm
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by
        congr 1
        symm
        rw [← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]
        refine finsum_congr fun x => ?_
        obtain ⟨κ, hκ⟩ := out_smul (KU σ n) k x
        simp only [MulAction.toPerm_apply]
        rw [hκ]
        have e1 : h (k * x.out * κ) = h x.out := hbi ⟨k, hk⟩ κ x.out
        rw [e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ`. Take `⟨φ0, -, -, huniq⟩` from `hSphericalExistsU L ϖ σ q n m hU hm hm' α hα`. Establish `h1` using `huniq _ (fSatake_hAct_sph hh hφ)`. Establish `h2` using `huniq _ hφ`. Establish `hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1`.

Unfold `hAct`. Simplify using `only [one_mul, smul_eq_mul]`. Conclude with `fSatake_key hSphericalExistsU hU hm hm' hα hh hφ`. Rewrite using `[h1, hv]`. Use `conv_rhs => rw [h2]`.

Use function extensionality and compare the values at `g`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem satake_transform_inert_prime (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatakeInert := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ
  obtain ⟨φ0, -, -, huniq⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have h1 := huniq _ (fSatake_hAct_sph hh hφ)
  have h2 := huniq _ hφ
  have hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1 := by
    unfold hAct
    simp only [one_mul, smul_eq_mul]
    exact fSatake_key hSphericalExistsU hU hm hm' hα hh hφ
  rw [h1, hv]
  conv_rhs => rw [h2]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂`. Take `⟨φ0, hφ0, hφ01, -⟩` from `hSphericalExistsU L ϖ σ q n m hU hm hm' α hα`. Establish `hSI` using `satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα`. Establish `hh₁'` using `hh₁`. Establish `hh₂'` using `hh₂`.

Take `⟨hb₁, hs₁⟩` from `hh₁'`. Take `⟨hb₂, hs₂⟩` from `hh₂'`. Establish `hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n)` using `by show _ ∧ _`. Conclude with `⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩`. Establish `hb1 : IsBorelU (1 : GU σ n)` using `fun i j hij => by`.

Simplify using `[Matrix.one_apply_ne (ne_of_lt hij).symm]`. Establish `hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n) (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ)`. Introduce `γ g κ`. Establish `hγ : (γ : GU σ n) = 1` using `Subgroup.mem_bot.mp γ.2`. Rewrite using `[hγ, one_mul]`.

Use `hφ0 1 g κ hb1 κ.2` as an intermediate fact. Simplify `this` using `[fSatake_chiDelta_one]`. Establish `hmul` using `hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf`. Establish `hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0)` using `fun b g k hb hk => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hmul` using `[hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2]`. Use `congrFun hmul 1` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this`. Rewrite using `[this]`.
-/
theorem satake_transform_multiplicative (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatMul := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂
  obtain ⟨φ0, hφ0, hφ01, -⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hSI := satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hh₁' := hh₁
  have hh₂' := hh₂
  obtain ⟨hb₁, hs₁⟩ := hh₁'
  obtain ⟨hb₂, hs₂⟩ := hh₂'
  have hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n) := by
    show _ ∧ _
    exact ⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n)
      (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ) := by
    intro γ g κ
    have hγ : (γ : GU σ n) = 1 := Subgroup.mem_bot.mp γ.2
    rw [hγ, one_mul]
    have := hφ0 1 g κ hb1 κ.2
    simpa [fSatake_chiDelta_one] using this
  have hmul := hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf
  have hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0) := fun b g k hb hk => by
    simp only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]
    ring
  rw [hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2] at hmul
  have := congrFun hmul 1
  simp only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this
  rw [this]

end Formalism.UG.P
