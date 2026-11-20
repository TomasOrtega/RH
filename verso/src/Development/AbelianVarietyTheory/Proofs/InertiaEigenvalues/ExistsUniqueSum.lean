import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc

namespace ParamRing

variable {R : Type} [CommRing R] {σ : R⟦X⟧ →ₐ[R] R⟦X⟧} {w : R⟦X⟧} {s : ℕ}

/- English proof (translation)
Take `⟨H, rfl⟩` from `hG`. Conclude with `⟨w ^ j * σ H, by rw [map_mul, map_pow, h, pow_mul]; ring⟩`.
-/
theorem X_pow_dvd_map (h : σ X = w * X ^ s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    X ^ (s * j) ∣ σ G := by
  obtain ⟨H, rfl⟩ := hG
  exact ⟨w ^ j * σ H, by rw [map_mul, map_pow, h, pow_mul]; ring⟩

/- English proof (translation)
Take `⟨H, rfl⟩` from `hG`. Establish `h0 : constantCoeff (σ H) = constantCoeff H` using `by conv_lhs => rw [eq_X_mul_shift_add_const H]`. Rewrite using `[map_add, map_mul, h, show σ (C (constantCoeff H)) = C (constantCoeff H) from σ.commutes _]`. Simplify using `[hs.ne']`. Establish `h1 : σ (X ^ j * H) = X ^ (s * j) * (w ^ j * σ H)`.

Rewrite using `[map_mul, map_pow, h, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `coeff_X_pow_mul (w ^ j * σ H) (s * j) 0`. Establish `h3` using `coeff_X_pow_mul H j 0`. Rewrite `h2`, `h3` using `[zero_add]`.

Rewrite using `[h1, h2, h3]`. Simplify using `[h0]`.
-/
theorem coeff_map_lead (h : σ X = w * X ^ s) (hs : 0 < s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    coeff (s * j) (σ G) = constantCoeff w ^ j * coeff j G := by
  obtain ⟨H, rfl⟩ := hG
  have h0 : constantCoeff (σ H) = constantCoeff H := by
    conv_lhs => rw [eq_X_mul_shift_add_const H]
    rw [map_add, map_mul, h, show σ (C (constantCoeff H)) = C (constantCoeff H) from σ.commutes _]
    simp [hs.ne']
  have h1 : σ (X ^ j * H) = X ^ (s * j) * (w ^ j * σ H) := by
    rw [map_mul, map_pow, h, pow_mul]; ring
  have h2 := coeff_X_pow_mul (w ^ j * σ H) (s * j) 0
  have h3 := coeff_X_pow_mul H j 0
  rw [zero_add] at h2 h3
  rw [h1, h2, h3]
  simp [h0]

/- English proof (translation)
Establish `hn` using `Nat.mod_add_div n s`. Establish `key : ∀ k : Fin s, (k : ℕ) ≠ n % s → X ^ (n + 1) ∣ X ^ (k : ℕ) * σ (G k)`. Introduce `k hk`. Establish `hk'` using `k.2`. Break down `lt_or_gt_of_ne hk with hlt | hgt` into its components or cases.

Establish `h1 : X ^ (n / s + 1) ∣ G k` using `X_pow_dvd_iff.2 fun m hm => hG k m (by`. Use `Nat.mul_le_mul_left s (Nat.lt_succ_iff.1 hm)` as an intermediate fact. Use the proof step `omega)`. Use `(pow_dvd_pow X ?_).trans ((X_pow_dvd_map h h1).mul_left _)` and prove the remaining obligations. Use `Nat.mod_lt n hs` as an intermediate fact.

Rewrite using `[mul_add]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : X ^ (n / s) ∣ G k` using `X_pow_dvd_iff.2 fun m hm => hG k m (by`. Use `Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm)` as an intermediate fact. Rewrite `this` using `[Nat.mul_succ]`.

Use the proof step `omega)`. Use `(pow_dvd_pow X (show n + 1 ≤ k + s * (n / s) by omega)).trans ?_` and prove the remaining obligations. Rewrite using `[pow_add]`. Conclude with `mul_dvd_mul_left _ (X_pow_dvd_map h h1)`. Establish `h1 : X ^ (n / s) ∣ G ⟨n % s, Nat.mod_lt _ hs⟩` using `X_pow_dvd_iff.2 fun m hm => hG _ m (by`.

Use `Nat.mul_lt_mul_of_pos_left hm hs` as an intermediate fact. Simplify using `only`. Use the proof step `omega)`. Prove the components needed by the constructor for the conclusion. Use `Finset.dvd_sum fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : (k : ℕ) = n % s`. Take `rfl : k = ⟨n % s, Nat.mod_lt _ hs⟩` from `Fin.ext hk conv_lhs => rw [← hn, pow_add]`. Conclude with `mul_dvd_mul_left _ (X_pow_dvd_map h h1)`. Conclude with `(pow_dvd_pow X n.le_succ).trans (key k hk)`. Rewrite using `[map_sum, Finset.sum_eq_single ⟨n % s, Nat.mod_lt _ hs⟩]`.

Rewrite using `[← coeff_map_lead h hs h1, ← coeff_X_pow_mul (σ _) (n % s) (s * (n / s)), add_comm, hn]`. Introduce `k _ hk`. Conclude with `X_pow_dvd_iff.1 (key k fun e => hk (Fin.ext e)) n n.lt_succ_self`. Simplify using the standard rewrite rules.
-/
theorem lead_sum (h : σ X = w * X ^ s) (hs : 0 < s) (G : Fin s → R⟦X⟧) (n : ℕ)
    (hG : ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0) :
    X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) ∧
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) =
        constantCoeff w ^ (n / s) * coeff (n / s) (G ⟨n % s, Nat.mod_lt _ hs⟩) := by
  have hn := Nat.mod_add_div n s
  have key : ∀ k : Fin s, (k : ℕ) ≠ n % s → X ^ (n + 1) ∣ X ^ (k : ℕ) * σ (G k) := by
    intro k hk
    have hk' := k.2
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h1 : X ^ (n / s + 1) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.lt_succ_iff.1 hm)
        omega)
      refine (pow_dvd_pow X ?_).trans ((X_pow_dvd_map h h1).mul_left _)
      have := Nat.mod_lt n hs
      rw [mul_add]; omega
    · have h1 : X ^ (n / s) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm)
        rw [Nat.mul_succ] at this
        omega)
      refine (pow_dvd_pow X (show n + 1 ≤ k + s * (n / s) by omega)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
  have h1 : X ^ (n / s) ∣ G ⟨n % s, Nat.mod_lt _ hs⟩ := X_pow_dvd_iff.2 fun m hm => hG _ m (by
    have := Nat.mul_lt_mul_of_pos_left hm hs
    simp only
    omega)
  constructor
  · refine Finset.dvd_sum fun k _ => ?_
    by_cases hk : (k : ℕ) = n % s
    · obtain rfl : k = ⟨n % s, Nat.mod_lt _ hs⟩ := Fin.ext hk
      conv_lhs => rw [← hn, pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
    · exact (pow_dvd_pow X n.le_succ).trans (key k hk)
  · rw [map_sum, Finset.sum_eq_single ⟨n % s, Nat.mod_lt _ hs⟩]
    · rw [← coeff_map_lead h hs h1, ← coeff_X_pow_mul (σ _) (n % s) (s * (n / s)), add_comm, hn]
    · intro k _ hk
      exact X_pow_dvd_iff.1 (key k fun e => hk (Fin.ext e)) n n.lt_succ_self
    · simp

/- English proof (translation)
Establish `key : ∀ n, ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro k j hj`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ n ih`. Introduce `k j hj`. Break down `(Nat.lt_succ_iff.1 hj).lt_or_eq with hj | hj` into its components or cases. Conclude with `ih k j hj`. Take `⟨h1, h2⟩` from `lead_sum h hs G n ih`.

Establish `e1 : n % s = k` using `by rw [← hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]`. Establish `e2 : n / s = j` using `by rw [← hj, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt k.2, zero_add]`. Establish `e3 : (⟨n % s, Nat.mod_lt _ hs⟩ : Fin s) = k` using `Fin.ext e1`. Establish `h3` using `hG n h1`. Rewrite `h3` using `[h2, e3, e2]`.

Break down `h3 with h3 | h3` into its components or cases. Conclude with `((hw.map constantCoeff).pow j).mul_right_eq_zero.1 h3`. Rewrite using `[h3, map_zero]`. Use extensionality with `k j`. Conclude with `key _ k j (Nat.lt_succ_self _)`.
-/
theorem eq_zero_of_lead (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (G : Fin s → R⟦X⟧)
    (hG : ∀ n, X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) →
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) = 0 ∨ G ⟨n % s, Nat.mod_lt _ hs⟩ = 0) : G = 0 := by
  have key : ∀ n, ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0 := by
    intro n
    induction n with
    | zero => intro k j hj; omega
    | succ n ih =>
      intro k j hj
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | hj
      · exact ih k j hj
      obtain ⟨h1, h2⟩ := lead_sum h hs G n ih
      have e1 : n % s = k := by rw [← hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
      have e2 : n / s = j := by rw [← hj, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt k.2, zero_add]
      have e3 : (⟨n % s, Nat.mod_lt _ hs⟩ : Fin s) = k := Fin.ext e1
      have h3 := hG n h1
      rw [h2, e3, e2] at h3
      rcases h3 with h3 | h3
      · exact ((hw.map constantCoeff).pow j).mul_right_eq_zero.1 h3
      · rw [h3, map_zero]
  ext k j
  exact key _ k j (Nat.lt_succ_self _)

/- English proof (translation)
Take `⟨v, hv⟩` from `hw.exists_right_inv`. Set `T : R⟦X⟧ → R⟦X⟧` to `fun b => v * mk fun i => coeff (i + s) b`. Set `G : R⟦X⟧ → Fin s → R⟦X⟧` to `fun b k => mk fun j => coeff k (T^[j] b)`. Establish `hT : ∀ b : R⟦X⟧, b = σ X * T b + ∑ k : Fin s, X ^ (k : ℕ) * C (coeff k b)`. Introduce `b`.

Establish `h1 : σ X * T b = X ^ s * mk fun i => coeff (i + s) b`. Simplify using `only [h, T]`. Take the linear combination `(X ^ s * mk fun i => coeff (i + s) b) * hv`. Rewrite using `[h1]`. Use extensionality with `n`.

Rewrite using `[map_add, coeff_X_pow_mul', map_sum]`. Simplify using `only [coeff_mul_C, coeff_X_pow, coeff_mk]`. Use `split_ifs with hn`. Rewrite using `[Nat.sub_add_cancel hn, Finset.sum_eq_zero, add_zero]`. Introduce `k _`.

Use `k.2` as an intermediate fact. Rewrite using `[if_neg (by omega), zero_mul]`. Rewrite using `[zero_add, Finset.sum_eq_single ⟨n, by omega⟩]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Rewrite using `[if_neg (fun e => hk (Fin.ext e.symm)), zero_mul]`. Simplify using the standard rewrite rules. Establish `hG : ∀ b k, σ (G b k) = σ X * σ (G (T b) k) + C (coeff k b)`. Introduce `b k`. Establish `: G b k = X * G (T b) k + C (coeff k b)` using `by conv_lhs => rw [eq_X_mul_shift_add_const (G b k)]`.

Simplify using `[G]`. Rewrite using `[this, map_add, map_mul]`. Use `congr 1`. Conclude with `σ.commutes _`. Establish `key : ∀ n, ∀ b : R⟦X⟧, X ^ n ∣ b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Introduce `b`.

Establish `: b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) = σ X * (T b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G (T b) k))`. Establish `h1` using `hT b`. Simplify using `only [hG b, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_left_comm (σ X)]`. Take the linear combination `h1`. Rewrite using `[this, pow_succ']`.

Use `mul_dvd_mul ?_ (ih _)` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `(dvd_pow_self X hs.ne').mul_left w`. Use `⟨G b, sub_eq_zero.1 ?_⟩` and prove the remaining obligations. Use extensionality with `n`.

Conclude with `X_pow_dvd_iff.1 (key (n + 1) b) n n.lt_succ_self`.
-/
theorem exists_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃ G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  let T : R⟦X⟧ → R⟦X⟧ := fun b => v * mk fun i => coeff (i + s) b
  let G : R⟦X⟧ → Fin s → R⟦X⟧ := fun b k => mk fun j => coeff k (T^[j] b)
  have hT : ∀ b : R⟦X⟧, b = σ X * T b + ∑ k : Fin s, X ^ (k : ℕ) * C (coeff k b) := by
    intro b
    have h1 : σ X * T b = X ^ s * mk fun i => coeff (i + s) b := by
      simp only [h, T]
      linear_combination (X ^ s * mk fun i => coeff (i + s) b) * hv
    rw [h1]
    ext n
    rw [map_add, coeff_X_pow_mul', map_sum]
    simp only [coeff_mul_C, coeff_X_pow, coeff_mk]
    split_ifs with hn
    · rw [Nat.sub_add_cancel hn, Finset.sum_eq_zero, add_zero]
      intro k _
      have := k.2
      rw [if_neg (by omega), zero_mul]
    · rw [zero_add, Finset.sum_eq_single ⟨n, by omega⟩]
      · simp
      · intro k _ hk
        rw [if_neg (fun e => hk (Fin.ext e.symm)), zero_mul]
      · simp
  have hG : ∀ b k, σ (G b k) = σ X * σ (G (T b) k) + C (coeff k b) := by
    intro b k
    have : G b k = X * G (T b) k + C (coeff k b) := by
      conv_lhs => rw [eq_X_mul_shift_add_const (G b k)]
      simp [G]
    rw [this, map_add, map_mul]
    congr 1
    exact σ.commutes _
  have key : ∀ n, ∀ b : R⟦X⟧, X ^ n ∣ b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      have : b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) =
          σ X * (T b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G (T b) k)) := by
        have h1 := hT b
        simp only [hG b, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_left_comm (σ X)]
        linear_combination h1
      rw [this, pow_succ']
      refine mul_dvd_mul ?_ (ih _)
      rw [h]
      exact (dvd_pow_self X hs.ne').mul_left w
  refine ⟨G b, sub_eq_zero.1 ?_⟩
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1) b) n n.lt_succ_self

/- English proof (translation)
Take `⟨G, hG⟩` from `exists_sum h hs hw b`. Use `⟨G, hG, fun G' hG' => sub_eq_zero.1 (eq_zero_of_lead h hs hw _ fun n _ => Or.inl ?_)⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, map_sub σ, mul_sub, Finset.sum_sub_distrib, ← hG, ← hG', sub_self, map_zero]`.
-/
theorem existsUnique_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃! G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨G, hG⟩ := exists_sum h hs hw b
  refine ⟨G, hG, fun G' hG' => sub_eq_zero.1 (eq_zero_of_lead h hs hw _ fun n _ => Or.inl ?_)⟩
  simp only [Pi.sub_apply, map_sub σ, mul_sub, Finset.sum_sub_distrib, ← hG, ← hG', sub_self, map_zero]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Rewrite `hx` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Conclude with `mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl) hx`.
-/
theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] (hl : (l : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl) hx

end ParamRing

open ParamRing

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ hl _ Δ _ π' w hw hπ hinv`. Establish `hs : 0 < Fintype.card ↥Δ` using `Fintype.card_pos`. Establish `hsub : HasSubst π'` using `HasSubst.of_constantCoeff_zero' (by simp [hπ, hs.ne'])`. Use `set σ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hsub with hσ`. Establish `hσa : ∀ g, subst π' g = σ g` using `fun g => (congrFun (coe_substAlgHom hsub) g).symm`.

Establish `hσX : σ X = w * X ^ Fintype.card ↥Δ` using `(substAlgHom_X hsub).trans hπ`. Establish `hfix : ∀ (d : ↥Δ) (g : O⟦X⟧), act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) (σ g) = σ g`. Introduce `d g`. Use `hinv d` as an intermediate fact. Rewrite `this` using `[act_apply]`.

Rewrite using `[← hσa, act_apply, subst_comp_subst_apply hsub (HasSubst.of_constantCoeff_zero' (cyc_const l O _)), this]`. Simplify using `only [hσa]`. Use `⟨existsUnique_sum hσX hs hw, fun b => ⟨fun hb => ?_, ?_⟩⟩` and prove the remaining obligations. Use `swap`. Introduce and unpack `⟨g, rfl⟩ d`.

Conclude with `hfix d g`. Take `⟨G, hG⟩` from `exists_sum hσX hs hw b`. Use `⟨G ⟨0, hs⟩, ?_⟩` and prove the remaining obligations. Establish `hG' : b - σ (G ⟨0, hs⟩) = ∑ k : Fin (Fintype.card ↥Δ), X ^ (k : ℕ) * σ (Function.update G ⟨0, hs⟩ 0 k)`. Rewrite using `[hG, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩), ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩)]`.

Simplify using `only [pow_zero, one_mul, Function.update_self, map_zero, zero_add, add_sub_cancel_left]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hk)]`. Establish `h0 : Function.update G ⟨0, hs⟩ 0 = 0`. Use `eq_zero_of_lead hσX hs hw _ fun n hn => ?_` and prove the remaining obligations.

Rewrite `hn`, the goal using `[← hG']`. Distinguish the cases in `hd : Fintype.card ↥Δ ∣ n`. Use `right`. Establish `: (⟨n % _, Nat.mod_lt _ hs⟩ : Fin (Fintype.card ↥Δ)) = ⟨0, hs⟩` using `Fin.ext (Nat.mod_eq_zero_of_dvd hd)`. Rewrite using `[this, Function.update_self]`.

Use `left`. Assume the negation of the conclusion as `hc`. Apply `hd` to reduce the goal to its premises. Use `haveI : IsCyclic ↥Δ := isCyclic_of_injective_ringHom ((Units.coeHom ℤ_[l]).comp Δ.subtype) (Units.val_injective.comp Subtype.val_injective)`. Take `⟨d, hd⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := ↥Δ)`.

Rewrite using `[← Nat.card_eq_fintype_card, ← hd, orderOf_dvd_iff_pow_eq_one]`. Take `⟨u, hu⟩ : (X : O⟦X⟧) ∣ cyc l O ((d : ℤ_[l]ˣ) : ℤ_[l])` from `X_dvd_iff.2 (cyc_const l O _)`. Establish `hu0 : constantCoeff u = algebraMap ℤ_[l] O ((d : ℤ_[l]ˣ) : ℤ_[l])`. Rewrite using `[← coeff_one_cyc, hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]`. Establish `h1` using `coeff_map_lead (σ := act l O ((d : ℤ_[l]ˣ) : ℤ_[l])) (w := u) (s := 1) (by rw [act_X, hu, pow_one, mul_comm]) one_pos hn`.

Rewrite `h1` using `[map_sub (act l O _), hb, hfix, one_mul, hu0, ← map_pow, eq_comm, mul_eq_right₀ hc, ← map_one (algebraMap ℤ_[l] O)]`. Establish `h2` using `algebraMap_injective l O hl h1`. Use `ext`. Simplify using `using h2`. Rewrite using `[← sub_eq_zero, hG', h0]`.

Simplify using the standard rewrite rules.
-/
theorem invariants_param : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Δ : Subgroup ℤ_[l]ˣ) [Fintype ↥Δ] (π' w : PowerSeries O), IsUnit w → π' = w * PowerSeries.X ^ Fintype.card ↥Δ → (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) π' = π') → (∀ b : PowerSeries O, ∃! G : Fin (Fintype.card ↥Δ) → PowerSeries O, b = ∑ k : Fin (Fintype.card ↥Δ), PowerSeries.X ^ (k : ℕ) * PowerSeries.subst π' (G k)) ∧ ∀ b : PowerSeries O, (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) b = b) ↔ ∃ g : PowerSeries O, b = PowerSeries.subst π' g := by
  intro l _ O _ _ _ _ _ hl _ Δ _ π' w hw hπ hinv
  have hs : 0 < Fintype.card ↥Δ := Fintype.card_pos
  have hsub : HasSubst π' := HasSubst.of_constantCoeff_zero' (by simp [hπ, hs.ne'])
  set σ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hsub with hσ
  have hσa : ∀ g, subst π' g = σ g := fun g => (congrFun (coe_substAlgHom hsub) g).symm
  have hσX : σ X = w * X ^ Fintype.card ↥Δ := (substAlgHom_X hsub).trans hπ
  have hfix : ∀ (d : ↥Δ) (g : O⟦X⟧), act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) (σ g) = σ g := by
    intro d g
    have := hinv d
    rw [act_apply] at this
    rw [← hσa, act_apply, subst_comp_subst_apply hsub
      (HasSubst.of_constantCoeff_zero' (cyc_const l O _)), this]
  simp only [hσa]
  refine ⟨existsUnique_sum hσX hs hw, fun b => ⟨fun hb => ?_, ?_⟩⟩
  swap
  · rintro ⟨g, rfl⟩ d
    exact hfix d g
  obtain ⟨G, hG⟩ := exists_sum hσX hs hw b
  refine ⟨G ⟨0, hs⟩, ?_⟩
  have hG' : b - σ (G ⟨0, hs⟩) =
      ∑ k : Fin (Fintype.card ↥Δ), X ^ (k : ℕ) * σ (Function.update G ⟨0, hs⟩ 0 k) := by
    rw [hG, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩)]
    simp only [pow_zero, one_mul, Function.update_self, map_zero, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h0 : Function.update G ⟨0, hs⟩ 0 = 0 := by
    refine eq_zero_of_lead hσX hs hw _ fun n hn => ?_
    rw [← hG'] at hn ⊢
    by_cases hd : Fintype.card ↥Δ ∣ n
    · right
      have : (⟨n % _, Nat.mod_lt _ hs⟩ : Fin (Fintype.card ↥Δ)) = ⟨0, hs⟩ :=
        Fin.ext (Nat.mod_eq_zero_of_dvd hd)
      rw [this, Function.update_self]
    left
    by_contra hc
    apply hd
    haveI : IsCyclic ↥Δ := isCyclic_of_injective_ringHom ((Units.coeHom ℤ_[l]).comp Δ.subtype)
      (Units.val_injective.comp Subtype.val_injective)
    obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Δ)
    rw [← Nat.card_eq_fintype_card, ← hd, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨u, hu⟩ : (X : O⟦X⟧) ∣ cyc l O ((d : ℤ_[l]ˣ) : ℤ_[l]) := X_dvd_iff.2 (cyc_const l O _)
    have hu0 : constantCoeff u = algebraMap ℤ_[l] O ((d : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [← coeff_one_cyc, hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    have h1 := coeff_map_lead (σ := act l O ((d : ℤ_[l]ˣ) : ℤ_[l])) (w := u) (s := 1)
      (by rw [act_X, hu, pow_one, mul_comm]) one_pos hn
    rw [map_sub (act l O _), hb, hfix, one_mul, hu0, ← map_pow, eq_comm, mul_eq_right₀ hc,
      ← map_one (algebraMap ℤ_[l] O)] at h1
    have h2 := algebraMap_injective l O hl h1
    ext
    simpa using h2
  rw [← sub_eq_zero, hG', h0]
  simp

end GlobalTheory.Cyc
