import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

/- English proof (translation)
Set `e : (Fin f → Fin p) ≃ (Fin f → Fin p)` to `Equiv.arrowCongr (Equiv.refl _) Fin.revPerm`. Establish `h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ)` using `e.sum_comp (fun d => (d j : ℕ))`. Establish `h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1)`. Introduce `d`. Simplify using `[e, Equiv.arrowCongr_apply, Fin.val_rev]`.

Simplify using `only [h2] at h1`. Rewrite using `[mul_two]`. Use `nth_rewrite 2 [← h1]`. Rewrite using `[← Finset.sum_add_distrib]`. Establish `h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1`.

Introduce `d`. Use `(d j).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]`.
-/
lemma two_mul_sum_digit (p f : ℕ) (j : Fin f) :
    (∑ d : Fin f → Fin p, (d j : ℕ)) * 2 = p ^ f * (p - 1) := by
  let e : (Fin f → Fin p) ≃ (Fin f → Fin p) := Equiv.arrowCongr (Equiv.refl _) Fin.revPerm
  have h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ) :=
    e.sum_comp (fun d => (d j : ℕ))
  have h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1) := by
    intro d
    simp [e, Equiv.arrowCongr_apply, Fin.val_rev]
  simp only [h2] at h1
  rw [mul_two]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  have h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1 := by
    intro d; have := (d j).2; omega
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1))`. Introduce `j`. Rewrite using `[Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma prod_digit_sq (p f : ℕ) (x : Fin f → NNReal) :
    (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2 = (∏ j, x j) ^ (p ^ f * (p - 1)) := by
  have key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1)) := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]
  calc (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2
      = (∏ j, ∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := by rw [Finset.prod_comm]
    _ = ∏ j, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := (Finset.prod_pow _ _ _).symm
    _ = ∏ j, x j ^ (p ^ f * (p - 1)) := Finset.prod_congr rfl (fun j _ => key j)
    _ = (∏ j, x j) ^ (p ^ f * (p - 1)) := Finset.prod_pow _ _ _

def num {p f : ℕ} (d : Fin f → Fin p) : ℕ := ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)

/- English proof (translation)
Rewrite using `[num, finFunctionFinEquiv_apply]`.
-/
lemma num_eq {p f : ℕ} (d : Fin f → Fin p) : num d = (finFunctionFinEquiv d : ℕ) := by
  rw [num, finFunctionFinEquiv_apply]

/- English proof (translation)
Rewrite using `[num_eq]`. Conclude with `Fin.isLt _`.
-/
lemma num_lt {p f : ℕ} (d : Fin f → Fin p) : num d < p ^ f := by
  rw [num_eq]; exact Fin.isLt _

/- English proof (translation)
Rewrite `h` using `[num_eq, num_eq]`. Conclude with `finFunctionFinEquiv.injective (Fin.ext h)`.
-/
lemma num_inj {p f : ℕ} {d e : Fin f → Fin p} (h : num d = num e) : d = e := by
  rw [num_eq, num_eq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩`.
-/
lemma num_surj {p f m : ℕ} (h : m < p ^ f) : ∃ d : Fin f → Fin p, num d = m :=
  ⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Establish `hc' : ∀ n, (d n : ℕ) = 0` using `fun n => by_contra (fun hn => hc ⟨n, hn⟩)`. Apply `h` to reduce the goal to its premises.

Simplify using `[num, hc']`. Introduce and unpack `⟨n, hn⟩ h`. Apply `hn` to reduce the goal to its premises. Rewrite `h` using `[num]`. Establish `h'` using `(Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)`.

Break down `mul_eq_zero.mp h' with h'' | h''` into its components or cases. Conclude with `h''`. Conclude with `absurd h'' (pow_ne_zero _ hp.ne')`.
-/
lemma num_ne_zero_iff {p f : ℕ} (hp : 0 < p) (d : Fin f → Fin p) :
    num d ≠ 0 ↔ ∃ n, (d n : ℕ) ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ n, (d n : ℕ) = 0 := fun n => by_contra (fun hn => hc ⟨n, hn⟩)
    apply h
    simp [num, hc']
  · rintro ⟨n, hn⟩ h
    apply hn
    rw [num] at h
    have h' := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (pow_ne_zero _ hp.ne')

/- English proof (translation)
Establish `hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d` using `Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))`. Rewrite using `[← hfilt]`. Use `symm`. Use `Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `d hd`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hd`. Use `num_lt d` as an intermediate fact. Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Introduce `a _ b _ h`.

Conclude with `num_inj h`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_Icc]`. Take `⟨d, hd⟩` from `num_surj (p := p) (f := f) (show m < p ^ f by omega)`. Use `⟨d, ?_, hd⟩` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Introduce `d hd`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hd`. Conclude with `(h1 d hd).symm`.
-/
lemma prod_Icc_num {M : Type} [CommMonoid M] {p f : ℕ} (hp : 0 < p) (g : ℕ → M)
    (G : (Fin f → Fin p) → M) (h0 : ∀ d, num d = 0 → G d = 1)
    (h1 : ∀ d, num d ≠ 0 → g (num d) = G d) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), g m = ∏ d, G d := by
  classical
  have hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d :=
    Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))
  rw [← hfilt]
  symm
  refine Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have := num_lt d
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    exact num_inj h
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨d, hd⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact (h1 d hd).symm

/- English proof (translation)
Establish `hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n` using `fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a`. Rewrite using `[MulChar.pow_apply' σ hd a]`. Simplify using `only [hpow']`. Simplify using `only [map_mul, map_pow, map_prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]`.

Use `congr 2`. Conclude with `Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)`.
-/
lemma mono_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F] {p f : ℕ}
    (hp : 0 < p) (σ : MulChar F R) (c : ℕ → R) (d : Fin f → Fin p) (hd : num d ≠ 0) (a : F) :
    ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) =
      algebraMap R C ((∏ n : Fin f, c n ^ (d n : ℕ)) * (σ ^ num d) a) := by
  have hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n :=
    fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a
  rw [MulChar.pow_apply' σ hd a]
  simp only [hpow']
  simp only [map_mul, map_pow, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]
  congr 2
  exact Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `(num_ne_zero_iff hp d).2 ⟨n, h⟩ hd`.
-/
lemma digits_zero {p f : ℕ} (hp : 0 < p) {d : Fin f → Fin p} (hd : num d = 0) (n : Fin f) :
    (d n : ℕ) = 0 := by
  by_contra h
  exact (num_ne_zero_iff hp d).2 ⟨n, h⟩ hd

end GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

open GlobalTheory.CompanionTheory.Ar.GR.RankOneColen in

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `hT` using `GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧ ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by`. Use `⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩` and prove the remaining obligations.

Introduce `m dsimp only`. Distinguish the cases in `h : m ≠ 0 ∧ m < p ^ f`. Rewrite using `[dif_pos h]`. Establish `hd` using `Classical.choose_spec (num_surj h.2)`. Establish `hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0` using `(num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)`.

Establish `e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2))` using `by rw [hd]`. Rewrite using `[e]`. Conclude with `hT.2 _ hne`. Rewrite using `[dif_neg h]`. Conclude with `(Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2`.

Introduce `d hd dsimp only`. Establish `h : num d ≠ 0 ∧ num d < p ^ f` using `⟨hd, num_lt d⟩`. Rewrite using `[dif_pos h]`. Use `num_inj (Classical.choose_spec (num_surj h.2))` as an intermediate fact. Rewrite using `[this]`.

Take `⟨hAug, hCar, hCol⟩` from `r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hset : Set.range (fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) = insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1)))`. Use extensionality with `g`. Simplify using `only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, rfl⟩`. Distinguish the cases in `h0 : num d = 0`. Use `left`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.one_apply]`. Conclude with `Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])`. Use `right`. Use `⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Rewrite using `[mono_eq hp σ c d h0 a, hc'd d h0]`. Introduce and unpack `(rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)`. Use `⟨fun _ => ⟨0, hp⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.one_apply]`.

Conclude with `Finset.prod_eq_one (fun n _ => pow_zero _)`. Take `⟨d, rfl⟩` from `num_surj (p := p) (f := f) (show m < p ^ f by omega)`. Establish `h0 : num d ≠ 0` using `by omega`. Use `⟨d, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Rewrite using `[mono_eq hp σ c d h0 a, hc'd d h0]`. Rewrite using `[hset, Submodule.span_insert, ← hAug, ← hCar]`. Introduce `cN hcN`. Establish `huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m))`. Take `⟨B, hB, hBd⟩` from `hcN`.

Take `⟨B', hB', hB'd⟩` from `hCol`. Take `⟨P, hPu, hP⟩` from `AA.lat`. Rewrite using `[← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB), valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]`. Rewrite using `[huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m))) (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]`. Conclude with `prod_digit_sq p f (fun n => v (algebraMap R C (c n)))`.

Introduce `d hd`. Conclude with `Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])`. Introduce `d hd`. Simplify using `only [hc'd d hd, map_prod, map_pow]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hT := GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc
  obtain ⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧
      ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by
    refine ⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then
        ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ)
      else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩
    · intro m
      dsimp only
      by_cases h : m ≠ 0 ∧ m < p ^ f
      · rw [dif_pos h]
        have hd := Classical.choose_spec (num_surj h.2)
        have hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0 :=
          (num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)
        have e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2)) := by rw [hd]
        rw [e]
        exact hT.2 _ hne
      · rw [dif_neg h]
        exact (Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2
    · intro d hd
      dsimp only
      have h : num d ≠ 0 ∧ num d < p ^ f := ⟨hd, num_lt d⟩
      rw [dif_pos h]
      have := num_inj (Classical.choose_spec (num_surj h.2))
      rw [this]
  obtain ⟨hAug, hCar, hCol⟩ := r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'
  refine ⟨?_, ?_⟩
  · have hset : Set.range (fun (d : Fin f → Fin p) (a : F) =>
          ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) =
        insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1))) := by
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨d, rfl⟩
        by_cases h0 : num d = 0
        · left
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])
        · right
          refine ⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
      · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
        · refine ⟨fun _ => ⟨0, hp⟩, ?_⟩
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => pow_zero _)
        · obtain ⟨d, rfl⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
          have h0 : num d ≠ 0 := by omega
          refine ⟨d, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
    rw [hset, Submodule.span_insert, ← hAug, ← hCar]
  · intro cN hcN
    have huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m)) := by
      obtain ⟨B, hB, hBd⟩ := hcN
      obtain ⟨B', hB', hB'd⟩ := hCol
      obtain ⟨P, hPu, hP⟩ := AA.lat
      rw [← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB),
        valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]
    rw [huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m)))
      (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]
    · exact prod_digit_sq p f (fun n => v (algebraMap R C (c n)))
    · intro d hd
      exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])
    · intro d hd
      simp only [hc'd d hd, map_prod, map_pow]
