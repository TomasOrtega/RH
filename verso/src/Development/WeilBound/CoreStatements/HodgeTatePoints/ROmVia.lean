import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgrROm

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rom

/- English proof (translation)
Establish `hp2` using `hp.two_le`. Establish `hq : 2 ≤ p ^ f` using `le_trans hp2 (by`. Combine the equalities or inequalities in the displayed calculation. Use `set M := p ^ f - 1 with hM`. Use `set S := ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f) with hS`.

Establish `hpf : (p : ZMod M) ^ f = 1`. Establish `h1 : p ^ f ≡ 1 [MOD M]` using `Nat.modEq_sub (by omega)`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).2 h1` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `hcop : Nat.Coprime M (p ^ (n + 1))`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.coprime_comm, hp.coprime_iff_not_dvd]`. Introduce `hd`. Establish `h2 : p ∣ p ^ f` using `dvd_pow_self p (by omega)`.

Establish `h3 : p ∣ p ^ f - (p ^ f - 1)` using `Nat.dvd_sub h2 hd`. Establish `h4 : p ^ f - (p ^ f - 1) = 1` using `by omega`. Rewrite `h3` using `[h4]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h3)`. Establish `hmul : p ^ (n + 1) * S ≡ p ^ (n + 1) * 1 [MOD M]`.

Rewrite using `[mul_one]`. Use `Nat.ModEq.trans ?_ hc` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Use `push_cast`. Rewrite using `[hS]`.

Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `hdm` using `Nat.div_add_mod (n + f - i) f`.

Establish `hr` using `Nat.mod_lt (n + f - i) (by omega : f > 0)`. Establish `hexp : n + 1 + (f - 1 - (n + f - i) % f) = (i : ℕ) + f * ((n + f - i) / f)` using `by omega`. Rewrite using `[mul_left_comm, ← pow_add, hexp, pow_add, pow_mul, hpf, one_pow, mul_one]`. Establish `hS1 : S ≡ 1 [MOD M]` using `Nat.ModEq.cancel_left_of_coprime hcop hmul`. Establish `hS2 : 2 ≤ S`.

Use `le_trans he (Finset.sum_le_sum (fun i _ => ?_))` and prove the remaining obligations. Conclude with `Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Unfold `Nat.ModEq at hS1`.

Break down `Nat.lt_or_ge S M with h | h` into its components or cases. Rewrite `hS1` using `[Nat.mod_eq_of_lt h]`. Rewrite `hS1` using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `: S = M` using `by omega`.

Rewrite `hS1` using `[this, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem prime_pow_le_sum_mul_pow_of_modEq (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (e : Fin f → ℕ) (he : 2 ≤ ∑ i, e i)
    (hc : ∑ i, e i * p ^ (i : ℕ) ≡ p ^ (n + 1) [MOD p ^ f - 1]) :
    p ^ f ≤ ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f) := by
  have hp2 := hp.two_le
  have hq : 2 ≤ p ^ f := le_trans hp2 (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf)
  set M := p ^ f - 1 with hM
  set S := ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f) with hS
  have hpf : (p : ZMod M) ^ f = 1 := by
    have h1 : p ^ f ≡ 1 [MOD M] := Nat.modEq_sub (by omega)
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    push_cast at this
    exact this
  have hcop : Nat.Coprime M (p ^ (n + 1)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h3 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h2 hd
    have h4 : p ^ f - (p ^ f - 1) = 1 := by omega
    rw [h4] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  have hmul : p ^ (n + 1) * S ≡ p ^ (n + 1) * 1 [MOD M] := by
    rw [mul_one]
    refine Nat.ModEq.trans ?_ hc
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hS]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := i.isLt
    have hdm := Nat.div_add_mod (n + f - i) f
    have hr := Nat.mod_lt (n + f - i) (by omega : f > 0)
    have hexp : n + 1 + (f - 1 - (n + f - i) % f) = (i : ℕ) + f * ((n + f - i) / f) := by omega
    rw [mul_left_comm, ← pow_add, hexp, pow_add, pow_mul, hpf, one_pow, mul_one]
  have hS1 : S ≡ 1 [MOD M] := Nat.ModEq.cancel_left_of_coprime hcop hmul
  have hS2 : 2 ≤ S := by
    refine le_trans he (Finset.sum_le_sum (fun i _ => ?_))
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  by_contra hlt
  push_neg at hlt
  unfold Nat.ModEq at hS1
  rcases Nat.lt_or_ge S M with h | h
  · rw [Nat.mod_eq_of_lt h] at hS1
    rw [Nat.mod_eq_of_lt (by omega)] at hS1
    omega
  · have : S = M := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hS1
    omega

/- English proof (translation)
Establish `hit : ∀ t m, a m ^ (p ^ t) ≤ a (m + t)`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => intro m`. Simplify using the standard rewrite rules.

Consider the case `succ t ih`. Introduce `m`. Rewrite using `[pow_succ, pow_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hi : ∀ i : Fin f, a i ^ p ^ ((n + f - i) % f) ≤ a n`.

Introduce `i`. Use `le_trans (hit _ _) (le_of_eq ?_)` and prove the remaining obligations. Establish `hil` using `i.isLt`. Establish `hmod : ((i : ℕ) + (n + f - i) % f) % f = n % f`. Establish `h2 : (i : ℕ) + (n + f - i) % f ≡ (i : ℕ) + (n + f - i) [MOD f]` using `Nat.ModEq.add_left _ (Nat.mod_modEq _ _)`.

Establish `h3 : (i : ℕ) + (n + f - i) = n + f` using `by omega`. Rewrite `h2` using `[h3]`. Unfold `Nat.ModEq at h2`. Rewrite using `[h2, Nat.add_mod_right]`. Rewrite using `[← hper, hmod, hper]`.

Establish `hP : p ^ (f - 1) ≠ 0` using `pow_ne_zero _ (by omega)`. Rewrite using `[← pow_le_pow_iff_left₀ (zero_le) (zero_le) hP, ← Finset.prod_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod' (fun i _ => ?_)` and prove the remaining obligations. Establish `hil` using `i.isLt`.

Establish `hr` using `Nat.mod_lt (n + f - i) (by omega : f > 0)`. Establish `hsplit : p ^ (f - 1) = p ^ ((n + f - i) % f) * p ^ (f - 1 - (n + f - i) % f)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← pow_mul, hsplit, mul_left_comm, pow_mul]`. Conclude with `pow_le_pow_left₀ (zero_le) (hi i) _`. Use `_ = a n ^ (∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f)) := Finset.prod_pow_eq_pow_sum _ _ _`. Use `_ ≤ a n ^ (p ^ f) := pow_le_pow_of_le_one (zero_le) (h1 n) hS`. Use `_ = (a n ^ p) ^ p ^ (f - 1) := by`.

Rewrite using `[← pow_mul, ← pow_succ']`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
private theorem prod_pow_le_pow_of_frobenius_le (p f n : ℕ) (hp : 1 ≤ p) (hf : 1 ≤ f) (a : ℕ → NNReal) (h1 : ∀ m, a m ≤ 1)
    (hs : ∀ m, a m ^ p ≤ a (m + 1)) (hper : ∀ m, a (m % f) = a m) (e : Fin f → ℕ)
    (hS : p ^ f ≤ ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f)) :
    ∏ i : Fin f, a i ^ e i ≤ a n ^ p := by
  have hit : ∀ t m, a m ^ (p ^ t) ≤ a (m + t) := by
    intro t
    induction t with
    | zero => intro m; simp
    | succ t ih =>
      intro m
      rw [pow_succ, pow_mul]
      calc (a m ^ p ^ t) ^ p ≤ a (m + t) ^ p := pow_le_pow_left₀ (zero_le) (ih m) p
        _ ≤ a (m + t + 1) := hs _
        _ = a (m + (t + 1)) := by rw [add_assoc]
  have hi : ∀ i : Fin f, a i ^ p ^ ((n + f - i) % f) ≤ a n := by
    intro i
    refine le_trans (hit _ _) (le_of_eq ?_)
    have hil := i.isLt
    have hmod : ((i : ℕ) + (n + f - i) % f) % f = n % f := by
      have h2 : (i : ℕ) + (n + f - i) % f ≡ (i : ℕ) + (n + f - i) [MOD f] :=
        Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
      have h3 : (i : ℕ) + (n + f - i) = n + f := by omega
      rw [h3] at h2
      unfold Nat.ModEq at h2
      rw [h2, Nat.add_mod_right]
    rw [← hper, hmod, hper]
  have hP : p ^ (f - 1) ≠ 0 := pow_ne_zero _ (by omega)
  rw [← pow_le_pow_iff_left₀ (zero_le) (zero_le) hP, ← Finset.prod_pow]
  calc ∏ i : Fin f, (a i ^ e i) ^ p ^ (f - 1)
      ≤ ∏ i : Fin f, a n ^ (e i * p ^ (f - 1 - (n + f - i) % f)) := by
        refine Finset.prod_le_prod' (fun i _ => ?_)
        have hil := i.isLt
        have hr := Nat.mod_lt (n + f - i) (by omega : f > 0)
        have hsplit : p ^ (f - 1) = p ^ ((n + f - i) % f) * p ^ (f - 1 - (n + f - i) % f) := by
          rw [← pow_add]; congr 1; omega
        rw [← pow_mul, hsplit, mul_left_comm, pow_mul]
        exact pow_le_pow_left₀ (zero_le) (hi i) _
    _ = a n ^ (∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ a n ^ (p ^ f) := pow_le_pow_of_le_one (zero_le) (h1 n) hS
    _ = (a n ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']; congr 2; omega

open PositivityTheory.Xgn.A_xgr_r_om PositivityTheory.HtPt.Rb in
/- English proof (translation)
Introduce `p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard AA hst σ hσ c hc n`. Establish `hpr : p.Prime` using `hpp.out`. Establish `hp2` using `hpr.two_le`. Take `⟨hord, -, -, -, -⟩` from `GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hp F f hcard σ hσ`. Take `⟨hval, hprod⟩` from `h p C v R hv hp F f hcard AA hst σ hσ c hc`.

Use `haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj`. Establish `hf1 : 1 ≤ f`. Break down `Nat.eq_zero_or_pos f with h0 | h0` into its components or cases. Establish `h1` using `Fintype.one_lt_card (α := F)`. Rewrite `h1` using `[hcard, h0, pow_zero]`.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Take `⟨hcardne, w, hw⟩` from `exists_inv_card (F := F) hv hp hcard`. Establish `hvp : v (p : C) ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff]`.

Conclude with `hpr.ne_zero` after adjusting the coercions. Establish `hcne : ∀ m, c m ≠ 0`. Introduce `m hm`. Establish `h1` using `(hval m)`. Rewrite `h1` using `[hm, map_zero, map_zero, zero_pow (by omega)]`.

Conclude with `hvp (le_antisymm h1 (zero_le))`. Establish `hstep : ∀ m, c m ^ p ∈ Ideal.span {c (m + 1)}`. Introduce `m`. Rewrite using `[← hc (m + 1), mem_x_ideal_iff]`. Establish `h1` using `pow_mem_sq AA (σ ^ p ^ m) (c := c m) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2`.

Rewrite `h1` using `[← pow_mul, ← pow_succ]`. Conclude with `sq_le AA h1`. Establish `hper : ∀ m, σ ^ p ^ (m % f) = σ ^ p ^ m`. Introduce `m`. Rewrite using `[pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff]`.

Establish `h1 : p ^ f ≡ 1 [MOD p ^ f - 1]` using `Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))`. Establish `h2` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 h1`. Move the coercions through the operations in `at h2 ⊢`. Use `conv_rhs => rw [← Nat.mod_add_div m f, pow_add, pow_mul, h2, one_pow, mul_one]`. Use `set a : ℕ → NNReal := fun m => v (algebraMap R C (c m)) with ha`.

Establish `ha1 : ∀ m, a m ≤ 1` using `fun m => hv.map_le_one _`. Establish `has : ∀ m, a m ^ p ≤ a (m + 1)`. Introduce `m`. Establish `h1` using `hv.le_of_dvd (Ideal.mem_span_singleton.1 (hstep m))`. Simplify using `only [ha, map_pow] at h1 ⊢`.

Conclude with `h1`. Establish `haper : ∀ m, a (m % f) = a m`. Introduce `m`. Conclude with `v_eq_of_span hv (by rw [← hc, ← hc, hper])`. Establish `hE : ∀ m, 1 ≤ m → m ≤ p ^ f - 1 → ∀ e ∈ eig AA.carrier (σ ^ m), ∃ d : Fin f → Fin p, (∃ i, (d i : ℕ) ≠ 0) ∧ ∑ i : Fin f, (d i : ℕ) * p ^ (i : ℕ) = m ∧ v (e 1) ≤ ∏ i : Fin f, a i ^ (d i : ℕ)`.

Introduce `m hm1 hm2 e he`. Establish `he' : e ∈ AA.carrier ∧ ∀ (x : F) (y : F), e (x • y) = algebraMap R C ((σ ^ m) x) * e y` using `he`. Take `⟨d, hd0, hdm⟩` from `digits (p := p) (f := f) hm1 (by have := Nat.one_le_pow f p (by omega); omega)`. Use `⟨d, hd0, hdm, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `AA.le_int he'.1 1`.

Establish `hfun : (fun x : F => algebraMap R C (t * (σ ^ m) x)) = e`. Use function extensionality and compare the values at `x`. Use `he'.2 x 1` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, mul_one]`. Rewrite using `[this, ← ht, map_mul, mul_comm]`.

Establish `htm : t ∈ xIdeal AA.carrier (σ ^ m)`. Rewrite using `[mem_x_ideal_iff, hfun]`. Conclude with `he'.1`. Rewrite `htm` using `[← hdm, hprod d hd0]`. Rewrite using `[← ht]`.

Use `le_trans (v_le_of_mem hv htm) (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [ha, map_prod, map_pow]`. Use `set χ : MulChar F R := σ ^ p ^ (n + 1) with hχdef`. Use `set L : (F → C) →ₗ[R] C := (LinearMap.proj (R := R) (φ := fun _ : F => C) (1 : F)).comp (projL χ) with hL`. Establish `hLapp : ∀ g, L g = proj χ g 1`.

Introduce `g`. Simplify using `[hL, projL_apply]`. Establish `hbound : ∀ g ∈ augIdeal AA.carrier, ∀ g' ∈ augIdeal AA.carrier, v (L (g * g')) ≤ a n ^ p`. Introduce `g hg g' hg'`. Take `⟨hPg, hsum, -⟩` from `proj_props p C v R hv hp F f hcard F AA hst σ hσ g hg`.

Take `⟨hPg', hsum', -⟩` from `proj_props p C v R hv hp F f hcard F AA hst σ hσ g' hg'`. Establish `hgg : g * g' = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), ∑ m' ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g * proj (σ ^ m') g'` using `by conv_lhs => rw [hsum, hsum']`. Rewrite using `[Finset.sum_mul_sum]`. Rewrite using `[hgg, map_sum]`. Use `Valuation.map_sum_le _ (fun m hm => ?_)` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Valuation.map_sum_le _ (fun m' hm' => ?_)` and prove the remaining obligations. Rewrite `hm`, `hm'` using `[Finset.mem_Icc]`. Establish `e1 : proj (σ ^ m) g ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m) g (x • y) = algebraMap R C ((σ ^ m) x) * proj (σ ^ m) g y` using `hPg (σ ^ m)`. Establish `e2 : proj (σ ^ m') g' ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m') g' (x • y) = algebraMap R C ((σ ^ m') x) * proj (σ ^ m') g' y` using `hPg' (σ ^ m')`.

Establish `heig : ∀ (x : F) (y : F), (proj (σ ^ m) g * proj (σ ^ m') g') (x • y) = algebraMap R C ((σ ^ m * σ ^ m') x) * (proj (σ ^ m) g * proj (σ ^ m') g') y`. Introduce `x y`. Simplify using `only [Pi.mul_apply, e1.2, e2.2, MulChar.mul_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hχ : σ ^ m * σ ^ m' = χ`.

Rewrite using `[hLapp, proj_eigen_self hcardne χ _ (by rw [← hχ]; exact heig), Pi.mul_apply, map_mul]`. Take `⟨d, hd0, hdm, hdv⟩` from `hE m hm.1 hm.2 _ (hPg (σ ^ m))`. Take `⟨d', hd0', hdm', hdv'⟩` from `hE m' hm'.1 hm'.2 _ (hPg' (σ ^ m'))`. Use `le_trans (mul_le_mul' hdv hdv') ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Simplify using `only [← pow_add]`. Use `prod_pow_le_pow_of_frobenius_le p f n (by omega) hf1 a ha1 has haper (fun i => (d i : ℕ) + d' i) ?_` and prove the remaining obligations. Use `prime_pow_le_sum_mul_pow_of_modEq p f n hpr hf1 _ ?_ ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hd0`. Take `⟨i', hi'⟩` from `hd0'`.

Rewrite using `[Finset.sum_add_distrib]`. Establish `h1` using `Finset.single_le_sum (f := fun j => ((d j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `h2` using `Finset.single_le_sum (f := fun j => ((d' j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i')`. Use linear arithmetic over natural numbers and integers. Simplify using `only [add_mul, Finset.sum_add_distrib, hdm, hdm']`.

Rewrite using `[← hord, ← pow_eq_pow_iff_modEq, pow_add, hχ]`. Rewrite using `[hLapp, proj_eigen_ne (Ne.symm hχ) _ heig]`. Simplify using the standard rewrite rules. Establish `hsqn : (fun x : F => algebraMap R C (c n ^ p * χ x)) ∈ sqIdeal (augIdeal AA.carrier)`. Establish `h1` using `pow_mem_sq AA (σ ^ p ^ n) (c := c n) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2`.

Rewrite `h1` using `[← pow_mul, ← pow_succ]`. Conclude with `h1`. Establish `hP1 : ∀ r : R, (fun x : F => algebraMap R C (r * χ x)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}`. Introduce `r`. Prove the components needed by the constructor for the conclusion.

Introduce `hr`. Establish `h1` using `sq_bound hv (augIdeal AA.carrier : Set (F → C)) L (a n ^ p) (fun g hg g' hg' => hbound g hg g' hg') _ (by rwa [Submodule.span_eq])`. Rewrite `h1` using `[hLapp, proj_eigen_self hcardne χ _ (fun x y => eig_fun χ r x y), MulChar.map_one, mul_one]`. Rewrite using `[Ideal.mem_span_singleton]`. Use `hv.dvd_of_le ?_` and prove the remaining obligations.

Simplify `h1` using `[ha, map_pow]`. Introduce `hr`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Establish `: (fun x : F => algebraMap R C (s * c n ^ p * χ x)) = s • (fun x : F => algebraMap R C (c n ^ p * χ x))`. Use function extensionality and compare the values at `x`.

Simplify using `[Algebra.smul_def, mul_assoc]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hsqn`. Use `⟨hP1, ?_, ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ⟩` from `Ideal.mem_span_singleton'.1 (hstep n)`.

Conclude with `⟨δ, hδ.symm⟩`. Introduce `δ hδ set e0 : F → C := fun x => algebraMap R C (c (n + 1) * χ x) with he0def`. Establish `he0 : e0 ∈ eig AA.carrier χ` using `by show e0 ∈ AA.carrier ∧ ∀ (x y : F), e0 (x • y) = algebraMap R C (χ x) * e0 y`. Conclude with `⟨(mem_x_ideal_iff _ _ _).1 (by rw [hc]; exact Ideal.mem_span_singleton_self _), fun x y => eig_fun χ _ x y⟩`. Set `φ : R →ₗ[R] OmType AA.carrier χ` to `(Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ (⟨e0, he0⟩ : eig AA.carrier χ))`.

Establish `hφ : ∀ r, φ r = Submodule.Quotient.mk (r • (⟨e0, he0⟩ : eig AA.carrier χ))` using `fun r => rfl`. Use `hasLen_quot v φ ?_ δ ?_` and prove the remaining obligations. Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H y`.

Take `⟨y, hy⟩` from `y`. Establish `hy' : y ∈ AA.carrier ∧ ∀ (x z : F), y (x • z) = algebraMap R C (χ x) * y z` using `hy`. Take `⟨t, ht⟩` from `AA.le_int hy'.1 1`. Establish `hfun : (fun x : F => algebraMap R C (t * χ x)) = y`. Use function extensionality and compare the values at `x`.

Use `hy'.2 x 1` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, mul_one]`. Rewrite using `[this, ← ht, map_mul, mul_comm]`. Establish `htm : t ∈ xIdeal AA.carrier χ`. Rewrite using `[mem_x_ideal_iff, hfun]`.

Conclude with `hy'.1`. Rewrite `htm` using `[hc]`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 htm`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((s • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) = y`. Rewrite using `[← hfun]`. Use function extensionality and compare the values at `x`.

Simplify using `[he0def, Algebra.smul_def, mul_assoc]`. Use extensionality with `r`. Rewrite using `[LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Establish `hfun : ((r • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) = (fun x : F => algebraMap R C (r * c (n + 1) * χ x))`. Use function extensionality and compare the values at `x`.

Simplify using `[he0def, Algebra.smul_def, mul_assoc]`. Rewrite using `[Submodule.subtype_apply, hfun, hP1, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton, mul_dvd_mul_iff_right (hcne (n + 1))]`.
-/
theorem r_om_of (h : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_powers) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard AA hst σ hσ c hc n
  have hpr : p.Prime := hpp.out
  have hp2 := hpr.two_le
  obtain ⟨hord, -, -, -, -⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hp F f hcard σ hσ
  obtain ⟨hval, hprod⟩ := h p C v R hv hp F f hcard AA hst σ hσ c hc
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 := Fintype.one_lt_card (α := F)
      rw [hcard, h0, pow_zero] at h1
      omega
    · exact h0
  obtain ⟨hcardne, w, hw⟩ := exists_inv_card (F := F) hv hp hcard
  have hvp : v (p : C) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hpr.ne_zero
  have hcne : ∀ m, c m ≠ 0 := by
    intro m hm
    have h1 := (hval m)
    rw [hm, map_zero, map_zero, zero_pow (by omega)] at h1
    exact hvp (le_antisymm h1 (zero_le))
  have hstep : ∀ m, c m ^ p ∈ Ideal.span {c (m + 1)} := by
    intro m
    rw [← hc (m + 1), mem_x_ideal_iff]
    have h1 := pow_mem_sq AA (σ ^ p ^ m) (c := c m) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2
    rw [← pow_mul, ← pow_succ] at h1
    exact sq_le AA h1
  have hper : ∀ m, σ ^ p ^ (m % f) = σ ^ p ^ m := by
    intro m
    rw [pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff]
    have h1 : p ^ f ≡ 1 [MOD p ^ f - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    push_cast at h2 ⊢
    conv_rhs => rw [← Nat.mod_add_div m f, pow_add, pow_mul, h2, one_pow, mul_one]
  set a : ℕ → NNReal := fun m => v (algebraMap R C (c m)) with ha
  have ha1 : ∀ m, a m ≤ 1 := fun m => hv.map_le_one _
  have has : ∀ m, a m ^ p ≤ a (m + 1) := by
    intro m
    have h1 := hv.le_of_dvd (Ideal.mem_span_singleton.1 (hstep m))
    simp only [ha, map_pow] at h1 ⊢
    exact h1
  have haper : ∀ m, a (m % f) = a m := by
    intro m
    exact v_eq_of_span hv (by rw [← hc, ← hc, hper])
  have hE : ∀ m, 1 ≤ m → m ≤ p ^ f - 1 → ∀ e ∈ eig AA.carrier (σ ^ m), ∃ d : Fin f → Fin p,
      (∃ i, (d i : ℕ) ≠ 0) ∧ ∑ i : Fin f, (d i : ℕ) * p ^ (i : ℕ) = m ∧
      v (e 1) ≤ ∏ i : Fin f, a i ^ (d i : ℕ) := by
    intro m hm1 hm2 e he
    have he' : e ∈ AA.carrier ∧ ∀ (x : F) (y : F), e (x • y) = algebraMap R C ((σ ^ m) x) * e y := he
    obtain ⟨d, hd0, hdm⟩ := digits (p := p) (f := f) hm1 (by have := Nat.one_le_pow f p (by omega); omega)
    refine ⟨d, hd0, hdm, ?_⟩
    obtain ⟨t, ht⟩ := AA.le_int he'.1 1
    have hfun : (fun x : F => algebraMap R C (t * (σ ^ m) x)) = e := by
      funext x
      have := he'.2 x 1
      rw [smul_eq_mul, mul_one] at this
      rw [this, ← ht, map_mul, mul_comm]
    have htm : t ∈ xIdeal AA.carrier (σ ^ m) := by
      rw [mem_x_ideal_iff, hfun]; exact he'.1
    rw [← hdm, hprod d hd0] at htm
    rw [← ht]
    refine le_trans (v_le_of_mem hv htm) (le_of_eq ?_)
    simp only [ha, map_prod, map_pow]
  set χ : MulChar F R := σ ^ p ^ (n + 1) with hχdef
  set L : (F → C) →ₗ[R] C := (LinearMap.proj (R := R) (φ := fun _ : F => C) (1 : F)).comp (projL χ) with hL
  have hLapp : ∀ g, L g = proj χ g 1 := by
    intro g; simp [hL, projL_apply]
  have hbound : ∀ g ∈ augIdeal AA.carrier, ∀ g' ∈ augIdeal AA.carrier, v (L (g * g')) ≤ a n ^ p := by
    intro g hg g' hg'
    obtain ⟨hPg, hsum, -⟩ := proj_props p C v R hv hp F f hcard F AA hst σ hσ g hg
    obtain ⟨hPg', hsum', -⟩ := proj_props p C v R hv hp F f hcard F AA hst σ hσ g' hg'
    have hgg : g * g' = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), ∑ m' ∈ Finset.Icc 1 (p ^ f - 1),
        proj (σ ^ m) g * proj (σ ^ m') g' := by
      conv_lhs => rw [hsum, hsum']
      rw [Finset.sum_mul_sum]
    rw [hgg, map_sum]
    refine Valuation.map_sum_le _ (fun m hm => ?_)
    rw [map_sum]
    refine Valuation.map_sum_le _ (fun m' hm' => ?_)
    rw [Finset.mem_Icc] at hm hm'
    have e1 : proj (σ ^ m) g ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m) g (x • y) = algebraMap R C ((σ ^ m) x) * proj (σ ^ m) g y := hPg (σ ^ m)
    have e2 : proj (σ ^ m') g' ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m') g' (x • y) = algebraMap R C ((σ ^ m') x) * proj (σ ^ m') g' y := hPg' (σ ^ m')
    have heig : ∀ (x : F) (y : F), (proj (σ ^ m) g * proj (σ ^ m') g') (x • y) =
        algebraMap R C ((σ ^ m * σ ^ m') x) * (proj (σ ^ m) g * proj (σ ^ m') g') y := by
      intro x y
      simp only [Pi.mul_apply, e1.2, e2.2, MulChar.mul_apply, map_mul]
      ring
    by_cases hχ : σ ^ m * σ ^ m' = χ
    · rw [hLapp, proj_eigen_self hcardne χ _ (by rw [← hχ]; exact heig), Pi.mul_apply, map_mul]
      obtain ⟨d, hd0, hdm, hdv⟩ := hE m hm.1 hm.2 _ (hPg (σ ^ m))
      obtain ⟨d', hd0', hdm', hdv'⟩ := hE m' hm'.1 hm'.2 _ (hPg' (σ ^ m'))
      refine le_trans (mul_le_mul' hdv hdv') ?_
      rw [← Finset.prod_mul_distrib]
      simp only [← pow_add]
      refine prod_pow_le_pow_of_frobenius_le p f n (by omega) hf1 a ha1 has haper (fun i => (d i : ℕ) + d' i) ?_
      refine prime_pow_le_sum_mul_pow_of_modEq p f n hpr hf1 _ ?_ ?_
      · obtain ⟨i, hi⟩ := hd0
        obtain ⟨i', hi'⟩ := hd0'
        rw [Finset.sum_add_distrib]
        have h1 := Finset.single_le_sum (f := fun j => ((d j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have h2 := Finset.single_le_sum (f := fun j => ((d' j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i')
        omega
      · simp only [add_mul, Finset.sum_add_distrib, hdm, hdm']
        rw [← hord, ← pow_eq_pow_iff_modEq, pow_add, hχ]
    · rw [hLapp, proj_eigen_ne (Ne.symm hχ) _ heig]
      simp
  have hsqn : (fun x : F => algebraMap R C (c n ^ p * χ x)) ∈ sqIdeal (augIdeal AA.carrier) := by
    have h1 := pow_mem_sq AA (σ ^ p ^ n) (c := c n) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2
    rw [← pow_mul, ← pow_succ] at h1
    exact h1
  have hP1 : ∀ r : R, (fun x : F => algebraMap R C (r * χ x)) ∈ sqIdeal (augIdeal AA.carrier) ↔
      r ∈ Ideal.span {c n ^ p} := by
    intro r
    constructor
    · intro hr
      have h1 := sq_bound hv (augIdeal AA.carrier : Set (F → C)) L (a n ^ p)
        (fun g hg g' hg' => hbound g hg g' hg') _ (by rwa [Submodule.span_eq])
      rw [hLapp, proj_eigen_self hcardne χ _ (fun x y => eig_fun χ r x y), MulChar.map_one, mul_one] at h1
      rw [Ideal.mem_span_singleton]
      refine hv.dvd_of_le ?_
      simpa [ha, map_pow] using h1
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      have : (fun x : F => algebraMap R C (s * c n ^ p * χ x)) = s • (fun x : F => algebraMap R C (c n ^ p * χ x)) := by
        funext x; simp [Algebra.smul_def, mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ _ hsqn
  refine ⟨hP1, ?_, ?_⟩
  · obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    exact ⟨δ, hδ.symm⟩
  · intro δ hδ
    set e0 : F → C := fun x => algebraMap R C (c (n + 1) * χ x) with he0def
    have he0 : e0 ∈ eig AA.carrier χ := by
      show e0 ∈ AA.carrier ∧ ∀ (x y : F), e0 (x • y) = algebraMap R C (χ x) * e0 y
      exact ⟨(mem_x_ideal_iff _ _ _).1 (by rw [hc]; exact Ideal.mem_span_singleton_self _),
        fun x y => eig_fun χ _ x y⟩
    let φ : R →ₗ[R] OmType AA.carrier χ :=
      (Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ (⟨e0, he0⟩ : eig AA.carrier χ))
    have hφ : ∀ r, φ r = Submodule.Quotient.mk (r • (⟨e0, he0⟩ : eig AA.carrier χ)) := fun r => rfl
    refine hasLen_quot v φ ?_ δ ?_
    · intro x
      induction x using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨y, hy⟩ := y
        have hy' : y ∈ AA.carrier ∧ ∀ (x z : F), y (x • z) = algebraMap R C (χ x) * y z := hy
        obtain ⟨t, ht⟩ := AA.le_int hy'.1 1
        have hfun : (fun x : F => algebraMap R C (t * χ x)) = y := by
          funext x
          have := hy'.2 x 1
          rw [smul_eq_mul, mul_one] at this
          rw [this, ← ht, map_mul, mul_comm]
        have htm : t ∈ xIdeal AA.carrier χ := by
          rw [mem_x_ideal_iff, hfun]; exact hy'.1
        rw [hc] at htm
        obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 htm
        refine ⟨s, ?_⟩
        rw [hφ]
        congr 1
        apply Subtype.ext
        show ((s • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) = y
        rw [← hfun]
        funext x
        simp [he0def, Algebra.smul_def, mul_assoc]
    · ext r
      rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      have hfun : ((r • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) =
          (fun x : F => algebraMap R C (r * c (n + 1) * χ x)) := by
        funext x
        simp [he0def, Algebra.smul_def, mul_assoc]
      rw [Submodule.subtype_apply, hfun, hP1, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        mul_dvd_mul_iff_right (hcne (n + 1))]

end PositivityTheory.HtPt.Rom
