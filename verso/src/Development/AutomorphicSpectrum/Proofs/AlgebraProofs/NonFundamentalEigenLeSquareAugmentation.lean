import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.NonFund

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N)

/- English proof (translation)
Use `⟨AA.mul_mem _ _ hg.1 hh, ?_⟩` and prove the remaining obligations. Establish `h0 : g 0 = 0` using `hg.2`. Express the relevant statement in the definitionally equal form `g 0 * h 0 = 0`. Rewrite using `[h0, zero_mul]`.
-/
theorem aug_mul {g h : N → C} (hg : g ∈ augIdeal AA.carrier) (hh : h ∈ AA.carrier) :
    g * h ∈ augIdeal AA.carrier := by
  refine ⟨AA.mul_mem _ _ hg.1 hh, ?_⟩
  have h0 : g 0 = 0 := hg.2
  change g 0 * h 0 = 0
  rw [h0, zero_mul]

/- English proof (translation)
Unfold `sqIdeal at hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, b, hb, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨a, ha, b * h, aug_mul AA hb hh, mul_assoc _ _ _⟩`.

Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem sq_mul {g h : N → C} (hg : g ∈ sqIdeal (augIdeal AA.carrier)) (hh : h ∈ AA.carrier) :
    g * h ∈ sqIdeal (augIdeal AA.carrier) := by
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, b * h, aug_mul AA hb hh, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def Lev (k : ℕ) (g : N → C) : Prop :=
  g ∈ AA.carrier ∧ (1 ≤ k → g ∈ augIdeal AA.carrier) ∧
    (2 ≤ k → g ∈ sqIdeal (augIdeal AA.carrier))

/- English proof (translation)
Assemble the required witnesses or components as `⟨AA.one_mem, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩`.
-/
theorem lev_one : Lev AA 0 1 :=
  ⟨AA.one_mem, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/- English proof (translation)
Use `⟨AA.mul_mem _ _ hg.1 hh.1, fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : 1 ≤ k`. Conclude with `aug_mul AA (hg.2.1 h1) hh.1`. Rewrite using `[mul_comm]; exact aug_mul AA (hh.2.1 (by omega)) hg.1`. Distinguish the cases in `h2 : 2 ≤ k`.

Conclude with `sq_mul AA (hg.2.2 h2) hh.1`. Distinguish the cases in `h3 : 2 ≤ l`. Rewrite using `[mul_comm]`. Conclude with `sq_mul AA (hh.2.2 h3) hg.1`. Conclude with `Submodule.subset_span ⟨g, hg.2.1 (by omega), h, hh.2.1 (by omega), rfl⟩`.
-/
theorem lev_mul {k l : ℕ} {g h : N → C} (hg : Lev AA k g) (hh : Lev AA l h) :
    Lev AA (k + l) (g * h) := by
  refine ⟨AA.mul_mem _ _ hg.1 hh.1, fun hk => ?_, fun hk => ?_⟩
  · by_cases h1 : 1 ≤ k
    · exact aug_mul AA (hg.2.1 h1) hh.1
    · rw [mul_comm]; exact aug_mul AA (hh.2.1 (by omega)) hg.1
  · by_cases h2 : 2 ≤ k
    · exact sq_mul AA (hg.2.2 h2) hh.1
    · by_cases h3 : 2 ≤ l
      · rw [mul_comm]; exact sq_mul AA (hh.2.2 h3) hg.1
      · exact Submodule.subset_span ⟨g, hg.2.1 (by omega), h, hh.2.1 (by omega), rfl⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `lev_one AA`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Conclude with `lev_mul AA ih ⟨hg.1, fun _ => hg, fun h => absurd h (by omega)⟩`.
-/
theorem lev_pow {g : N → C} (hg : g ∈ augIdeal AA.carrier) (k : ℕ) : Lev AA k (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact lev_one AA
  | succ k ih =>
    rw [pow_succ]
    exact lev_mul AA ih ⟨hg.1, fun _ => hg, fun h => absurd h (by omega)⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty]`. Conclude with `lev_one AA`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`.

Conclude with `lev_mul AA (lev_pow AA (hu a) _) ih`.
-/
theorem lev_prod {ι : Type} (s : Finset ι) (u : ι → N → C) (hu : ∀ i, u i ∈ augIdeal AA.carrier)
    (d : ι → ℕ) : Lev AA (∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact lev_one AA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact lev_mul AA (lev_pow AA (hu a) _) ih

/- English proof (translation)
Establish `h` using `Finset.add_sum_erase Finset.univ d (Finset.mem_univ n)`. Establish `h1 : d n = 1` using `by omega`. Establish `h0 : ∑ i ∈ Finset.univ.erase n, d i = 0` using `by omega`. Rewrite `h0` using `[Finset.sum_eq_zero_iff]`. Rewrite using `[Finset.sum_eq_single n, h1, one_mul]`.

Introduce `b _ hb`. Rewrite using `[h0 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ n) h`.
-/
theorem digits_single {f p : ℕ} (d : Fin f → ℕ) (n : Fin f) (hn : d n ≠ 0)
    (hs : ¬ 2 ≤ ∑ i, d i) : ∑ i : Fin f, d i * p ^ (i : ℕ) = p ^ (n : ℕ) := by
  have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ n)
  have h1 : d n = 1 := by omega
  have h0 : ∑ i ∈ Finset.univ.erase n, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.sum_eq_single n, h1, one_mul]
  · intro b _ hb
    rw [h0 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩), zero_mul]
  · intro h; exact absurd (Finset.mem_univ n) h

end GlobalTheory.CompanionTheory.Ar.GR.NonFund

open GlobalTheory.CompanionTheory.Ar.GR.NonFund in
/- English proof (translation)
Introduce `p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hc AA hA χ hχ g hg`. Take `⟨σ, hσ⟩` from `fund_ex_relay p C v R hv hp F f hc`. Take `⟨-, hgen, hfund, -, -⟩` from `FundGen.main p C v R hv hp F f hc σ hσ`. Take `⟨m, hm1, hm2, rfl⟩` from `hgen χ`. Establish `hr` using `eig_rank_one p C v R hv hp F f hc AA hA`.

Use `choose c hc0 hcx using fun n : ℕ => (hr (σ ^ p ^ n)).1`. Establish `hp0 : 0 < p` using `hpp.out.pos`. Establish `hlt : m < p ^ f`. Use `pow_pos hp0 f` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : Fin f → Fin p, ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by`. Use `⟨finFunctionFinEquiv.symm ⟨m, hlt⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]`. Establish `hne : ∃ n, (d n : ℕ) ≠ 0`. Assume the negation of the conclusion as `hcon`.

Establish `h0 : ∀ n, (d n : ℕ) = 0` using `fun n => by`. Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨n, h⟩`. Simplify using `only [h0, zero_mul, Finset.sum_const_zero] at hd`. Use linear arithmetic over natural numbers and integers.

Establish `hx` using `(GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hc AA hA σ hσ c hcx).2 d hne`. Rewrite `hx` using `[hd]`. Establish `hs : 2 ≤ ∑ n, (d n : ℕ)`. Assume the negation of the conclusion as `hs`. Take `⟨n, hn⟩` from `hne`.

Use `digits_single (p := p) (fun n => (d n : ℕ)) n hn hs` as an intermediate fact. Rewrite `this` using `[hd]`. Rewrite `hχ` using `[this]`. Conclude with `hχ (hfund n)`. Take `⟨c0, hc0m, rfl⟩` from `((hr (σ ^ m)).2 g).1 hg`.

Rewrite `hc0m` using `[hx, Ideal.mem_span_singleton']`. Take `⟨r, rfl⟩` from `hc0m`. Set `u : Fin f → F → C` to `fun n a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)`. Establish `hu : ∀ n, u n ∈ augIdeal AA.carrier`. Introduce `n`.

Establish `h1 : u n ∈ eig AA.carrier (σ ^ p ^ (n : ℕ))` using `((hr _).2 _).2 ⟨c n, by rw [hcx]; exact Ideal.mem_span_singleton_self _, rfl⟩`. Use `⟨h1.1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) 0) = 0`. Rewrite using `[MulChar.map_zero, mul_zero, map_zero]`. Establish `hprod` using `(lev_prod AA Finset.univ u hu fun n => (d n : ℕ)).2.2 hs`.

Use `Submodule.smul_mem _ r hprod using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Establish `ha : (σ ^ m) a = ∏ n : Fin f, ((σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)`. Rewrite using `[MulChar.pow_apply' _ (by omega), ← hd, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[MulChar.pow_apply' _ (pow_pos hp0 _).ne', ← pow_mul, mul_comm]`. Rewrite using `[ha, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod, Pi.smul_apply, Algebra.smul_def, Finset.prod_apply]`. Use `congrArg _ (Finset.prod_congr rfl fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_pow, map_pow, Pi.pow_apply]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hc AA hA χ hχ g hg
  obtain ⟨σ, hσ⟩ := fund_ex_relay p C v R hv hp F f hc
  obtain ⟨-, hgen, hfund, -, -⟩ := FundGen.main p C v R hv hp F f hc σ hσ
  obtain ⟨m, hm1, hm2, rfl⟩ := hgen χ
  have hr := eig_rank_one p C v R hv hp F f hc AA hA
  choose c hc0 hcx using fun n : ℕ => (hr (σ ^ p ^ n)).1
  have hp0 : 0 < p := hpp.out.pos
  have hlt : m < p ^ f := by
    have := pow_pos hp0 f
    omega
  obtain ⟨d, hd⟩ : ∃ d : Fin f → Fin p, ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
    refine ⟨finFunctionFinEquiv.symm ⟨m, hlt⟩, ?_⟩
    rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]
  have hne : ∃ n, (d n : ℕ) ≠ 0 := by
    by_contra hcon
    have h0 : ∀ n, (d n : ℕ) = 0 := fun n => by
      by_contra h; exact hcon ⟨n, h⟩
    simp only [h0, zero_mul, Finset.sum_const_zero] at hd
    omega
  have hx := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hc AA hA σ hσ c hcx).2 d hne
  rw [hd] at hx
  have hs : 2 ≤ ∑ n, (d n : ℕ) := by
    by_contra hs
    obtain ⟨n, hn⟩ := hne
    have := digits_single (p := p) (fun n => (d n : ℕ)) n hn hs
    rw [hd] at this
    rw [this] at hχ
    exact hχ (hfund n)
  obtain ⟨c0, hc0m, rfl⟩ := ((hr (σ ^ m)).2 g).1 hg
  rw [hx, Ideal.mem_span_singleton'] at hc0m
  obtain ⟨r, rfl⟩ := hc0m
  let u : Fin f → F → C := fun n a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)
  have hu : ∀ n, u n ∈ augIdeal AA.carrier := by
    intro n
    have h1 : u n ∈ eig AA.carrier (σ ^ p ^ (n : ℕ)) :=
      ((hr _).2 _).2 ⟨c n, by rw [hcx]; exact Ideal.mem_span_singleton_self _, rfl⟩
    refine ⟨h1.1, ?_⟩
    change algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) 0) = 0
    rw [MulChar.map_zero, mul_zero, map_zero]
  have hprod := (lev_prod AA Finset.univ u hu fun n => (d n : ℕ)).2.2 hs
  convert Submodule.smul_mem _ r hprod using 1
  funext a
  have ha : (σ ^ m) a = ∏ n : Fin f, ((σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) := by
    rw [MulChar.pow_apply' _ (by omega), ← hd, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [MulChar.pow_apply' _ (pow_pos hp0 _).ne', ← pow_mul, mul_comm]
  rw [ha, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod, Pi.smul_apply,
    Algebra.smul_def, Finset.prod_apply]
  refine congrArg _ (Finset.prod_congr rfl fun n _ => ?_)
  rw [← mul_pow, map_pow, Pi.pow_apply]
