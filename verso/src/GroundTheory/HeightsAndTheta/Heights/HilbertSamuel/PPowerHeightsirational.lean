import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerHeightsirational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace PowerHeightsirational

set_option linter.unusedSectionVars false

section Lattices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def InLat (y : (Σ k, ι k) → Ω) (α : K → ℤ) (x : Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → x * ∏ k, y ⟨k, c k⟩ ^ (-(α k)) ∈ chartRingZ y c

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_chartLat_iff {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {x : Ω} :
    x ∈ chartLat y a τ ↔ InLat y (fun k => (τ : ℤ) * a k) x := Iff.rfl

/- English proof (translation)
The claim follows from `hαβ ▸ h`.
-/
theorem InLat.congr {y : (Σ k, ι k) → Ω} {α β : K → ℤ} {x : Ω} (h : InLat y α x) (hαβ : α = β) :
    InLat y β x := hαβ ▸ h

/- English proof (translation)
Introduce `c hc`. Establish `hp : ∏ k, y ⟨k, c k⟩ ^ (-((α + β) k)) = (∏ k, y ⟨k, c k⟩ ^ (-(α k))) * ∏ k, y ⟨k, c k⟩ ^ (-(β k))`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, neg_add, zpow_add₀ (hc k)]`.

Establish `h : x * x' * ∏ k, y ⟨k, c k⟩ ^ (-((α + β) k)) = (x * ∏ k, y ⟨k, c k⟩ ^ (-(α k))) * (x' * ∏ k, y ⟨k, c k⟩ ^ (-(β k)))`. Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Subalgebra.mul_mem _ (hx c hc) (hx' c hc)`.
-/
theorem InLat.mul {y : (Σ k, ι k) → Ω} {α β : K → ℤ} {x x' : Ω} (hx : InLat y α x) (hx' : InLat y β x') :
    InLat y (α + β) (x * x') := by
  intro c hc
  have hp : ∏ k, y ⟨k, c k⟩ ^ (-((α + β) k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-(α k))) * ∏ k, y ⟨k, c k⟩ ^ (-(β k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
  have h : x * x' * ∏ k, y ⟨k, c k⟩ ^ (-((α + β) k)) =
      (x * ∏ k, y ⟨k, c k⟩ ^ (-(α k))) * (x' * ∏ k, y ⟨k, c k⟩ ^ (-(β k))) := by
    rw [hp]; ring
  rw [h]
  exact Subalgebra.mul_mem _ (hx c hc) (hx' c hc)

/- English proof (translation)
Introduce `c _`. Simplify using `only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]`. Conclude with `Subalgebra.one_mem _`.
-/
theorem inLat_one (y : (Σ k, ι k) → Ω) : InLat y 0 1 := by
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using inLat_one y`. Consider the case `succ n ih => rw [pow_succ, succ_nsmul]`. Conclude with `ih.mul hx`.
-/
theorem InLat.pow {y : (Σ k, ι k) → Ω} {α : K → ℤ} {x : Ω} (hx : InLat y α x) (n : ℕ) :
    InLat y (n • α) (x ^ n) := by
  induction n with
  | zero => simpa using inLat_one y
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hx

/- English proof (translation)
Introduce `c hc`. Establish `h : (∏ k, y ⟨k, f k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-((1 : K → ℤ) k)) = ∏ k, (y ⟨k, f k⟩ / y ⟨k, c k⟩)`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.one_apply, zpow_neg_one, div_eq_mul_inv]`.

Rewrite using `[h]`. Conclude with `Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, f k⟩, rfl⟩`.
-/
theorem inLat_prod (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) : InLat y 1 (∏ k, y ⟨k, f k⟩) := by
  intro c hc
  have h : (∏ k, y ⟨k, f k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-((1 : K → ℤ) k)) = ∏ k, (y ⟨k, f k⟩ / y ⟨k, c k⟩) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.one_apply, zpow_neg_one, div_eq_mul_inv]
  rw [h]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, f k⟩, rfl⟩

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hm' : ∏ p, lam p.1 ^ m p = ∏ k, lam k ^ d k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k]`. Establish `hsplit : ∏ p, (lam p.1 * z p) ^ m p = (∏ p, lam p.1 ^ m p) * ∏ p, z p ^ m p`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun p _ => mul_pow _ _ _`.

Rewrite using `[hsplit, hm']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale {d : K → ℕ} {g : MRing ι} (hg : IsMultiHomog g d) (lam : K → Ω) (z : (Σ k, ι k) → Ω) :
    aeval (fun p => lam p.1 * z p) g = (∏ k, lam k ^ d k) * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : ∏ p, lam p.1 ^ m p = ∏ k, lam k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  have hsplit : ∏ p, (lam p.1 * z p) ^ m p = (∏ p, lam p.1 ^ m p) * ∏ p, z p ^ m p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => mul_pow _ _ _
  rw [hsplit, hm']
  ring

/- English proof (translation)
Establish `h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hV.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show mConeMap y (X ⟨k, i⟩) = 0`.

Simplify using `[mConeMap, h0]`. Conclude with `⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩`.
-/
theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  exact ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩

end Lattices

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.
-/
theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Use `exacts [hf m h k, hg m h k]`.
-/
theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  exacts [hf m h k, hg m h k]

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.support_neg]`. Conclude with `hf m hm`.
-/
theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm

/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k, Pi.add_apply]`.
-/
theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k, Pi.add_apply]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[blockDeg]`.
-/
theorem blockDeg_zero (k₀ : K) : blockDeg k₀ 0 = 0 := by
  funext k
  simp [blockDeg]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [blockDeg, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem blockDeg_add (k₀ : K) (s t : ℕ) : blockDeg k₀ s + blockDeg k₀ t = blockDeg k₀ (s + t) := by
  funext k
  simp only [blockDeg, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `blockDeg_add k₀ s t ▸ homog_mul hf hg`.
-/
theorem homog_mul_block {k₀ : K} {f g : MRing ι} {s t : ℕ} (hf : IsMultiHomog f (blockDeg k₀ s))
    (hg : IsMultiHomog g (blockDeg k₀ t)) : IsMultiHomog (f * g) (blockDeg k₀ (s + t)) :=
  blockDeg_add k₀ s t ▸ homog_mul hf hg

/- English proof (translation)
The claim follows from `(blockDeg_zero k₀).symm ▸ homog_one`.
-/
theorem homog_one_block (k₀ : K) : IsMultiHomog (1 : MRing ι) (blockDeg k₀ 0) :=
  (blockDeg_zero k₀).symm ▸ homog_one

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Simplify using `only [blockDeg, if_true]`. Rewrite using `[Finset.sum_eq_single i₀]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hb (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm`. Simplify using the standard rewrite rules. Rewrite using `[blockDeg, if_neg hk]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hk (Sigma.mk.inj_iff.mp h).1.symm`.
-/
theorem homog_X_block (k₀ : K) (i₀ : ι k₀) : IsMultiHomog (X ⟨k₀, i₀⟩ : MRing ι) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k = k₀
  · subst hk
    simp only [blockDeg, if_true]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hb (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [blockDeg, if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (Sigma.mk.inj_iff.mp h).1.symm

def blockFrac (Y : (Σ k, ι k) → Ω) (k₀ : K) : Subfield Ω where
  carrier := {s | ∃ (t : ℕ) (g h : MRing ι), IsMultiHomog g (blockDeg k₀ t) ∧ IsMultiHomog h (blockDeg k₀ t) ∧
    aeval Y h ≠ 0 ∧ aeval Y g = s * aeval Y h}
  zero_mem' := ⟨0, 0, 1, homog_zero _, homog_one_block k₀, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, homog_one_block k₀, homog_one_block k₀, by simp, by simp⟩
  add_mem' := by
    rintro s s' ⟨t, g, h, hg, hh, hh0, he⟩ ⟨t', g', h', hg', hh', hh0', he'⟩
    refine ⟨t + t', g * h' + h * g', h * h', homog_add (homog_mul_block hg hh') (homog_mul_block hh hg'),
      homog_mul_block hh hh', by rw [map_mul]; exact mul_ne_zero hh0 hh0', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, he, he']
    ring
  neg_mem' := by
    rintro s ⟨t, g, h, hg, hh, hh0, he⟩
    exact ⟨t, -g, h, homog_neg hg, hh, hh0, by rw [map_neg, he, neg_mul]⟩
  mul_mem' := by
    rintro s s' ⟨t, g, h, hg, hh, hh0, he⟩ ⟨t', g', h', hg', hh', hh0', he'⟩
    refine ⟨t + t', g * g', h * h', homog_mul_block hg hg', homog_mul_block hh hh',
      by rw [map_mul]; exact mul_ne_zero hh0 hh0', ?_⟩
    rw [map_mul, map_mul, he, he']
    ring
  inv_mem' := by
    rintro s ⟨t, g, h, hg, hh, hh0, he⟩
    by_cases hs : s = 0
    · subst hs
      exact ⟨0, 0, 1, homog_zero _, homog_one_block k₀, by simp, by simp⟩
    · refine ⟨t, h, g, hh, hg, by rw [he]; exact mul_ne_zero hs hh0, ?_⟩
      rw [he, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Conclude with `⟨X ⟨none, j⟩, homog_X_block (ι := addIdx ι N) none j, by simp [addBlock]⟩`. Consider the case `zero => exact ⟨0, homog_zero _, by simp⟩`.

Consider the case `add x x' _ _ hx hx'`. Take `⟨g, hg, rfl⟩` from `hx`. Take `⟨g', hg', rfl⟩` from `hx'`. Conclude with `⟨g + g', homog_add hg hg', by simp⟩`. Consider the case `neg x _ hx`.

Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `⟨-g, homog_neg hg, by simp⟩`.
-/
theorem exists_form_of_mem_closure {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) {x : Ω}
    (hx : x ∈ AddSubgroup.closure (Set.range v)) :
    ∃ g : MRing (addIdx ι N), IsMultiHomog g (blockDeg (none : Option K) 1) ∧ aeval (addBlock y v) g = x := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨X ⟨none, j⟩, homog_X_block (ι := addIdx ι N) none j, by simp [addBlock]⟩
  | zero => exact ⟨0, homog_zero _, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', rfl⟩ := hx'
    exact ⟨g + g', homog_add hg hg', by simp⟩
  | neg x _ hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨-g, homog_neg hg, by simp⟩

end Forms

end PowerHeightsirational

open PowerHeightsirational in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ _ y D a q w hD hV hB hw hgen hdeg`. Take `⟨c0, hc0⟩` from `exists_chart hV`. Take `⟨k, e, hk, he0, heQ⟩` from `hK K ι Ω y D a hD hV hB (hN K ι Ω y D a q w hV hw hgen) hdeg`. Take `⟨n, hn, hne⟩` from `hC K ι Ω y _ 1 e heQ`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, w j ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨u, -, hu⟩` from `hgen c0 hc0`. Simplify using `[hcon] at hu`. Use `⟨k, fun m hm N v hv => ?_⟩` and prove the remaining obligations.

Establish `hE0 : (n : Ω) * e * w j ^ (m - k) ≠ 0` using `mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0) (pow_ne_zero _ hj)`. Establish `hEl : InLat y ((fun κ => (k : ℤ) * a κ - 1) + (m - k) • fun κ => (1 : ℤ) * a κ) ((n : Ω) * e * w j ^ (m - k))`. Establish `h1 : InLat y (fun κ => (k : ℤ) * a κ - 1) ((n : Ω) * e)` using `(mem_chartLat_iff.mp hne).congr (by funext κ; simp)`. Conclude with `h1.mul ((mem_chartLat_iff.mp (hw j)).pow _)`. Establish `hsec : ∀ f : ∀ κ, ι κ, (n : Ω) * e * w j ^ (m - k) * ∏ κ, y ⟨κ, f κ⟩ ∈ AddSubgroup.closure (Set.range v)`.

Introduce `f`. Rewrite using `[hv, mem_chartLat_iff]`. Use `(hEl.mul (inLat_prod y f)).congr ?_` and prove the remaining obligations. Use function extensionality and compare the values at `κ`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.one_apply]`.

Establish `hmk : ((m - k : ℕ) : ℤ) = (m : ℤ) - k` using `by omega`. Rewrite using `[nsmul_eq_mul, hmk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrat : ∀ p : Σ κ, ι κ, y p / y ⟨p.1, c0 p.1⟩ ∈ blockFrac (addBlock y v) none`. Introduce and unpack `⟨κ0, i⟩`.

Take `⟨g1, hg1, hv1⟩` from `exists_form_of_mem_closure y v (hsec (Function.update c0 κ0 i))`. Take `⟨g2, hg2, hv2⟩` from `exists_form_of_mem_closure y v (hsec c0)`. Use `⟨1, g1, g2, hg1, hg2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv2]`. Conclude with `mul_ne_zero hE0 (Finset.prod_ne_zero_iff.mpr fun κ _ => hc0 κ)`.

Rewrite using `[hv1, hv2]`. Establish `h1 : ∏ κ, y ⟨κ, Function.update c0 κ0 i κ⟩ = y ⟨κ0, i⟩ * ∏ κ ∈ Finset.univ.erase κ0, y ⟨κ, c0 κ⟩`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun κ => y ⟨κ, Function.update c0 κ0 i κ⟩) (Finset.mem_univ κ0)]`. Simplify using `only [Function.update_self]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun κ hκ => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hκ)]`. Establish `h2 : ∏ κ, y ⟨κ, c0 κ⟩ = y ⟨κ0, c0 κ0⟩ * ∏ κ ∈ Finset.univ.erase κ0, y ⟨κ, c0 κ⟩` using `(Finset.mul_prod_erase Finset.univ (fun κ => y ⟨κ, c0 κ⟩) (Finset.mem_univ κ0)).symm`. Rewrite using `[h1, h2]`. Use `hc0 κ0` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `hall : ∀ s : Ω, s ∈ blockFrac (addBlock y v) none`. Introduce `s`. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hB s`. Establish `hmem : ∀ f : MRing ι, aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) f ∈ blockFrac (addBlock y v) none`.

Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r`. Rewrite using `[aeval_C, algebraMap_int_eq, eq_intCast]`. Conclude with `intCast_mem _ r`.

Consider the case `add f1 f2 h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`. Consider the case `mul_X f p h1 => rw [map_mul, aeval_X]`. Conclude with `mul_mem h1 (hrat p)`. Establish `hy : (fun p : Σ κ, ι κ => y ⟨p.1, c0 p.1⟩ * (y p / y ⟨p.1, c0 p.1⟩)) = y`.

Use function extensionality and compare the values at `p`. Use `hc0 p.1` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `eg` using `aeval_scale hg (fun κ => y ⟨κ, c0 κ⟩) (fun p => y p / y ⟨p.1, c0 p.1⟩)`. Establish `eh` using `aeval_scale hh (fun κ => y ⟨κ, c0 κ⟩) (fun p => y p / y ⟨p.1, c0 p.1⟩)`.

Rewrite `eg`, `eh` using `[hy]`. Establish `hΛ : (∏ κ, y ⟨κ, c0 κ⟩ ^ d κ) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc0 κ)`. Establish `hh0' : aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) h ≠ 0`. Introduce `h0`. Rewrite `eh` using `[h0, mul_zero]`.

Conclude with `hh0 eh`. Establish `hs : s = aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) g / aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) h`. Rewrite using `[eq_div_iff hh0']`. Apply `mul_left_cancel₀ hΛ` to reduce the goal to its premises. Rewrite using `[← eg, hgh, eh]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`. Conclude with `div_mem (hmem g) (hmem h)`. Introduce `d g h hg hh hh0`. Take `⟨t, g', h', hg', hh', hh0', he⟩` from `hall (aeval (addBlock y v) g / aeval (addBlock y v) h)`.

Use `⟨t, g', h', hg', hh', hh0', ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Clear the denominators using the available nonvanishing facts.
-/
theorem PowerHeightsirational.proof (hN : GeneratedNefGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) : PowerHeightsirational.Statement := by
  intro K _ _ ι _ Ω _ _ y D a q w hD hV hB hw hgen hdeg
  obtain ⟨c0, hc0⟩ := exists_chart hV
  obtain ⟨k, e, hk, he0, heQ⟩ := hK K ι Ω y D a hD hV hB (hN K ι Ω y D a q w hV hw hgen) hdeg
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, -, hu⟩ := hgen c0 hc0
    simp [hcon] at hu
  refine ⟨k, fun m hm N v hv => ?_⟩
  have hE0 : (n : Ω) * e * w j ^ (m - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0) (pow_ne_zero _ hj)
  have hEl : InLat y ((fun κ => (k : ℤ) * a κ - 1) + (m - k) • fun κ => (1 : ℤ) * a κ)
      ((n : Ω) * e * w j ^ (m - k)) := by
    have h1 : InLat y (fun κ => (k : ℤ) * a κ - 1) ((n : Ω) * e) :=
      (mem_chartLat_iff.mp hne).congr (by funext κ; simp)
    exact h1.mul ((mem_chartLat_iff.mp (hw j)).pow _)
  have hsec : ∀ f : ∀ κ, ι κ,
      (n : Ω) * e * w j ^ (m - k) * ∏ κ, y ⟨κ, f κ⟩ ∈ AddSubgroup.closure (Set.range v) := by
    intro f
    rw [hv, mem_chartLat_iff]
    refine (hEl.mul (inLat_prod y f)).congr ?_
    funext κ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply]
    have hmk : ((m - k : ℕ) : ℤ) = (m : ℤ) - k := by omega
    rw [nsmul_eq_mul, hmk]
    ring
  have hrat : ∀ p : Σ κ, ι κ, y p / y ⟨p.1, c0 p.1⟩ ∈ blockFrac (addBlock y v) none := by
    rintro ⟨κ0, i⟩
    obtain ⟨g1, hg1, hv1⟩ := exists_form_of_mem_closure y v (hsec (Function.update c0 κ0 i))
    obtain ⟨g2, hg2, hv2⟩ := exists_form_of_mem_closure y v (hsec c0)
    refine ⟨1, g1, g2, hg1, hg2, ?_, ?_⟩
    · rw [hv2]
      exact mul_ne_zero hE0 (Finset.prod_ne_zero_iff.mpr fun κ _ => hc0 κ)
    · rw [hv1, hv2]
      have h1 : ∏ κ, y ⟨κ, Function.update c0 κ0 i κ⟩ =
          y ⟨κ0, i⟩ * ∏ κ ∈ Finset.univ.erase κ0, y ⟨κ, c0 κ⟩ := by
        rw [← Finset.mul_prod_erase Finset.univ (fun κ => y ⟨κ, Function.update c0 κ0 i κ⟩)
          (Finset.mem_univ κ0)]
        simp only [Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun κ hκ => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hκ)]
      have h2 : ∏ κ, y ⟨κ, c0 κ⟩ = y ⟨κ0, c0 κ0⟩ * ∏ κ ∈ Finset.univ.erase κ0, y ⟨κ, c0 κ⟩ :=
        (Finset.mul_prod_erase Finset.univ (fun κ => y ⟨κ, c0 κ⟩) (Finset.mem_univ κ0)).symm
      rw [h1, h2]
      have := hc0 κ0
      field_simp
  have hall : ∀ s : Ω, s ∈ blockFrac (addBlock y v) none := by
    intro s
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB s
    have hmem : ∀ f : MRing ι, aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) f ∈ blockFrac (addBlock y v) none := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C r =>
        rw [aeval_C, algebraMap_int_eq, eq_intCast]
        exact intCast_mem _ r
      | add f1 f2 h1 h2 => rw [map_add]; exact add_mem h1 h2
      | mul_X f p h1 => rw [map_mul, aeval_X]; exact mul_mem h1 (hrat p)
    have hy : (fun p : Σ κ, ι κ => y ⟨p.1, c0 p.1⟩ * (y p / y ⟨p.1, c0 p.1⟩)) = y := by
      funext p
      have := hc0 p.1
      field_simp
    have eg := aeval_scale hg (fun κ => y ⟨κ, c0 κ⟩) (fun p => y p / y ⟨p.1, c0 p.1⟩)
    have eh := aeval_scale hh (fun κ => y ⟨κ, c0 κ⟩) (fun p => y p / y ⟨p.1, c0 p.1⟩)
    rw [hy] at eg eh
    have hΛ : (∏ κ, y ⟨κ, c0 κ⟩ ^ d κ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc0 κ)
    have hh0' : aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at eh
      exact hh0 eh
    have hs : s = aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) g / aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) h := by
      rw [eq_div_iff hh0']
      apply mul_left_cancel₀ hΛ
      rw [← eg, hgh, eh]
      ring
    rw [hs]
    exact div_mem (hmem g) (hmem h)
  intro d g h hg hh hh0
  obtain ⟨t, g', h', hg', hh', hh0', he⟩ := hall (aeval (addBlock y v) g / aeval (addBlock y v) h)
  refine ⟨t, g', h', hg', hh', hh0', ?_⟩
  rw [he]
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
