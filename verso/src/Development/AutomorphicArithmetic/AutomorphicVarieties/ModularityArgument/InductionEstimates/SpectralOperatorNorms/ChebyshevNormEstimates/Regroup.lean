import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Exponents3

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open Classical in
/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `symm`.

Establish `hinj : Set.InjOn (fun ζ : ℂ => (a i, ζ)) (S i)` using `fun z _ z' _ h => (Prod.ext_iff.1 h).2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image hinj]`. Use `Finset.sum_congr rfl fun ζ hζ => ?_` and prove the remaining obligations. Rewrite using `[if_pos ⟨rfl, hζ⟩, mul_assoc]`.

Use `_ = _ := by`. Use `Finset.sum_subset ?_ ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨ζ, hζ, rfl⟩` from `Finset.mem_image.1 hq`. Conclude with `hP i hi ζ hζ`.

Introduce `q _ hq`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hq (Finset.mem_image.2 ⟨q.2, h2, Prod.ext h1 rfl⟩)`.
-/
private lemma regroup {T : Type} (s : Finset T) (a : T → ℝ) (S : T → Finset ℂ) (c : T → ℂ → ℂ) (w : T → ℂ) (P : Finset (ℝ × ℂ))
    (hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P) (f : ℝ × ℂ → ℂ) :
    ∑ q ∈ P, (∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q =
      ∑ i ∈ s, w i * ∑ ζ ∈ S i, c i ζ * f (a i, ζ) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  symm
  have hinj : Set.InjOn (fun ζ : ℂ => (a i, ζ)) (S i) := fun z _ z' _ h => (Prod.ext_iff.1 h).2
  calc ∑ ζ ∈ S i, w i * (c i ζ * f (a i, ζ))
      = ∑ q ∈ (S i).image (fun ζ : ℂ => (a i, ζ)), (if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [if_pos ⟨rfl, hζ⟩, mul_assoc]
    _ = _ := by
        refine Finset.sum_subset ?_ ?_
        · intro q hq
          obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
          exact hP i hi ζ hζ
        · intro q _ hq
          rw [if_neg, zero_mul]
          rintro ⟨h1, h2⟩
          exact hq (Finset.mem_image.2 ⟨q.2, h2, Prod.ext h1 rfl⟩)

/- English proof (translation)
Use `tendsto_atTop.2 fun M => ?_` and prove the remaining obligations. Use `filter_upwards [h 1, eventually_ge_atTop M.factorial] with j hj hM`. Assume the negation of the conclusion as `hlt`. Establish `h1 : (d j).factorial ≤ M.factorial` using `Nat.factorial_le (not_le.1 hlt).le`. Establish `h2 : ((d j).factorial : ℝ) ≤ j` using `by exact_mod_cast h1.trans hM`.

Establish `h3` using `Real.add_one_le_exp (1 * (j : ℝ))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma d_top (d : ℕ → ℕ) (h : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (1 * (j : ℝ))
  linarith

/- English proof (translation)
Take `⟨M, hM⟩` from `(Z.image fun ζ => -Real.log ‖ζ‖).bddAbove`. Use `⟨M, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `h1 : -Real.log ‖ζ‖ ≤ M` using `hM (by simpa using ⟨ζ, hζ, rfl⟩)`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma low_bd (Z : Finset ℂ) (hZ : ∀ ζ ∈ Z, ζ ≠ 0) : ∃ cq : ℝ, ∀ ζ ∈ Z, Real.exp (-cq) ≤ ‖ζ‖ := by
  obtain ⟨M, hM⟩ := (Z.image fun ζ => -Real.log ‖ζ‖).bddAbove
  refine ⟨M, fun ζ hζ => ?_⟩
  have h1 : -Real.log ‖ζ‖ ≤ M := hM (by simpa using ⟨ζ, hζ, rfl⟩)
  calc Real.exp (-M) ≤ Real.exp (Real.log ‖ζ‖) := Real.exp_le_exp.2 (by linarith)
    _ = ‖ζ‖ := Real.exp_log (norm_pos_iff.2 (hZ ζ hζ))

/- English proof (translation)
Introduce `T a τ act good x hx hx1 p hp d hd hfac hexp hfin H`. Use `choose! S c hS0 hτ using hexp`. Take `⟨cq, hcq⟩` from `low_bd (hfin.toFinset.biUnion S) (by`. Introduce `ζ hζ h0`. Take `⟨i, hi, hζ⟩` from `Finset.mem_biUnion.1 hζ`.

Establish `hi'` using `hfin.mem_toFinset.1 hi`. Conclude with `hS0 i hi'.1 (hi'.2 ▸ hx) (h0 ▸ hζ))`. Take `⟨N, hN⟩` from `exponents3 d hd hfac p hp cq x hx hx1`. Take `⟨c₁, H⟩` from `H N`. Take `⟨η, hη, hηx, hE⟩` from `hN c₁`.

Take `⟨s, u, u', k, hk, hs, hu, hgood, hbad, hest⟩` from `H η hη hηx`. Establish `hsp : ∀ i ∈ s, act i ∧ 0 < a i` using `fun i hi => ⟨((hs i).1 hi).2, hη.trans ((hs i).1 hi).1⟩`. Use `set P : Finset (ℝ × ℂ) := s.biUnion fun i => (S i).image fun ζ => (a i, ζ) with hPdef`. Establish `hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P` using `fun i hi ζ hζ => Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨ζ, hζ, rfl⟩⟩`. Establish `hP' : ∀ q ∈ P, ∃ i ∈ s, a i = q.1 ∧ q.2 ∈ S i`.

Introduce `q hq`. Take `⟨i, hi, hq⟩` from `Finset.mem_biUnion.1 hq`. Take `⟨ζ, hζ, rfl⟩` from `Finset.mem_image.1 hq`. Conclude with `⟨i, hi, rfl, hζ⟩`. Establish `hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ S i, c i ζ * ζ ^ j` using `(Filter.eventually_all_finset s).2 fun i hi => hτ i (hsp i hi).1 (hsp i hi).2`.

Take `⟨J, hJ⟩` from `eventually_atTop.1 hall`. Set `C : (T → ℂ) → ℝ × ℂ → ℂ` to `fun w q => ∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0`. Establish `key` using `hE η hη le_rfl P (fun q => q.1.1) (fun q => q.1.2) (fun q => by`. Take `⟨i, hi, h1, -⟩` from `hP' q.1 q.2`. Conclude with `h1 ▸ ((hs i).1 hi).1)`.

Use the proof step `(fun q h0 => by`. Take `⟨i, hi, -, h2⟩` from `hP' q.1 q.2`. Conclude with `hS0 i (hsp i hi).1 (hsp i hi).2 (h0 ▸ h2))`. Use the proof step `(fun q q' h => Subtype.ext h)`. Use the proof step `(fun j q => C (fun i => u i (d j)) q.1) (fun q => C u' q.1)`.

Use the proof step `(fun q => by`. Use `tendsto_finset_sum _ fun i hi => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `((hu i hi).comp (d_top d hfac)).mul_const _`. Conclude with `tendsto_const_nhds)`.

Use the proof step `(fun s₀ => by`. Take `⟨K, hK⟩` from `hest s₀`. Use `⟨K, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'`. Use `le_of_eq_of_le ?_ (hj m hm m' hm')` and prove the remaining obligations.

Use `congr 1`. Establish `h1` using `regroup s a S c (fun i => u i (d j)) P hP (fun q => (q.1 : ℂ) ^ d j * (cheb η (j / p + m) q.1 : ℂ) * q.2 ^ (j + m'))`. Rewrite `h1` using `[← Finset.sum_coe_sort P]`. Use `Eq.trans (Finset.sum_congr rfl fun q _ => by simp only [C, mul_assoc]) (h1.trans ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[hJ (j + m') (by omega) i hi, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Use the proof step `ring)`. Use `filter_upwards [hall] with j hj`. Establish `h1` using `regroup s a S c u' P hP (fun q => if q.1 = x then q.2 ^ j else 0)`.

Establish `h2 : ∑ q ∈ P, C u' q * (if q.1 = x then q.2 ^ j else 0) = 0`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations. Use `split_ifs with hqx`. Take `⟨i, hi, h1, h2⟩` from `hP' q hq`. Use `key ⟨q, hq⟩ hqx.ge (hcq _ (Finset.mem_biUnion.2 ⟨i, hfin.mem_toFinset.2 ⟨(hsp i hi).1, h1.trans hqx⟩, h2⟩))` as an intermediate fact.

Rewrite using `[this, zero_mul]`. Conclude with `mul_zero _`. Establish `h3 : k * ∑ i ∈ s.filter (fun i => good i ∧ a i = x), τ i j = 0`. Rewrite using `[← h2]`. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hg : good i`. Distinguish the cases in `ha : a i = x`. Simplify using `only [hg, ha, and_self, if_true, hgood i hi hg ha, hj i hi]`.

Simplify using `[ha]`. Simplify using `[hg, hbad i hi hg]`. Establish `h4 : {i | act i ∧ good i ∧ a i = x} = ↑(s.filter (fun i => good i ∧ a i = x))`. Use extensionality with `i`. Simplify using `only [Set.mem_setOf_eq, Finset.coe_filter]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨(hs i).2 ⟨h3 ▸ hηx, h1⟩, h2, h3⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(hsp i h1).1, h2⟩`.

Use `show ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0`. Rewrite using `[h4, finsum_mem_coe_finset]`. Conclude with `(mul_eq_zero.1 h3).resolve_left hk`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.absX :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      {i | act i ∧ a i = x}.Finite →
      (∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  classical
  intro T a τ act good x hx hx1 p hp d hd hfac hexp hfin H
  choose! S c hS0 hτ using hexp
  obtain ⟨cq, hcq⟩ := low_bd (hfin.toFinset.biUnion S) (by
    intro ζ hζ h0
    obtain ⟨i, hi, hζ⟩ := Finset.mem_biUnion.1 hζ
    have hi' := hfin.mem_toFinset.1 hi
    exact hS0 i hi'.1 (hi'.2 ▸ hx) (h0 ▸ hζ))
  obtain ⟨N, hN⟩ := exponents3 d hd hfac p hp cq x hx hx1
  obtain ⟨c₁, H⟩ := H N
  obtain ⟨η, hη, hηx, hE⟩ := hN c₁
  obtain ⟨s, u, u', k, hk, hs, hu, hgood, hbad, hest⟩ := H η hη hηx
  have hsp : ∀ i ∈ s, act i ∧ 0 < a i := fun i hi => ⟨((hs i).1 hi).2, hη.trans ((hs i).1 hi).1⟩
  set P : Finset (ℝ × ℂ) := s.biUnion fun i => (S i).image fun ζ => (a i, ζ) with hPdef
  have hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P := fun i hi ζ hζ =>
    Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨ζ, hζ, rfl⟩⟩
  have hP' : ∀ q ∈ P, ∃ i ∈ s, a i = q.1 ∧ q.2 ∈ S i := by
    intro q hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨i, hi, rfl, hζ⟩
  have hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ S i, c i ζ * ζ ^ j :=
    (Filter.eventually_all_finset s).2 fun i hi => hτ i (hsp i hi).1 (hsp i hi).2
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  let C : (T → ℂ) → ℝ × ℂ → ℂ := fun w q => ∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0
  have key := hE η hη le_rfl P (fun q => q.1.1) (fun q => q.1.2)
    (fun q => by
      obtain ⟨i, hi, h1, -⟩ := hP' q.1 q.2
      exact h1 ▸ ((hs i).1 hi).1)
    (fun q h0 => by
      obtain ⟨i, hi, -, h2⟩ := hP' q.1 q.2
      exact hS0 i (hsp i hi).1 (hsp i hi).2 (h0 ▸ h2))
    (fun q q' h => Subtype.ext h)
    (fun j q => C (fun i => u i (d j)) q.1) (fun q => C u' q.1)
    (fun q => by
      refine tendsto_finset_sum _ fun i hi => ?_
      split_ifs
      · exact ((hu i hi).comp (d_top d hfac)).mul_const _
      · exact tendsto_const_nhds)
    (fun s₀ => by
      obtain ⟨K, hK⟩ := hest s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
      refine le_of_eq_of_le ?_ (hj m hm m' hm')
      congr 1
      have h1 := regroup s a S c (fun i => u i (d j)) P hP
        (fun q => (q.1 : ℂ) ^ d j * (cheb η (j / p + m) q.1 : ℂ) * q.2 ^ (j + m'))
      rw [← Finset.sum_coe_sort P] at h1
      refine Eq.trans (Finset.sum_congr rfl fun q _ => by simp only [C, mul_assoc]) (h1.trans ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hJ (j + m') (by omega) i hi, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      ring)
  filter_upwards [hall] with j hj
  have h1 := regroup s a S c u' P hP (fun q => if q.1 = x then q.2 ^ j else 0)
  have h2 : ∑ q ∈ P, C u' q * (if q.1 = x then q.2 ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    split_ifs with hqx
    · obtain ⟨i, hi, h1, h2⟩ := hP' q hq
      have := key ⟨q, hq⟩ hqx.ge (hcq _ (Finset.mem_biUnion.2
        ⟨i, hfin.mem_toFinset.2 ⟨(hsp i hi).1, h1.trans hqx⟩, h2⟩))
      rw [this, zero_mul]
    · exact mul_zero _
  have h3 : k * ∑ i ∈ s.filter (fun i => good i ∧ a i = x), τ i j = 0 := by
    rw [← h2]
    refine Eq.trans ?_ h1.symm
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hg : good i
    · by_cases ha : a i = x
      · simp only [hg, ha, and_self, if_true, hgood i hi hg ha, hj i hi]
      · simp [ha]
    · simp [hg, hbad i hi hg]
  have h4 : {i | act i ∧ good i ∧ a i = x} = ↑(s.filter (fun i => good i ∧ a i = x)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hs i).2 ⟨h3 ▸ hηx, h1⟩, h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hsp i h1).1, h2⟩
  show ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0
  rw [h4, finsum_mem_coe_finset]
  exact (mul_eq_zero.1 h3).resolve_left hk
