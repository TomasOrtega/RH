import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFix

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramGen

/- English proof (translation)
Establish `h1 : z 1 = 0` using `by simpa using hadd 1 1`. Establish `hinv : ∀ σ, z σ⁻¹ = - z σ`. Introduce `σ`. Establish `h` using `hadd σ σ⁻¹`. Rewrite `h` using `[mul_inv_cancel, h1]`.

Take the linear combination `-h`. Set `H : Subgroup G` to `{ carrier := {σ | ‖z σ‖ ≤ ‖z F‖} mul_mem' := fun {a b} ha hb => by show ‖z (a * b)‖ ≤ ‖z F‖`. Rewrite using `[hadd]`. Conclude with `(PadicInt.nonarchimedean _ _).trans (max_le ha hb)`. Use the proof step `one_mem' := by show ‖z 1‖ ≤ ‖z F‖`.

Rewrite using `[h1, norm_zero]`. Conclude with `norm_nonneg _`. Use the proof step `inv_mem' := fun {a} ha => by show ‖z a⁻¹‖ ≤ ‖z F‖`. Rewrite using `[hinv, norm_neg]`. Conclude with `ha }`.

Establish `hHc : IsClosed (H : Set G)` using `isClosed_le (continuous_norm.comp hc) continuous_const`. Establish `hsup : Subgroup.zpowers F ⊔ I ≤ H`. Use `sup_le ((Subgroup.zpowers_le (H := H)).2 (show ‖z F‖ ≤ ‖z F‖ from le_rfl)) ?_` and prove the remaining obligations. Introduce `σ hσ`. Use `show ‖z σ‖ ≤ ‖z F‖`.

Rewrite using `[hI σ hσ, norm_zero]`. Conclude with `norm_nonneg _`. Establish `hbound : ∀ σ, ‖z σ‖ ≤ ‖z F‖`. Introduce `σ`. Establish `hle` using `Subgroup.topologicalClosure_minimal _ hsup hHc`.

Rewrite `hle` using `[hF]`. Conclude with `hle (Subgroup.mem_top σ)`. Establish `hF0 : z F ≠ 0`. Introduce `h`. Take `⟨σ, hσ⟩` from `h0`.

Apply `hσ` to reduce the goal to its premises. Use `hbound σ` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `norm_le_zero_iff.mp this`. Establish `hF0' : (z F : ℚ_[l]) ≠ 0` using `fun h => hF0 (Subtype.ext (h.trans PadicInt.coe_zero.symm))`.

Set `w : G → ℤ_[l]` to `fun σ => ⟨(z σ : ℚ_[l]) / (z F : ℚ_[l]), by`. Rewrite using `[norm_div, PadicInt.padic_norm_e_of_padicInt, PadicInt.padic_norm_e_of_padicInt, div_le_one (norm_pos_iff.mpr hF0)]`. Conclude with `hbound σ⟩`. Establish `hw : ∀ σ, (w σ : ℚ_[l]) = (z σ : ℚ_[l]) / (z F : ℚ_[l])` using `fun _ => rfl`. Establish `hwadd : ∀ σ τ, w (σ * τ) = w σ + w τ`.

Introduce `σ τ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (w (σ * τ) : ℚ_[l]) = ((w σ + w τ : ℤ_[l]) : ℚ_[l])`. Rewrite using `[PadicInt.coe_add, hw, hw, hw, hadd, PadicInt.coe_add, add_div]`. Establish `hwc : Continuous w` using `Continuous.subtype_mk ((continuous_subtype_val.comp hc).div_const _) _`.

Set `ν : G →* Multiplicative ℤ_[l]` to `MonoidHom.mk' (fun σ => Multiplicative.ofAdd (w σ)) (fun σ τ => by`. Rewrite using `[hwadd]`. Use the proof step `rfl)`. Use `⟨ν, continuous_ofAdd.comp hwc, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ show Multiplicative.ofAdd (w σ) = 1`.

Rewrite using `[ofAdd_eq_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (w σ : ℚ_[l]) = ((0 : ℤ_[l]) : ℚ_[l])`. Rewrite using `[hw, hI σ hσ]`. Simplify using the standard rewrite rules.

Use `show Multiplicative.ofAdd (w F) = Multiplicative.ofAdd 1`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (w F : ℚ_[l]) = ((1 : ℤ_[l]) : ℚ_[l])`. Rewrite using `[hw, div_self hF0', PadicInt.coe_one]`.
-/
theorem exists_normalised {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Subgroup G) (F : G)
    (hF : (Subgroup.zpowers F ⊔ I).topologicalClosure = ⊤) (z : G → ℤ_[l]) (hc : Continuous z)
    (hadd : ∀ σ τ, z (σ * τ) = z σ + z τ) (hI : ∀ σ ∈ I, z σ = 0) (h0 : ∃ σ, z σ ≠ 0) :
    ∃ ν : G →* Multiplicative ℤ_[l], Continuous ν ∧ (∀ σ ∈ I, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 := by
  have h1 : z 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ σ, z σ⁻¹ = - z σ := by
    intro σ
    have h := hadd σ σ⁻¹
    rw [mul_inv_cancel, h1] at h
    linear_combination -h

  let H : Subgroup G :=
    { carrier := {σ | ‖z σ‖ ≤ ‖z F‖}
      mul_mem' := fun {a b} ha hb => by
        show ‖z (a * b)‖ ≤ ‖z F‖
        rw [hadd]
        exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
      one_mem' := by
        show ‖z 1‖ ≤ ‖z F‖
        rw [h1, norm_zero]
        exact norm_nonneg _
      inv_mem' := fun {a} ha => by
        show ‖z a⁻¹‖ ≤ ‖z F‖
        rw [hinv, norm_neg]
        exact ha }
  have hHc : IsClosed (H : Set G) := isClosed_le (continuous_norm.comp hc) continuous_const
  have hsup : Subgroup.zpowers F ⊔ I ≤ H := by
    refine sup_le ((Subgroup.zpowers_le (H := H)).2 (show ‖z F‖ ≤ ‖z F‖ from le_rfl)) ?_
    intro σ hσ
    show ‖z σ‖ ≤ ‖z F‖
    rw [hI σ hσ, norm_zero]
    exact norm_nonneg _
  have hbound : ∀ σ, ‖z σ‖ ≤ ‖z F‖ := by
    intro σ
    have hle := Subgroup.topologicalClosure_minimal _ hsup hHc
    rw [hF] at hle
    exact hle (Subgroup.mem_top σ)
  have hF0 : z F ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := h0
    apply hσ
    have := hbound σ
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hF0' : (z F : ℚ_[l]) ≠ 0 := fun h => hF0 (Subtype.ext (h.trans PadicInt.coe_zero.symm))

  let w : G → ℤ_[l] := fun σ => ⟨(z σ : ℚ_[l]) / (z F : ℚ_[l]), by
    rw [norm_div, PadicInt.padic_norm_e_of_padicInt, PadicInt.padic_norm_e_of_padicInt,
      div_le_one (norm_pos_iff.mpr hF0)]
    exact hbound σ⟩
  have hw : ∀ σ, (w σ : ℚ_[l]) = (z σ : ℚ_[l]) / (z F : ℚ_[l]) := fun _ => rfl
  have hwadd : ∀ σ τ, w (σ * τ) = w σ + w τ := by
    intro σ τ
    apply Subtype.ext
    show (w (σ * τ) : ℚ_[l]) = ((w σ + w τ : ℤ_[l]) : ℚ_[l])
    rw [PadicInt.coe_add, hw, hw, hw, hadd, PadicInt.coe_add, add_div]
  have hwc : Continuous w :=
    Continuous.subtype_mk ((continuous_subtype_val.comp hc).div_const _) _
  let ν : G →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (w σ)) (fun σ τ => by
      rw [hwadd]
      rfl)
  refine ⟨ν, continuous_ofAdd.comp hwc, ?_, ?_⟩
  · intro σ hσ
    show Multiplicative.ofAdd (w σ) = 1
    rw [ofAdd_eq_one]
    apply Subtype.ext
    show (w σ : ℚ_[l]) = ((0 : ℤ_[l]) : ℚ_[l])
    rw [hw, hI σ hσ]
    simp
  · show Multiplicative.ofAdd (w F) = Multiplicative.ofAdd 1
    congr 1
    apply Subtype.ext
    show (w F : ℚ_[l]) = ((1 : ℤ_[l]) : ℚ_[l])
    rw [hw, div_self hF0', PadicInt.coe_one]

/- English proof (translation)
Establish `h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.
-/
private theorem norm_prime_lt_one_algClosure {l : ℕ} [Fact l.Prime] : ‖(l : Om l)‖ < 1 := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, norm_mul]`. Use `mul_le_of_le_one_left (norm_nonneg _) ?_` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations. Introduce `j _`. Rewrite using `[norm_mul, norm_pow, norm_pow]`.

Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)`.
-/
private theorem norm_pow_sub_pow_le_norm_sub {E : Type} [NormedField E] [IsUltrametricDist E] {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ ‖y - x‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro j _
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

/- English proof (translation)
Establish `hl1 : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hq : 1 < l ^ n` using `Nat.one_lt_pow hn.ne' hl1`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, map_zero]`. Establish `hxq : x ^ (l ^ n - 1) = 1`.

Establish `h : x ^ (l ^ n - 1) * x = 1 * x`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq.le, one_mul, hx]`. Conclude with `mul_right_cancel₀ hx0 h`. Establish `hnx : ‖x‖ = 1`. Establish `h` using `congrArg norm hxq`.

Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg x) (by omega)).mp h`. Establish `hy : σ x ^ l ^ n = σ x` using `by rw [← map_pow, hx]`. Establish `hε : ‖σ x - x‖ < 1` using `hσ x hnx.le`. Establish `hny : ‖σ x‖ ≤ 1`.

Establish `h` using `IsUltrametricDist.norm_add_le_max (σ x - x) x`. Rewrite `h` using `[sub_add_cancel, hnx]`. Conclude with `h.trans (max_le hε.le le_rfl)`. Assume the negation of the conclusion as `hne`. Establish `hne' : σ x - x ≠ 0` using `sub_ne_zero.mpr hne`.

Use `set S := ∑ i ∈ Finset.range (l ^ n), σ x ^ i * x ^ (l ^ n - 1 - i) with hSdef`. Establish `hS : S = 1`. Establish `h` using `geom_sum₂_mul (σ x) x (l ^ n)`. Rewrite `h` using `[hy, hx]`. Conclude with `mul_right_cancel₀ hne' (h.trans (one_mul _).symm)`.

Establish `hterm : ∀ i ∈ Finset.range (l ^ n), ‖σ x ^ i * x ^ (l ^ n - 1 - i) - 1‖ ≤ ‖σ x - x‖`. Introduce `i hi`. Establish `hi' : i ≤ l ^ n - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h1 : (1 : Om l) = x ^ i * x ^ (l ^ n - 1 - i)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hi', hxq]`. Rewrite using `[h1, ← sub_mul, norm_mul, norm_pow, hnx, one_pow, mul_one]`. Conclude with `norm_pow_sub_pow_le_norm_sub hnx.le hny i`. Establish `hsum : ‖S - ((l ^ n : ℕ) : Om l)‖ ≤ ‖σ x - x‖`.

Establish `h : ((l ^ n : ℕ) : Om l) = ∑ i ∈ Finset.range (l ^ n), (1 : Om l)` using `by simp`. Rewrite using `[h, hSdef, ← Finset.sum_sub_distrib]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm`. Establish `hlq : ‖((l ^ n : ℕ) : Om l)‖ < 1`. Rewrite using `[Nat.cast_pow, norm_pow]`.

Conclude with `pow_lt_one₀ (norm_nonneg _) norm_prime_lt_one_algClosure hn.ne'`. Establish `hq1 : ‖((l ^ n : ℕ) : Om l) - 1‖ = 1`. Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact hlq.ne), norm_neg, norm_one]`. Conclude with `max_eq_right hlq.le`. Establish `key : ‖S - 1‖ = 1`.

Establish `e : S - 1 = (((l ^ n : ℕ) : Om l) - 1) + (S - ((l ^ n : ℕ) : Om l))` using `by ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hq1]; exact (hsum.trans_lt hε).ne'), hq1]`. Conclude with `max_eq_left (hsum.trans hε.le)`. Rewrite `key` using `[hS, sub_self, norm_zero]`. Conclude with `zero_ne_one key`.
-/
private theorem fixes_root_of_unity_of_inertia_like {l : ℕ} [Fact l.Prime] (σ : GQ l)
    (hσ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) (n : ℕ) (hn : 0 < n) (x : Om l)
    (hx : x ^ l ^ n = x) : σ x = x := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl1
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hxq : x ^ (l ^ n - 1) = 1 := by
    have h : x ^ (l ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 h
  have hnx : ‖x‖ = 1 := by
    have h := congrArg norm hxq
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by omega)).mp h
  have hy : σ x ^ l ^ n = σ x := by rw [← map_pow, hx]
  have hε : ‖σ x - x‖ < 1 := hσ x hnx.le
  have hny : ‖σ x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (σ x - x) x
    rw [sub_add_cancel, hnx] at h
    exact h.trans (max_le hε.le le_rfl)
  by_contra hne
  have hne' : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range (l ^ n), σ x ^ i * x ^ (l ^ n - 1 - i) with hSdef

  have hS : S = 1 := by
    have h := geom_sum₂_mul (σ x) x (l ^ n)
    rw [hy, hx] at h
    exact mul_right_cancel₀ hne' (h.trans (one_mul _).symm)

  have hterm : ∀ i ∈ Finset.range (l ^ n),
      ‖σ x ^ i * x ^ (l ^ n - 1 - i) - 1‖ ≤ ‖σ x - x‖ := by
    intro i hi
    have hi' : i ≤ l ^ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (1 : Om l) = x ^ i * x ^ (l ^ n - 1 - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi', hxq]
    rw [h1, ← sub_mul, norm_mul, norm_pow, hnx, one_pow, mul_one]
    exact norm_pow_sub_pow_le_norm_sub hnx.le hny i
  have hsum : ‖S - ((l ^ n : ℕ) : Om l)‖ ≤ ‖σ x - x‖ := by
    have h : ((l ^ n : ℕ) : Om l) = ∑ i ∈ Finset.range (l ^ n), (1 : Om l) := by simp
    rw [h, hSdef, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
  have hlq : ‖((l ^ n : ℕ) : Om l)‖ < 1 := by
    rw [Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_prime_lt_one_algClosure hn.ne'
  have hq1 : ‖((l ^ n : ℕ) : Om l) - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlq.ne), norm_neg, norm_one]
    exact max_eq_right hlq.le
  have key : ‖S - 1‖ = 1 := by
    have e : S - 1 = (((l ^ n : ℕ) : Om l) - 1) + (S - ((l ^ n : ℕ) : Om l)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hq1]; exact (hsum.trans_lt hε).ne'), hq1]
    exact max_eq_left (hsum.trans hε.le)
  rw [hS, sub_self, norm_zero] at key
  exact zero_ne_one key

/- English proof (translation)
Introduce `l _ K`. Take `⟨φ, hφ⟩` from `(GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).1`. Take `⟨z, hzc, hzadd, hzval⟩` from `GlobalTheory.UnramifiedDegree.exists_degree l (fun n hn σ => GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l n hn σ) (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).2`. Establish `hz1 : z 1 = 0` using `by simpa using hzadd 1 1`. Establish `hzφ : z φ = 1`.

Establish `h` using `hzval φ 1 (fun n hn x hx => by rw [pow_one]; exact hφ n hn x hx)`. Simplify using `using h`. Establish `hzpow : ∀ m : ℕ, z (φ ^ m) = m`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp [hz1]`. Consider the case `succ m ih`. Rewrite using `[pow_succ, hzadd, ih, hzφ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfix : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0`. Introduce `σ hσ`. Establish `h` using `hzval σ 0 (fun n hn x hx => by`. Rewrite using `[pow_zero, pow_one]`. Conclude with `fixes_root_of_unity_of_inertia_like σ hσ n hn x hx)`.

Simplify using `using h`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN, hmem⟩ : ∃ N : ℕ, 0 < N ∧ φ ^ N ∈ GK K := by`. Establish `: FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l))` using `K.2`. Set `g : ℕ → ((K : IntermediateField ℚ_[l] (Om l)) →ₐ[ℚ_[l]] Om l)` to `fun m => ((φ ^ m : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (K : IntermediateField ℚ_[l] (Om l)).val`. Establish `claim : ∀ i j, i < j → g i = g j → φ ^ (j - i) ∈ GK K`.

Introduce `i j hij hg`. Use `show φ ^ (j - i) ∈ (K : IntermediateField ℚ_[l] (Om l)).fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `h1 : (φ ^ i) x = (φ ^ j) x` using `DFunLike.congr_fun hg ⟨x, hx⟩`.

Establish `h2 : φ ^ j = φ ^ i * φ ^ (j - i)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hij.le]`. Rewrite `h1` using `[h2, AlgEquiv.mul_apply]`. Conclude with `((φ ^ i).injective h1).symm`. Take `⟨i, j, hij, hg⟩` from `Finite.exists_ne_map_eq_of_infinite g`.

Break down `Nat.lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `⟨j - i, by omega, claim i j h hg⟩`. Conclude with `⟨i - j, by omega, claim j i h hg.symm⟩`. Set `z' : ↥(GK K) → ℤ_[l]` to `fun σ => z σ`. Establish `hz'c : Continuous z'` using `hzc.comp continuous_subtype_val`.

Establish `hz'add : ∀ σ τ, z' (σ * τ) = z' σ + z' τ` using `fun σ τ => hzadd σ τ`. Set `f : ↥(GK K) →* Multiplicative ℤ_[l]` to `MonoidHom.mk' (fun σ => Multiplicative.ofAdd (z' σ)) (fun σ τ => by rw [hz'add]; rfl)`. Establish `hIK : IK K ≤ f.ker`. Unfold `IK`. Rewrite using `[Subgroup.closure_le]`.

Introduce `σ hσ`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Use `show Multiplicative.ofAdd (z σ) = 1`. Rewrite using `[hfix σ hσ, ofAdd_zero]`. Establish `hz'I : ∀ σ ∈ IK K, z' σ = 0`.

Introduce `σ hσ`. Establish `h` using `hIK hσ`. Rewrite `h` using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Multiplicative.ofAdd (z' σ) = 1 at h`. Conclude with `ofAdd_eq_one.mp h`.

Establish `h0 : ∃ σ, z' σ ≠ 0` using `⟨⟨φ ^ N, hmem⟩, by show z (φ ^ N) ≠ 0`. Rewrite using `[hzpow]`. Conclude with `Nat.cast_ne_zero.mpr hN.ne'⟩`. Take `⟨F, hF⟩` from `GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K`. Take `⟨ν, hνc, hνI, hνF⟩` from `exists_normalised (IK K) F hF z' hz'c hz'add hz'I h0`.

Use `⟨F, ν, hνc, hνI, hνF, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hF]`. Use `Subgroup.topologicalClosure_mono (sup_le ?_ ?_)` and prove the remaining obligations. Conclude with `Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert F _))`. Introduce `σ hσ`.

Conclude with `Subgroup.subset_closure (Set.mem_insert_of_mem F hσ)`.
-/
theorem exists_gen_degree : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l),
    ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 ∧
      (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  intro l _ K

  obtain ⟨φ, hφ⟩ := (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).1
  obtain ⟨z, hzc, hzadd, hzval⟩ := GlobalTheory.UnramifiedDegree.exists_degree l
    (fun n hn σ => GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l n hn σ)
    (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).2
  have hz1 : z 1 = 0 := by simpa using hzadd 1 1
  have hzφ : z φ = 1 := by
    have h := hzval φ 1 (fun n hn x hx => by rw [pow_one]; exact hφ n hn x hx)
    simpa using h
  have hzpow : ∀ m : ℕ, z (φ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hz1]
    | succ m ih =>
      rw [pow_succ, hzadd, ih, hzφ]
      push_cast
      ring

  have hfix : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0 := by
    intro σ hσ
    have h := hzval σ 0 (fun n hn x hx => by
      rw [pow_zero, pow_one]
      exact fixes_root_of_unity_of_inertia_like σ hσ n hn x hx)
    simpa using h

  obtain ⟨N, hN, hmem⟩ : ∃ N : ℕ, 0 < N ∧ φ ^ N ∈ GK K := by
    have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
    let g : ℕ → ((K : IntermediateField ℚ_[l] (Om l)) →ₐ[ℚ_[l]] Om l) := fun m =>
      ((φ ^ m : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (K : IntermediateField ℚ_[l] (Om l)).val
    have claim : ∀ i j, i < j → g i = g j → φ ^ (j - i) ∈ GK K := by
      intro i j hij hg
      show φ ^ (j - i) ∈ (K : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (φ ^ i) x = (φ ^ j) x := DFunLike.congr_fun hg ⟨x, hx⟩
      have h2 : φ ^ j = φ ^ i * φ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hij.le]
      rw [h2, AlgEquiv.mul_apply] at h1
      exact ((φ ^ i).injective h1).symm
    obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, claim i j h hg⟩
    · exact ⟨i - j, by omega, claim j i h hg.symm⟩

  let z' : ↥(GK K) → ℤ_[l] := fun σ => z σ
  have hz'c : Continuous z' := hzc.comp continuous_subtype_val
  have hz'add : ∀ σ τ, z' (σ * τ) = z' σ + z' τ := fun σ τ => hzadd σ τ
  let f : ↥(GK K) →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (z' σ)) (fun σ τ => by rw [hz'add]; rfl)
  have hIK : IK K ≤ f.ker := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z σ) = 1
    rw [hfix σ hσ, ofAdd_zero]
  have hz'I : ∀ σ ∈ IK K, z' σ = 0 := by
    intro σ hσ
    have h := hIK hσ
    rw [MonoidHom.mem_ker] at h
    change Multiplicative.ofAdd (z' σ) = 1 at h
    exact ofAdd_eq_one.mp h
  have h0 : ∃ σ, z' σ ≠ 0 := ⟨⟨φ ^ N, hmem⟩, by
    show z (φ ^ N) ≠ 0
    rw [hzpow]
    exact Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨F, hF⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨ν, hνc, hνI, hνF⟩ := exists_normalised (IK K) F hF z' hz'c hz'add hz'I h0
  refine ⟨F, ν, hνc, hνI, hνF, ?_⟩
  rw [eq_top_iff, ← hF]
  refine Subgroup.topologicalClosure_mono (sup_le ?_ ?_)
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert F _))
  · intro σ hσ
    exact Subgroup.subset_closure (Set.mem_insert_of_mem F hσ)

end GlobalTheory.UnramGen
