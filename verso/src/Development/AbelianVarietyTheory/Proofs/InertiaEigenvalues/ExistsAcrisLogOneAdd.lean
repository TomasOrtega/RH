import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.AdicMaps.exists_acris_completion l`. Take `⟨y, hy⟩` from `Model.pc_lim (l := l) (Per.Acris0 l) s hs`. Use `⟨e.symm y, fun r n hn => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hy r n hn`. Use `⟨e.symm z, e.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, e.apply_symm_apply, he]`. Conclude with `hz`.
-/
theorem acris_lim_pt (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = ((l : ℕ) : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := Model.pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨e.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨e.symm z, e.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, e.apply_symm_apply, he]
  exact hz

/- English proof (translation)
Introduce `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl`. Establish `hb1 : b ∈ 𝓞_ℂ_[l]`.

Rewrite using `[GlobalTheory.RingBasics.mem_OC]`. Use `(GlobalTheory.RingBasics.mem_OC _).1 a.2` as an intermediate fact. Rewrite `this` using `[← hb, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this`. Use `⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[frobenius_def, ← map_pow]`. Conclude with `congrArg _ (Subtype.ext hb)`.
-/
theorem frobenius_surjective_modP : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

/- English proof (translation)
The claim follows from `surjective_fontaineTheta frobenius_surjective_modP`.
-/
theorem θ_surjective : Function.Surjective (Per.θ l) :=
  surjective_fontaineTheta frobenius_surjective_modP

/- English proof (translation)
Take `⟨c, hc⟩` from `hw`. Take `⟨a, ha⟩` from `θ_surjective (l := l) c`. Establish `hz : Per.θ l (w - (l : Per.Ainf l) * a) = 0`. Rewrite using `[map_sub, map_mul, map_natCast, ha, hc, sub_self]`. Establish `hd : ∀ j : ℕ, ∃ d : Per.AinfP l, d ∈ Per.Acris0 l ∧ ((j.factorial : ℕ) : Per.AinfP l) * d = algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j`.

Introduce `j`. Take `⟨u, hu⟩` from `(GlobalTheory.RingBasics.isUnit_nat l _ j.factorial_ne_zero).exists_right_inv`. Establish `e : ((j.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j) = algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j`. Rewrite using `[← mul_assoc, hu, one_mul]`. Conclude with `⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l _ j _ hz e, e⟩`.

Use `choose d hdm hdd using hd`. Use `choose q hq using fun m : ℕ => GlobalTheory.RingBasics.exists_pow_div_factorial l m`. Set `ζ : ℤ_[l] →+* Per.AinfP l` to `(algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)`. Establish `hq' : ∀ m : ℕ, ((m.factorial : ℕ) : Per.AinfP l) * ζ (q m) = ((l : ℕ) : Per.AinfP l) ^ m`. Introduce `m`.

Establish `h` using `congrArg ζ (hq m)`. Rewrite `h` using `[map_mul, map_natCast, map_pow, map_natCast]`. Then use the resulting hypothesis. Establish `hg : (∑ m ∈ Finset.range (k + 1), ζ (q m) * algebraMap (Per.Ainf l) (Per.AinfP l) a ^ m * d (k - m)) ∈ Per.Acris0 l`. Use `Subalgebra.sum_mem _ fun m _ => mul_mem (mul_mem ?_ (pow_mem (Subalgebra.algebraMap_mem _ _) _)) (hdm _)` and prove the remaining obligations. Conclude with `Subalgebra.algebraMap_mem _ (Per.zA l (q m))`.

Use `⟨⟨_, hg⟩, ?_⟩` and prove the remaining obligations. Establish `hw' : algebraMap (Per.Ainf l) (Per.AinfP l) w = ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) a + algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a)`. Rewrite using `[map_sub, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `show _ * ∑ m ∈ Finset.range (k + 1), _ = _`.

Rewrite using `[hw', add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hmk : m ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)`. Establish `hf : ((k.factorial : ℕ) : Per.AinfP l) = ((k.choose m : ℕ) : Per.AinfP l) * ((m.factorial : ℕ) : Per.AinfP l) * (((k - m).factorial : ℕ) : Per.AinfP l)`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hmk]`.

Rewrite using `[hf, mul_pow, ← hq' m, ← hdd (k - m)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_divPow {w : Per.Ainf l} (hw : InJ w) (k : ℕ) :
    ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) w ^ k := by
  obtain ⟨c, hc⟩ := hw
  obtain ⟨a, ha⟩ := θ_surjective (l := l) c
  have hz : Per.θ l (w - (l : Per.Ainf l) * a) = 0 := by
    rw [map_sub, map_mul, map_natCast, ha, hc, sub_self]
  have hd : ∀ j : ℕ, ∃ d : Per.AinfP l, d ∈ Per.Acris0 l ∧ ((j.factorial : ℕ) : Per.AinfP l) * d =
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
    intro j
    obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ j.factorial_ne_zero).exists_right_inv
    have e : ((j.factorial : ℕ) : Per.AinfP l) *
        (u * algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
      rw [← mul_assoc, hu, one_mul]
    exact ⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l _ j _ hz e, e⟩
  choose d hdm hdd using hd
  choose q hq using fun m : ℕ => GlobalTheory.RingBasics.exists_pow_div_factorial l m
  let ζ : ℤ_[l] →+* Per.AinfP l := (algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)
  have hq' : ∀ m : ℕ, ((m.factorial : ℕ) : Per.AinfP l) * ζ (q m) = ((l : ℕ) : Per.AinfP l) ^ m := by
    intro m
    have h := congrArg ζ (hq m)
    rwa [map_mul, map_natCast, map_pow, map_natCast] at h
  have hg : (∑ m ∈ Finset.range (k + 1), ζ (q m) * algebraMap (Per.Ainf l) (Per.AinfP l) a ^ m *
      d (k - m)) ∈ Per.Acris0 l := by
    refine Subalgebra.sum_mem _ fun m _ => mul_mem (mul_mem ?_ (pow_mem (Subalgebra.algebraMap_mem _ _) _))
      (hdm _)
    exact Subalgebra.algebraMap_mem _ (Per.zA l (q m))
  refine ⟨⟨_, hg⟩, ?_⟩
  have hw' : algebraMap (Per.Ainf l) (Per.AinfP l) w = ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) a +
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) := by
    rw [map_sub, map_mul, map_natCast]
    ring
  show _ * ∑ m ∈ Finset.range (k + 1), _ = _
  rw [hw', add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hf : ((k.factorial : ℕ) : Per.AinfP l) = ((k.choose m : ℕ) : Per.AinfP l) *
      ((m.factorial : ℕ) : Per.AinfP l) * (((k - m).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hmk]
  rw [hf, mul_pow, ← hq' m, ← hdd (k - m)]
  ring

/- English proof (translation)
Introduce `l _ w hw`. Establish `hl : l.Prime` using `Fact.out`. Use `choose g hg using exists_divPow hw`. Set `s : ℕ → Per.Acris0 l` to `fun n => ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)`. Take `⟨y, hy⟩` from `acris_lim_pt s (by`.

Introduce `r n hn`. Establish `: ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r)`. Simplify using `only [s]`. Rewrite using `[← Finset.sum_Ico_eq_sub _ hn]`. Use `Finset.dvd_sum fun k hk => ?_` and prove the remaining obligations.

Establish `h1 : l ^ r ∣ k.factorial` using `Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1`. Establish `h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l)`. Conclude with `Nat.cast_dvd_cast (α := Per.Acris0 l) h1` after adjusting the coercions. Conclude with `(h2.mul_left _).mul_right _`. Conclude with `this)`.

Use `⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩` and prove the remaining obligations. Simplify using `only [s]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `h1 : n.factorial = n.factorial / (k + 1) * (k + 1)` using `(Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm`. Establish `h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1)`. Conclude with `congrArg (Nat.cast : ℕ → Per.AinfP l) h1` after adjusting the coercions. Rewrite using `[← hg (k + 1), Nat.factorial_succ]`. Generalize the expression as in `((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢`.

Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isLogJ : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), InJ w → ∃ y : Per.Acris l, IsLogJ w y := by
  intro l _ w hw
  have hl : l.Prime := Fact.out
  choose g hg using exists_divPow hw
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim_pt s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

end GlobalTheory.LogU
