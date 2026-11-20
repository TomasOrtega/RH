import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedElementLthPowerModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemInertiaInvariantsCyclotomicAlgebraIffStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycRoots

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨n, hn⟩` from `hx`.

Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq (x : Ω) hp.pos`. Establish `hyA : y ∈ A` using `mem_of_pow_mem A hp.ne_zero (hy ▸ x.2)`. Establish `e : (⟨y, hyA⟩ : A) ^ l = x` using `Subtype.ext (by simpa using hy)`. Use `⟨⟨y, hyA⟩, mem_cycAlg_of_pow (n := n + 1) ?_, 0, by rw [e]; ring⟩` and prove the remaining obligations. Rewrite using `[pow_succ', pow_mul, e, hn]`.

Consider the case `algebraMap a`. Take `⟨b, z, h⟩` from `GlobalTheory.T.fixed_element_lth_power_mod l Ω A hA a`. Conclude with `⟨algebraMap (fixA A) A b, Subalgebra.algebraMap_mem _ b, z, h⟩`. Consider the case `add a b _ _ iha ihb`. Take `⟨y, hy, z, rfl⟩` from `iha`.

Take `⟨y', hy', z', rfl⟩` from `ihb`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp y y'`. Use `⟨y + y', Subalgebra.add_mem _ hy hy', z + z' - y * y' * r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `mul a b _ _ iha ihb`. Take `⟨y, hy, z, rfl⟩` from `iha`. Take `⟨y', hy', z', rfl⟩` from `ihb`. Use `⟨y * y', Subalgebra.mul_mem _ hy hy', z * y' ^ l + y ^ l * z' + (l : A) * z * z', ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem frob_cycAlg (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (x : A) (hx : x ∈ cycAlg l A) :
    ∃ y ∈ cycAlg l A, ∃ z : A, x = y ^ l + (l : A) * z := by
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hp.pos
    have hyA : y ∈ A := mem_of_pow_mem A hp.ne_zero (hy ▸ x.2)
    have e : (⟨y, hyA⟩ : A) ^ l = x := Subtype.ext (by simpa using hy)
    refine ⟨⟨y, hyA⟩, mem_cycAlg_of_pow (n := n + 1) ?_, 0, by rw [e]; ring⟩
    rw [pow_succ', pow_mul, e, hn]
  | algebraMap a =>
    obtain ⟨b, z, h⟩ := GlobalTheory.T.fixed_element_lth_power_mod l Ω A hA a
    exact ⟨algebraMap (fixA A) A b, Subalgebra.algebraMap_mem _ b, z, h⟩
  | add a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp y y'
    refine ⟨y + y', Subalgebra.add_mem _ hy hy', z + z' - y * y' * r, ?_⟩
    rw [hr]; ring
  | mul a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    refine ⟨y * y', Subalgebra.mul_mem _ hy hy', z * y' ^ l + y ^ l * z' + (l : A) * z * z', ?_⟩
    rw [mul_pow]; ring

/- English proof (translation)
Introduce `l _ hl2 Ω _ _ _ A hA v hv hl0 hl1`. Establish `hp : l.Prime` using `Fact.out`. Establish `hl3 : 3 ≤ l` using `by have := hp.two_le; omega`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`.

Establish `hF : ∀ x : A, x ∈ cycAlg l A ↔ (x : Ω) ∈ Fix Ω (ineCyc l A)`. Introduce `x`. Rewrite using `[GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff l Ω A hA x]`. Conclude with `⟨fun h g => h g g.2, fun h s hs => h ⟨s, hs⟩⟩`. Use `haveI : NeZero ((l ^ 2 : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hp.pos 2).ne'⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 2)`. Establish `hζA : ζ ∈ A` using `mem_of_pow_mem A (pow_pos hp.pos 2).ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)`. Establish `hζF : ζ ∈ Fix Ω (ineCyc l A)` using `(hF ⟨ζ, hζA⟩).1 (mem_cycAlg_of_pow (n := 2) (Subtype.ext (by simpa using hζ.pow_eq_one)))`. Use `set c : Ω := ζ - 1 with hc`. Establish `hcF : c ∈ Fix Ω (ineCyc l A)` using `Subfield.sub_mem _ hζF (Subfield.one_mem _)`.

Establish `hequiv : v.IsEquiv A.valuation` using `Valuation.isEquiv_iff_val_le_one.2 fun {x} => by rw [hv, A.valuation_le_one_iff]`. Establish `hvc : v c ^ (l * (l - 1)) = v (l : Ω)`. Establish `h` using `GlobalTheory.valuation_zeta_sub_one_pow_totient l Ω A 2 ζ (by norm_num) hζ`. Rewrite `h` using `[Nat.totient_prime_pow hp (by norm_num), ← map_pow]`. Rewrite using `[← map_pow, hequiv.eq_iff]`.

Simplify using `using h`. Establish `hN : l * (l - 1) ≠ 0` using `Nat.mul_ne_zero (by omega) (by omega)`. Establish `hc0 : 0 < v c`. Break down `(zero_le : 0 ≤ v c).eq_or_lt with h | h` into its components or cases. Rewrite `hvc` using `[← h, zero_pow hN]`.

Conclude with `absurd hvc hl0.ne`. Conclude with `h`. Establish `hc1 : v c < 1`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hvc ▸ one_le_pow₀ (not_lt.1 h)) (not_le.2 hl1)`.

Establish `hcne : c ≠ 0` using `fun h => by rw [h, map_zero] at hc0; exact lt_irrefl _ hc0`. Use `set r : ℝ≥0 := v c ^ l with hr`. Establish `hr0 : 0 < r` using `pow_pos hc0 l`. Establish `hr1 : r < 1` using `pow_lt_one₀ hc0.le hc1 hp.ne_zero`. Establish `hlr : v (l : Ω) ≤ r * r`.

Rewrite using `[← hvc, pow_mul, ← hr, ← sq]`. Conclude with `pow_le_pow_of_le_one hr0.le hr1.le (by omega)`. Use `⟨r, hr1, fun u hu => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hu0 : u = 0`. Use `⟨0, Subfield.zero_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[hu0, zero_pow hp.ne_zero, sub_zero, map_zero]`. Conclude with `zero_le`. Establish `hvu : 0 < v u` using `(Valuation.pos_iff v).2 hu0`. Take `⟨k, hk1, hk2⟩` from `NNReal.exists_mem_Ioc_zpow hvu.ne' ((one_lt_inv₀ hr0).2 hr1)`. Use `set d : Ω := c ^ (k + 1) with hd`.

Establish `hdF : d ∈ Fix Ω (ineCyc l A)` using `Subfield.zpow_mem _ hcF _`. Establish `hdne : d ≠ 0` using `zpow_ne_zero _ hcne`. Establish `hvd : v (d ^ l) = r ^ (k + 1)`. Rewrite using `[map_pow, hd, map_zpow₀, hr, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`. Establish `hrk : 0 < r ^ (k + 1)` using `zpow_pos hr0 _`.

Establish `h1 : v (u * d ^ l) ≤ 1`. Rewrite using `[map_mul, hvd]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : r ≤ v (u * d ^ l)`. Rewrite using `[map_mul, hvd]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_add_one₀ hr0.ne', ← mul_assoc, ← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow, one_mul]`. Use `_ ≤ v u * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk1.le zero_le`. Establish `hu'F : u * d ^ l ∈ Fix Ω (ineCyc l A)` using `Subfield.mul_mem _ hu (Subfield.pow_mem _ hdF _)`. Take `⟨y, hy, z, e⟩` from `frob_cycAlg l Ω A hA ⟨u * d ^ l, (hv _).1 h1⟩ ((hF _).2 hu'F)`.

Establish `e' : u * d ^ l = (y : Ω) ^ l + (l : Ω) * (z : Ω)`. Simplify using `using congrArg (fun t : A => (t : Ω)) e`. Use `⟨(y : Ω) / d, Subfield.div_mem _ ((hF y).1 hy) hdF, ?_⟩` and prove the remaining obligations. Establish `e2 : (u - ((y : Ω) / d) ^ l) * d ^ l = (l : Ω) * (z : Ω)`. Rewrite using `[sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdne), e']`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : v (u - ((y : Ω) / d) ^ l) * r ^ (k + 1) ≤ r * v u * r ^ (k + 1)`. Rewrite using `[← hvd, mul_assoc, ← map_mul, ← map_mul, e2, map_mul v (l : Ω)]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h3 hrk`.
-/
theorem approxRoot_fix_ineCyc : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) →
    0 < v (l : Ω) → v (l : Ω) < 1 → ApproxRoot l v (Fix Ω (ineCyc l A)) := by
  intro l _ hl2 Ω _ _ _ A hA v hv hl0 hl1
  have hp : l.Prime := Fact.out
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hF : ∀ x : A, x ∈ cycAlg l A ↔ (x : Ω) ∈ Fix Ω (ineCyc l A) := by
    intro x
    rw [GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff l Ω A hA x]
    exact ⟨fun h g => h g g.2, fun h s hs => h ⟨s, hs⟩⟩
  haveI : NeZero ((l ^ 2 : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hp.pos 2).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 2)
  have hζA : ζ ∈ A := mem_of_pow_mem A (pow_pos hp.pos 2).ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
  have hζF : ζ ∈ Fix Ω (ineCyc l A) :=
    (hF ⟨ζ, hζA⟩).1 (mem_cycAlg_of_pow (n := 2) (Subtype.ext (by simpa using hζ.pow_eq_one)))
  set c : Ω := ζ - 1 with hc
  have hcF : c ∈ Fix Ω (ineCyc l A) := Subfield.sub_mem _ hζF (Subfield.one_mem _)
  have hequiv : v.IsEquiv A.valuation :=
    Valuation.isEquiv_iff_val_le_one.2 fun {x} => by rw [hv, A.valuation_le_one_iff]
  have hvc : v c ^ (l * (l - 1)) = v (l : Ω) := by
    have h := GlobalTheory.valuation_zeta_sub_one_pow_totient l Ω A 2 ζ (by norm_num) hζ
    rw [Nat.totient_prime_pow hp (by norm_num), ← map_pow] at h
    rw [← map_pow, hequiv.eq_iff]
    simpa using h
  have hN : l * (l - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hc0 : 0 < v c := by
    rcases (zero_le : 0 ≤ v c).eq_or_lt with h | h
    · rw [← h, zero_pow hN] at hvc; exact absurd hvc hl0.ne
    · exact h
  have hc1 : v c < 1 := by
    by_contra h
    exact absurd (hvc ▸ one_le_pow₀ (not_lt.1 h)) (not_le.2 hl1)
  have hcne : c ≠ 0 := fun h => by rw [h, map_zero] at hc0; exact lt_irrefl _ hc0
  set r : ℝ≥0 := v c ^ l with hr
  have hr0 : 0 < r := pow_pos hc0 l
  have hr1 : r < 1 := pow_lt_one₀ hc0.le hc1 hp.ne_zero
  have hlr : v (l : Ω) ≤ r * r := by
    rw [← hvc, pow_mul, ← hr, ← sq]
    exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  refine ⟨r, hr1, fun u hu => ?_⟩
  by_cases hu0 : u = 0
  · refine ⟨0, Subfield.zero_mem _, ?_⟩
    rw [hu0, zero_pow hp.ne_zero, sub_zero, map_zero]; exact zero_le
  have hvu : 0 < v u := (Valuation.pos_iff v).2 hu0
  obtain ⟨k, hk1, hk2⟩ := NNReal.exists_mem_Ioc_zpow hvu.ne' ((one_lt_inv₀ hr0).2 hr1)

  set d : Ω := c ^ (k + 1) with hd
  have hdF : d ∈ Fix Ω (ineCyc l A) := Subfield.zpow_mem _ hcF _
  have hdne : d ≠ 0 := zpow_ne_zero _ hcne
  have hvd : v (d ^ l) = r ^ (k + 1) := by
    rw [map_pow, hd, map_zpow₀, hr, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hrk : 0 < r ^ (k + 1) := zpow_pos hr0 _
  have h1 : v (u * d ^ l) ≤ 1 := by
    rw [map_mul, hvd]
    calc v u * r ^ (k + 1) ≤ r⁻¹ ^ (k + 1) * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk2 zero_le
      _ = 1 := by rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have h2 : r ≤ v (u * d ^ l) := by
    rw [map_mul, hvd]
    calc r = r⁻¹ ^ k * r ^ (k + 1) := by
          rw [zpow_add_one₀ hr0.ne', ← mul_assoc, ← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow, one_mul]
      _ ≤ v u * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk1.le zero_le
  have hu'F : u * d ^ l ∈ Fix Ω (ineCyc l A) := Subfield.mul_mem _ hu (Subfield.pow_mem _ hdF _)
  obtain ⟨y, hy, z, e⟩ := frob_cycAlg l Ω A hA ⟨u * d ^ l, (hv _).1 h1⟩ ((hF _).2 hu'F)
  have e' : u * d ^ l = (y : Ω) ^ l + (l : Ω) * (z : Ω) := by
    simpa using congrArg (fun t : A => (t : Ω)) e
  refine ⟨(y : Ω) / d, Subfield.div_mem _ ((hF y).1 hy) hdF, ?_⟩
  have e2 : (u - ((y : Ω) / d) ^ l) * d ^ l = (l : Ω) * (z : Ω) := by
    rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdne), e']; ring
  have h3 : v (u - ((y : Ω) / d) ^ l) * r ^ (k + 1) ≤ r * v u * r ^ (k + 1) := by
    rw [← hvd, mul_assoc, ← map_mul, ← map_mul, e2, map_mul v (l : Ω)]
    calc v (l : Ω) * v (z : Ω) ≤ v (l : Ω) * 1 := mul_le_mul_of_nonneg_left ((hv _).2 z.2) zero_le
      _ = v (l : Ω) := mul_one _
      _ ≤ r * r := hlr
      _ ≤ r * v (u * d ^ l) := mul_le_mul_of_nonneg_left h2 zero_le
  exact le_of_mul_le_mul_right h3 hrk

end GlobalTheory.RecOne.CycRoots
