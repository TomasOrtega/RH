import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneRegularSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDiagonalSectionDifference
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace HyperplaneQuotientBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c hc`. Establish `h` using `Subalgebra.mul_mem _ (hs c hc) (ht c hc)`. Establish `heq : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + b') k)) = (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)))`. Rewrite using `[mul_mul_mul_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k)]`. Use `congr 1`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `h`.
-/
theorem mul_mem {b b' : K → ℤ} {s t : Ω} (hs : s ∈ chartLatQ y b 1) (ht : t ∈ chartLatQ y b' 1) :
    s * t ∈ chartLatQ y (b + b') 1 := by
  intro c hc
  have h := Subalgebra.mul_mem _ (hs c hc) (ht c hc)
  have heq : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + b') k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact h

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `c _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Establish `h` using `mul_mem ih hσ`. Establish `hb : (n : ℤ) • e + e = ((n + 1 : ℕ) : ℤ) • e`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`. Rewrite `h` using `[hb]`.

Rewrite using `[pow_succ]`. Conclude with `h`.
-/
theorem pow_mem {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1) (n : ℕ) :
    σ ^ n ∈ chartLatQ y ((n : ℤ) • e) 1 := by
  induction n with
  | zero =>
    intro c _
    simp
  | succ n ih =>
    have h := mul_mem ih hσ
    have hb : (n : ℤ) • e + e = ((n + 1 : ℕ) : ℤ) • e := by
      push_cast
      rw [add_smul, one_smul]
    rw [hb] at h
    rw [pow_succ]
    exact h

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `n generalizing b s with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Establish `hσs : σ * s ∈ chartLatQ y (b + e) 1`. Establish `h'` using `mul_mem hσ hs`.

Rewrite `h'` using `[add_comm e b]`. Then use the resulting hypothesis. Use `hreg b s hs (ih (b + e) (σ * s) hσs ?_)` and prove the remaining obligations. Establish `hb : b + ((n + 1 : ℕ) : ℤ) • e - 1 = b + e + (n : ℤ) • e - 1`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Rewrite `h` using `[hb, pow_succ, mul_assoc]`. Conclude with `h`.
-/
theorem pow_regular {c : ∀ k, ι k} {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1)
    (hreg : ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
      σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + e - 1) 1 → s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    (n : ℕ) (b : K → ℤ) (s : Ω) (hs : s ∈ chartLatQ y b 1)
    (h : σ ^ n * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (n : ℤ) • e - 1) 1) :
    s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  induction n generalizing b s with
  | zero => simpa using h
  | succ n ih =>
    have hσs : σ * s ∈ chartLatQ y (b + e) 1 := by
      have h' := mul_mem hσ hs
      rwa [add_comm e b] at h'
    refine hreg b s hs (ih (b + e) (σ * s) hσs ?_)
    have hb : b + ((n + 1 : ℕ) : ℤ) • e - 1 = b + e + (n : ℤ) • e - 1 := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hb, pow_succ, mul_assoc] at h
    exact h

/- English proof (translation)
Take `⟨G, hG⟩` from `hF K ι Ω y b 1 hy`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (G : Set Ω)) fun s hs => ?_` and prove the remaining obligations. Take `⟨N, hN, hNs⟩` from `ChartDenominator.proof K ι Ω y b 1 s hs`. Establish `hmem : (N : Ω) * s ∈ Submodule.span ℚ (G : Set Ω)`. Rewrite `hNs` using `[← hG]`.

Conclude with `(AddSubgroup.closure_le (Submodule.span ℚ (G : Set Ω)).toAddSubgroup).mpr Submodule.subset_span hNs`. Establish `hN0 : (N : Ω) ≠ 0` using `by exact_mod_cast (show N ≠ 0 by omega)`. Establish `hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s)`. Rewrite using `[Rat.smul_def]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hs']`. Conclude with `Submodule.smul_mem _ _ hmem`.
-/
theorem finiteDimensional (hF : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (b : K → ℤ) :
    FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨G, hG⟩ := hF K ι Ω y b 1 hy
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (G : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have hmem : (N : Ω) * s ∈ Submodule.span ℚ (G : Set Ω) := by
    rw [← hG] at hNs
    exact (AddSubgroup.closure_le (Submodule.span ℚ (G : Set Ω)).toAddSubgroup).mpr Submodule.subset_span hNs
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hmem

/- English proof (translation)
Establish `hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Simplify using `only [chartDivSec, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mulLeft_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hts⟩`. Rewrite using `[← hts, mul_div_cancel_left₀ _ hm0]`.

Conclude with `ht`. Introduce `h`. Conclude with `⟨_, h, mul_div_cancel₀ _ hm0⟩`.
-/
theorem mem_chartDivSec {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (s : chartLatQ y b 1) :
    s ∈ chartDivSec y c b ↔ (s : Ω) / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  simp only [chartDivSec, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [← hts, mul_div_cancel_left₀ _ hm0]
    exact ht
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ hm0⟩

/- English proof (translation)
Establish `hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Establish `hmem : ∀ t ∈ chartLatQ y (b - 1) 1, (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1` using `fun t ht => mul_mem_chartLatQ b ht`. Set `φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b` to `{ toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, hmem t t.2⟩, Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩ map_add' := fun s t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_add, mul_add]`. Use the proof step `map_smul' := fun r t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }`.

Establish `hinj : Function.Injective φ` using `fun s t h => by`. Establish `h'` using `congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h`. Conclude with `Subtype.ext (mul_left_cancel₀ hm0 h')`. Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hinj`. Establish `h2` using `Submodule.finrank_quotient_add_finrank (chartDivSec y c b)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_quot_add_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ)
    [FiniteDimensional ℚ (chartLatQ y b 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) + Module.finrank ℚ (chartLatQ y (b - 1) 1) ≤
      Module.finrank ℚ (chartLatQ y b 1) := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hmem : ∀ t ∈ chartLatQ y (b - 1) 1, (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 :=
    fun t ht => mul_mem_chartLatQ b ht
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, hmem t t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Submodule.finrank_quotient_add_finrank (chartDivSec y c b)
  omega

/- English proof (translation)
Substitute `hbd` using the available equality. Establish `hmem : ∀ s ∈ chartLatQ y b 1, τ * s ∈ chartLatQ y (b + d) 1` using `fun s hs => by`. Establish `h` using `mul_mem hτ hs`. Rewrite `h` using `[add_comm d b]`. Then use the resulting hypothesis. Set `φ : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y (b + d) 1` to `{ toFun := fun s => ⟨τ * s, hmem s s.2⟩ map_add' := fun s t => Subtype.ext (mul_add _ _ _) map_smul' := fun r s => Subtype.ext (mul_smul_comm r τ (s : Ω)) }`.

Establish `hle : chartDivSec y c b ≤ (chartDivSec y c (b + d)).comap φ`. Introduce `s hs`. Rewrite using `[Submodule.mem_comap, mem_chartDivSec hc]`. Rewrite `hs` using `[mem_chartDivSec hc]`. Establish `h` using `mul_mem hτ hs`.

Rewrite `h` using `[show d + (b - 1) = b + d - 1 by abel]`. Use `show τ * (s : Ω) / _ ∈ _`. Rewrite using `[mul_div_assoc]`. Conclude with `h`. Establish `hinj : Function.Injective (Submodule.mapQ _ _ φ hle)`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H s`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]`.

Rewrite using `[Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]`. Conclude with `hreg s s.2 hx`. Conclude with `LinearMap.finrank_le_finrank_of_injective hinj`.
-/
theorem finrank_quot_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {b d b' : K → ℤ} (hbd : b + d = b') {τ : Ω}
    (hτ : τ ∈ chartLatQ y d 1)
    (hreg : ∀ s ∈ chartLatQ y b 1, τ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b' - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    [FiniteDimensional ℚ (chartLatQ y b' 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) ≤
      Module.finrank ℚ (chartLatQ y b' 1 ⧸ chartDivSec y c b') := by
  subst hbd
  have hmem : ∀ s ∈ chartLatQ y b 1, τ * s ∈ chartLatQ y (b + d) 1 := fun s hs => by
    have h := mul_mem hτ hs
    rwa [add_comm d b] at h
  let φ : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y (b + d) 1 :=
    { toFun := fun s => ⟨τ * s, hmem s s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r τ (s : Ω)) }
  have hle : chartDivSec y c b ≤ (chartDivSec y c (b + d)).comap φ := by
    intro s hs
    rw [Submodule.mem_comap, mem_chartDivSec hc]
    rw [mem_chartDivSec hc] at hs
    have h := mul_mem hτ hs
    rw [show d + (b - 1) = b + d - 1 by abel] at h
    show τ * (s : Ω) / _ ∈ _
    rw [mul_div_assoc]
    exact h
  have hinj : Function.Injective (Submodule.mapQ _ _ φ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]
      exact hreg s s.2 hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

end HyperplaneQuotientBound

open HyperplaneQuotientBound in

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D a c hD hV _ hc`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM1, hMa⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, a k ≤ M := by`. Use `⟨(∑ k, (a k).toNat) + 1, Nat.le_add_left _ _, fun k => ?_⟩` and prove the remaining obligations. Establish `h1 : (a k).toNat ≤ ∑ k, (a k).toNat` using `Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Establish `h2` using `Int.self_le_toNat (a k)`.

Establish `h3 : ((a k).toNat : ℤ) ≤ ((∑ k, (a k).toNat : ℕ) : ℤ)` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h3 ⊢`. Use linear arithmetic over natural numbers and integers. Use `set e : K → ℕ := fun k => ((M : ℤ) - a k).toNat with he`. Establish `hek : ∀ k, (e k : ℤ) = M - a k` using `fun k => Int.toNat_of_nonneg (sub_nonneg.mpr (hMa k))`.

Take `⟨σ, -, hσ, hreg⟩` from `hR K ι Ω y c e hc`. Establish `hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => ⟨c k, hc k⟩`. Take `⟨C, hC⟩` from `hS K ι Ω y D hD hV`. Take `⟨N, hN⟩` from `eventually_atTop.mp hC`. Use `⟨C * (M : ℝ) ^ (D - 1), eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩` and prove the remaining obligations.

Establish `hbd : (n : ℤ) • a + (n : ℤ) • (fun k => (e k : ℤ)) = ((n * M : ℕ) : ℤ) • (1 : K → ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek, Pi.one_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `finiteDimensional hF hy (((n * M : ℕ) : ℤ) • (1 : K → ℤ))` as an intermediate fact. Establish `h1` using `finrank_quot_le hc hbd (pow_mem hσ n) (fun s hs h => pow_regular hσ hreg n _ s hs (by rwa [← hbd] at h))`. Establish `h2` using `finrank_quot_add_le hc (((n * M : ℕ) : ℤ) • (1 : K → ℤ))`. Establish `h3` using `hN (n * M) (le_trans hn (Nat.le_mul_of_pos_right n hM1))`. Establish `h1' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤ (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸ chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ)` using `by exact_mod_cast h1`.

Establish `h2' : (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸ chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) + (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) ≤ (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1) …` using `by exact_mod_cast h2`. Establish `hpow : ((n * M : ℕ) : ℝ) ^ (D - 1) = (M : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[hpow]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem HyperplaneQuotientBound.proof (hR : HyperplaneRegularSection.Statement)
    (hS : DiagonalSectionDifference.Statement) (hF : SectionLatticeFinite.Statement) :
    HyperplaneQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a c hD hV _ hc
  obtain ⟨M, hM1, hMa⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, a k ≤ M := by
    refine ⟨(∑ k, (a k).toNat) + 1, Nat.le_add_left _ _, fun k => ?_⟩
    have h1 : (a k).toNat ≤ ∑ k, (a k).toNat :=
      Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (a k)
    have h3 : ((a k).toNat : ℤ) ≤ ((∑ k, (a k).toNat : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 ⊢
    omega
  set e : K → ℕ := fun k => ((M : ℤ) - a k).toNat with he
  have hek : ∀ k, (e k : ℤ) = M - a k := fun k => Int.toNat_of_nonneg (sub_nonneg.mpr (hMa k))
  obtain ⟨σ, -, hσ, hreg⟩ := hR K ι Ω y c e hc
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  obtain ⟨C, hC⟩ := hS K ι Ω y D hD hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨C * (M : ℝ) ^ (D - 1), eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have hbd : (n : ℤ) • a + (n : ℤ) • (fun k => (e k : ℤ)) = ((n * M : ℕ) : ℤ) • (1 : K → ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek, Pi.one_apply]
    push_cast
    ring
  have := finiteDimensional hF hy (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h1 := finrank_quot_le hc hbd (pow_mem hσ n) (fun s hs h => pow_regular hσ hreg n _ s hs (by rwa [← hbd] at h))
  have h2 := finrank_quot_add_le hc (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h3 := hN (n * M) (le_trans hn (Nat.le_mul_of_pos_right n hM1))
  have h1' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) := by exact_mod_cast h1
  have h2' : (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) +
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1) : ℝ) := by exact_mod_cast h2
  have hpow : ((n * M : ℕ) : ℝ) ^ (D - 1) = (M : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by
    push_cast
    ring
  rw [hpow] at h3
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
