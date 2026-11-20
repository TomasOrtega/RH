import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

/- English proof (translation)
Establish `hb : (⊥ : Subalgebra ℚ F) = ⊤` using `Subalgebra.bot_eq_top_of_finrank_eq_one h`. Set `e : ℚ ≃ₐ[ℚ] F` to `(Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)`. Rewrite using `[← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]`. Both sides reduce to the same expression.
-/
theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Establish `h1 : Module.finrank ℚ (maximalRealSubfield E) = 1`. Use `Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hE` using `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E) (𝓞 (maximalRealSubfield E)) E (𝓞 E)`.

Establish `hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤` using `h`. Rewrite `hE` using `[hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow]`. Establish `h2 : Module.finrank ℚ E = 2`. Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]`. Establish `h3` using `NumberField.abs_discr_gt_two (K := E) (by omega)`.

Establish `h4 : |(discr E : ℤ)| = 1` using `by rw [Int.abs_eq_natAbs, hE]; rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

/- English proof (translation)
Substitute `hS0 hc0` using the available equality. Establish `h1 : Ω ^ (t * f) ≠ 0` using `pow_ne_zero _ hΩ`. Establish `h2 : p ^ K ≠ 0` using `pow_ne_zero _ hp`. Establish `h3 : r ^ K ≠ 0` using `pow_ne_zero _ hr`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [div_pow, mul_pow, ← pow_mul, pow_add]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alg_id (c0 S0 X C Ω W cW P sgn p r : ℂ) (f t K : ℕ)
    (hS0 : S0 = C ^ t * X / (cW * (sgn * P) * W)) (hc0 : c0 = cW * P * (p / r) ^ K)
    (hΩ : Ω ≠ 0) (hp : p ≠ 0) (hr : r ≠ 0) (hW : W ≠ 0) (hcW : cW ≠ 0) (hP : P ≠ 0) (hsgn : sgn ≠ 0) :
    c0 * S0 / Ω ^ (t * f + 2 * K) = X * (C / Ω ^ f) ^ t * (sgn * (W * (Ω ^ 2 * r / p) ^ K))⁻¹ := by
  subst hS0 hc0
  have h1 : Ω ^ (t * f) ≠ 0 := pow_ne_zero _ hΩ
  have h2 : p ^ K ≠ 0 := pow_ne_zero _ hp
  have h3 : r ^ K ≠ 0 := pow_ne_zero _ hr
  field_simp
  simp only [div_pow, mul_pow, ← pow_mul, pow_add]
  field_simp
  ring

/- English proof (translation)
Establish `hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j)`. Introduce `i j hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Establish `e : i = j` using `(hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm`. Substitute `e` using the available equality.

Establish `hr : ComplexEmbedding.IsReal (φ i)` using `ComplexEmbedding.isReal_iff.mpr hij.symm`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i))) (InfinitePlace.isReal_mk_iff.mpr hr)`. Establish `hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j) hij`.

Simplify using `only [Sum.elim_inl] at hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl hij)]`. Conclude with `absurd hij (hreal i j)`. Conclude with `absurd hij.symm (hreal j i)`.

Simplify using `only [Sum.elim_inr] at hij`. Establish `hij' : φ i = φ j`. Simplify using `using congrArg ComplexEmbedding.conjugate hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl hij')]`.

Introduce `σ`. Take `⟨k, hk, -⟩` from `h σ`. Break down `hk with hk | hk` into its components or cases. Conclude with `⟨Sum.inl k, hk.symm⟩`. Conclude with `⟨Sum.inr k, hk.symm⟩`.

Establish `h1` using `Fintype.card_of_bijective hbij`. Rewrite `h1` using `[Fintype.card_sum, NumberField.Embeddings.card E ℂ]`. Establish `h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E)`. Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1`. Rewrite using `[Nat.cast_sub hk]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]`. Rewrite using `[this, Real.Gamma_nat_eq_factorial]`. Consider the case `succ n ih`. Establish `hpos : (k : ℝ) + n ≠ 0`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Check the signs of the components of the expression. Rewrite using `[Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

/- English proof (translation)
Use `⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Multiset.count_replicate]`.

Simplify using `[hj]`. Simplify using the standard rewrite rules.
-/
theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

/- English proof (translation)
Establish `hk : 1 ≤ 2 * s` using `by omega`. Rewrite using `[cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

/- English proof (translation)
Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

/- English proof (translation)
Introduce `hZ hSt hEis hJet hMod`. Introduce `K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS`. Take `⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩` from `hDat`. Establish `hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)` using `two_le_finrank hUn`. Establish `hc0 : condQ 𝔣 Q ≠ ⊥` using `by show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0`.

Conclude with `mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)`. Establish `hΩ0 : Ω₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)`. Take `⟨⟨z, hz⟩, -⟩` from `hZ E s hs`.

Take `⟨𝔠, X₀, δ₀, N, T, hAdm, hOver, hCalg, hA⟩` from `hMod K d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hCM hφι (condQ 𝔣 Q) y hc0`. Set `R₀ : Subring ℂ` to `(algebraicClosure ℚ ℂ).toSubring`. Take `⟨r, hr⟩` from `hEis E hf2 𝔠 s hs z hz R₀ 1 (one_mem _) (fun C => by show _ ∈ algebraicClosure ℚ ℂ`. Conclude with `mul_mem (one_mem _) (SubfieldClass.ratCast_mem _ _))`. Take `⟨ε, hε⟩` from `hJet`.

Set `ι₀ : R₀ →+* Qb` to `{ toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Use `letI : Algebra R₀ Qb := ι₀.toAlgebra`. Take `⟨x, hx⟩` from `hε E I 𝔠 hf2 R₀ s r hs Qb X₀ δ₀ N hAdm κ`. Take `⟨⟨g, hg⟩, hD⟩` from `(((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1`. Take `⟨u, hu⟩` from `exists_list_count κ`.

Establish `hDg` using `((hD g hg).2 κ u hu).1 S hS`. Establish `hxe` using `hx (algebraMap Qb ℂ) (fun a => rfl) φ (condQ 𝔣 Q) y 1 hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu`. Establish `hcard` using `card_eq_finrank hCM`. Establish `hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`.

Conclude with `this.ne'` after adjusting the coercions. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hε0 : ((ε : ℤ) : ℂ) ≠ 0` using `by exact_mod_cast ε.ne_zero`. Establish `hW : ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero hε0 (hA i).1)`. Establish `hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0`.

Establish `: (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s)`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt`. Establish `h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)|` using `abs_pos.2 (by exact_mod_cast discr_ne_zero _)`. Conclude with `mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hP : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)` using `Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity`. Conclude with `this.ne'` after adjusting the coercions. Establish `hrF : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ ≠ 0`. Rewrite using `[risingFactor_eq]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hP`. Establish `hS0 : S 0 = T.C ^ (2 * s) * algebraMap Qb ℂ x / ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ * ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i)`. Rewrite using `[hxe, hDg]`. Clear the denominators using the available nonvanishing facts. Establish `hB : ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i = (∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i) * (Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) ^ (∑ i, κ i)`.

Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [← mul_pow]; ring`. Establish `key : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = algebraMap Qb ℂ x * (T.C / Ω₀ ^ Fintype.card I) ^ (2 * s) * ((-1) ^ (∑ i, κ i) * ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i)⁻¹`. Establish `hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) * (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i)`. Rewrite using `[cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hS0` using `[risingFactor_eq]`. Rewrite using `[GlobalTheory.ToricTransport.coordIn, hB]`. Conclude with `alg_id _ _ _ _ _ _ _ _ _ _ _ (Fintype.card I) (2 * s) (∑ i, κ i) hS0 hC0 hΩ0 (mul_ne_zero two_ne_zero hpi) hsd hW hcW hP (pow_ne_zero _ (by norm_num))`.

Rewrite using `[key, ← mem_algebraicClosure_iff]`. Establish `mem : ∀ w : ℂ, IsAlgebraic ℚ w → w ∈ algebraicClosure ℚ ℂ` using `fun w h => mem_algebraicClosure_iff.2 h`. Use `mul_mem (mul_mem x.2 (pow_mem (mem _ hCalg) _)) (inv_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (prod_mem fun i _ => pow_mem (mul_mem (intCast_mem _ _) (mem _ (hA i).2)) _)))` and prove the remaining obligations.
-/
theorem latAlg : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → EisRule → JetCore → ModelAlg → LatAlg := by
  intro hZ hSt hEis hJet hMod
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  obtain ⟨⟨z, hz⟩, -⟩ := hZ E s hs
  obtain ⟨𝔠, X₀, δ₀, N, T, hAdm, hOver, hCalg, hA⟩ :=
    hMod K d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hCM hφι (condQ 𝔣 Q) y hc0
  let R₀ : Subring ℂ := (algebraicClosure ℚ ℂ).toSubring
  obtain ⟨r, hr⟩ := hEis E hf2 𝔠 s hs z hz R₀ 1 (one_mem _) (fun C => by
    show _ ∈ algebraicClosure ℚ ℂ
    exact mul_mem (one_mem _) (SubfieldClass.ratCast_mem _ _))
  obtain ⟨ε, hε⟩ := hJet
  let ι₀ : R₀ →+* Qb :=
    { toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  letI : Algebra R₀ Qb := ι₀.toAlgebra
  obtain ⟨x, hx⟩ := hε E I 𝔠 hf2 R₀ s r hs Qb X₀ δ₀ N hAdm κ
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hxe := hx (algebraMap Qb ℂ) (fun a => rfl) φ (condQ 𝔣 Q) y 1 hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu
  have hcard := card_eq_finrank hCM
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hε0 : ((ε : ℤ) : ℂ) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hW : ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero hε0 (hA i).1)
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hrF : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ ≠ 0 := by
    rw [risingFactor_eq]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hP
  have hS0 : S 0 = T.C ^ (2 * s) * algebraMap Qb ℂ x /
      ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ *
        ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i) := by
    rw [hxe, hDg]
    field_simp
  have hB : ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i =
      (∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i) * (Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) ^ (∑ i, κ i) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← mul_pow]; ring
  have key : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) =
      algebraMap Qb ℂ x * (T.C / Ω₀ ^ Fintype.card I) ^ (2 * s) *
        ((-1) ^ (∑ i, κ i) * ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i)⁻¹ := by
    have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
        (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) := by
      rw [cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
    rw [risingFactor_eq] at hS0
    rw [GlobalTheory.ToricTransport.coordIn, hB]
    exact alg_id _ _ _ _ _ _ _ _ _ _ _ (Fintype.card I) (2 * s) (∑ i, κ i) hS0 hC0 hΩ0
      (mul_ne_zero two_ne_zero hpi) hsd hW hcW hP (pow_ne_zero _ (by norm_num))
  rw [key, ← mem_algebraicClosure_iff]
  have mem : ∀ w : ℂ, IsAlgebraic ℚ w → w ∈ algebraicClosure ℚ ℂ := fun w h => mem_algebraicClosure_iff.2 h
  refine mul_mem (mul_mem x.2 (pow_mem (mem _ hCalg) _)) (inv_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
    (prod_mem fun i _ => pow_mem (mul_mem (intCast_mem _ _) (mem _ (hA i).2)) _)))

end GlobalTheory.LatAlgebraic
