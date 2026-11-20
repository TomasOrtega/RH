import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Local

variable {E K : Type} [Field E] [NumberField E] [Field K]

/- English proof (translation)
Establish `hq` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`. Establish `e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E)` using `by rw [map_natCast]`. Establish `h1 : redP P (qOf P : E) = 0`. Rewrite using `[e, reduction_coe, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.absNorm_mem _`.

Establish `h2 : a = (qOf P : E) * (a / (qOf P : E))` using `by field_simp`. Rewrite using `[h2, reduction_mul (e ▸ IntAt.coe P _) h, h1, zero_mul]`.
-/
theorem reduction_eq_zero_of_integral_div_absNorm {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P (a / (qOf P : E))) : redP P a = 0 := by
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : redP P (qOf P : E) = 0 := by
    rw [e, reduction_coe, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have h2 : a = (qOf P : E) * (a / (qOf P : E)) := by field_simp
  rw [h2, reduction_mul (e ▸ IntAt.coe P _) h, h1, zero_mul]

/- English proof (translation)
Establish `hq` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`. Take `⟨k, u, hu, e⟩` from `GlobalTheory.Proof.IntegralPowerExpansion.exists_int_add_q_pow_mul hP D (hxi.mul ha)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `hu using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e`.
-/
theorem exists_int_sub_div {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (D : ℕ) {xi a : E} (hxi : IntAt P xi)
    (ha : IntAt P ((qOf P : E) ^ D * a)) : ∃ b : ℤ, IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) := by
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  obtain ⟨k, u, hu, e⟩ := GlobalTheory.Proof.IntegralPowerExpansion.exists_int_add_q_pow_mul hP D (hxi.mul ha)
  refine ⟨k, ?_⟩
  convert hu using 1
  field_simp
  linear_combination e

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Take `⟨i, -, hi⟩` from `(hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one (Complex.isPrimitiveRoot_exp n hn).pow_eq_one`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem exists_root_exp (σ : K →+* ℂ) {n : ℕ} (hn : n ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ω : K, σ ω = Complex.exp (2 * Real.pi * Complex.I / n) := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
Establish `hq` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`. Establish `hn : qOf P ^ D ≠ 0` using `pow_ne_zero _ hP.1.ne_zero`. Establish `hprim : IsPrimitiveRoot ω (qOf P ^ D)` using `IsPrimitiveRoot.of_map_of_injective (f := σ) (hω ▸ Complex.isPrimitiveRoot_exp _ hn) σ.injective`. Establish `hω0 : ω ≠ 0` using `hprim.ne_zero hn`. Set `ψ : E → K` to `fun a => if h : ∃ b : ℤ, IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) then ω ^ h.choose else 1`.

Establish `key : ∀ (a : E) (b : ℤ), IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) → ψ a = ω ^ b`. Introduce `a b hb`. Establish `hex : ∃ b : ℤ, IntAt P (xi * a - (b : E) / (qOf P : E) ^ D)` using `⟨b, hb⟩`. Establish `h1` using `hex.choose_spec`. Simplify using `only [ψ, dif_pos hex]`.

Generalize the expression as in `hex.choose = c at h1`. Establish `h2 : IntAt P (((qOf P : E) ^ D)⁻¹ * ((c - b : ℤ) : E))`. Use `hb.add (GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h1) using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.q_pow_dvd_of_intAt hP D h2`. Establish `h4 : ω ^ (c - b) = 1` using `(hprim.zpow_eq_one_iff_dvd _).2 (by exact_mod_cast h3)`. Rewrite `h4` using `[zpow_sub₀ hω0, div_eq_one_iff_eq (zpow_ne_zero _ hω0)]`. Conclude with `h4`.

Use `⟨ψ, fun x y hx hy => ?_, fun x hx => ?_, fun h => ?_, fun a b hb => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `exists_int_sub_div hP D hxi hx`. Take `⟨c, hc⟩` from `exists_int_sub_div hP D hxi hy`. Rewrite using `[key x b hb, key y c hc, key (x + y) (b + c) (by`. Use `hb.add hc using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Use the proof step `ring), zpow_add₀ hω0]`. Rewrite using `[key x 0 (by simpa using hxi.mul hx), zpow_zero]`. Take `⟨D', rfl⟩ : ∃ D', D = D' + 1` from `⟨D - 1, by omega⟩`. Establish `h1 : IntAt P ((qOf P : E) ^ (D' + 1) * (qOf P : E)⁻¹)`.

Use `GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P ((qOf P : ℤ) ^ D') using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb⟩` from `exists_int_sub_div hP _ hxi h1`.

Rewrite `h` using `[key _ b hb, hprim.zpow_eq_one_iff_dvd]`. Take `⟨c, rfl⟩` from `h`. Apply `hxi'` to reduce the goal to its premises. Apply `reduction_eq_zero_of_integral_div_absNorm` to reduce the goal to its premises. Use `hb.add (GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P c) using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key a b hb, map_zpow₀, hω, ← Complex.exp_int_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_psi (σ : K →+* ℂ) {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {D : ℕ} (hD : 1 ≤ D) {xi : E}
    (hxi : IntAt P xi) (hxi' : redP P xi ≠ 0) {ω : K}
    (hω : σ ω = Complex.exp (2 * Real.pi * Complex.I / ((qOf P ^ D : ℕ) : ℂ))) :
    ∃ ψ : E → K,
      (∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → ψ (x + y) = ψ x * ψ y) ∧
      (∀ x : E, IntAt P x → ψ x = 1) ∧ ψ ((qOf P : E)⁻¹) ≠ 1 ∧
      ∀ (a : E) (b : ℤ), IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) →
        σ (ψ a) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P : ℂ) ^ D) := by
  classical
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hn : qOf P ^ D ≠ 0 := pow_ne_zero _ hP.1.ne_zero
  have hprim : IsPrimitiveRoot ω (qOf P ^ D) :=
    IsPrimitiveRoot.of_map_of_injective (f := σ) (hω ▸ Complex.isPrimitiveRoot_exp _ hn) σ.injective
  have hω0 : ω ≠ 0 := hprim.ne_zero hn
  let ψ : E → K := fun a => if h : ∃ b : ℤ, IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) then ω ^ h.choose else 1
  have key : ∀ (a : E) (b : ℤ), IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) → ψ a = ω ^ b := by
    intro a b hb
    have hex : ∃ b : ℤ, IntAt P (xi * a - (b : E) / (qOf P : E) ^ D) := ⟨b, hb⟩
    have h1 := hex.choose_spec
    simp only [ψ, dif_pos hex]
    generalize hex.choose = c at h1
    have h2 : IntAt P (((qOf P : E) ^ D)⁻¹ * ((c - b : ℤ) : E)) := by
      convert hb.add (GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h1) using 1
      push_cast
      field_simp
      ring
    have h3 := GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.q_pow_dvd_of_intAt hP D h2
    have h4 : ω ^ (c - b) = 1 := (hprim.zpow_eq_one_iff_dvd _).2 (by exact_mod_cast h3)
    rw [zpow_sub₀ hω0, div_eq_one_iff_eq (zpow_ne_zero _ hω0)] at h4
    exact h4
  refine ⟨ψ, fun x y hx hy => ?_, fun x hx => ?_, fun h => ?_, fun a b hb => ?_⟩
  · obtain ⟨b, hb⟩ := exists_int_sub_div hP D hxi hx
    obtain ⟨c, hc⟩ := exists_int_sub_div hP D hxi hy
    rw [key x b hb, key y c hc, key (x + y) (b + c) (by
      convert hb.add hc using 1
      push_cast
      ring), zpow_add₀ hω0]
  · rw [key x 0 (by simpa using hxi.mul hx), zpow_zero]
  · obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    have h1 : IntAt P ((qOf P : E) ^ (D' + 1) * (qOf P : E)⁻¹) := by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P ((qOf P : ℤ) ^ D') using 1
      push_cast
      field_simp
      ring
    obtain ⟨b, hb⟩ := exists_int_sub_div hP _ hxi h1
    rw [key _ b hb, hprim.zpow_eq_one_iff_dvd] at h
    obtain ⟨c, rfl⟩ := h
    apply hxi'
    apply reduction_eq_zero_of_integral_div_absNorm
    convert hb.add (GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P c) using 1
    push_cast
    field_simp
    ring
  · rw [key a b hb, map_zpow₀, hω, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring

end Local

section Global

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by`. Unfold `Primes.vGs at hP`. Break down `Finset.mem_union.1 hP with h | h` into its components or cases. Use `exacts [⟨0, h⟩, ⟨1, h⟩]`. Establish `h1 : qOf P = Pr.g i` using `hPr.vG_norm i P hi`.

Unfold `DegOneUnram`. Rewrite using `[h1]`. Conclude with `⟨hPr.g_prime i, (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2⟩`.
-/
theorem degOneUnram_of_mem_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) : DegOneUnram P := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    unfold Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have h1 : qOf P = Pr.g i := hPr.vG_norm i P hi
  unfold DegOneUnram
  rw [h1]
  exact ⟨hPr.g_prime i, (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2⟩

/- English proof (translation)
Unfold `QE at hP`. Use `split_ifs at hP with h`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hP`. Rewrite `hv` using `[Set.Finite.mem_toFinset]`. Establish `hg : GoodPl X.E S v` using `by_contra fun hg => hv (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hg)`.

Conclude with `GlobalTheory.Proof.NormalFormAtPrime.degOne_of_split hX.rankE hg.1 hg.2.1 (hsel v)`. Simplify using `at hP`.
-/
theorem degOneUnram_of_mem_QE (hX : X.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel)
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    DegOneUnram P := by
  classical
  unfold QE at hP
  split_ifs at hP with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    rw [Set.Finite.mem_toFinset] at hv
    have hg : GoodPl X.E S v := by_contra fun hg => hv
      (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hg)
    exact GlobalTheory.Proof.NormalFormAtPrime.degOne_of_split hX.rankE hg.1 hg.2.1 (hsel v)
  · simp at hP

/- English proof (translation)
Break down `Finset.mem_union.1 P.2 with h | h` into its components or cases. Use `exacts [degOneUnram_of_mem_vGs hX hPr h, degOneUnram_of_mem_QE hX hsel mu h]`.
-/
theorem degOneUnram_rowSG (hX : X.Ok) (hPr : Pr.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : IsSel X sel) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : rowSG Pr sel mu) : DegOneUnram P.1 := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  exacts [degOneUnram_of_mem_vGs hX hPr h, degOneUnram_of_mem_QE hX hsel mu h]

/- English proof (translation)
Establish `hm` using `hT.mu0 j`. Establish `hg : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (hPr.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (hPr.g_prime 1).ne_zero)`. Establish `hoff : ∀ v : HeightOneSpectrum (𝓞 X.E), v ∉ divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E)) → ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal`. Introduce `v hv i hi`. Apply `hv` to reduce the goal to its premises.

Rewrite using `[Formalism.L2.Col.mem_divs hg]`. Use `fin_cases i`. Conclude with `v.asIdeal.mul_mem_right _ hi`. Conclude with `v.asIdeal.mul_mem_left _ hi`. Use `GlobalTheory.TameVal.locK_mem (m0 j) (GlobalTheory.TameVal.unitsIn σ₀.fieldRange) _ hm.tame (fun v hv => hm.unr v (hoff v hv)) (fun v hv => ⟨_, hT.muVal j v (hoff v hv)⟩) (fun k => ?_) P x` and prove the remaining obligations.

Take `⟨n, hn, hinf⟩` from `hm.inf`. Express the relevant statement in the definitionally equal form `(((m0 j).inf k : ℂˣ) : ℂ) ∈ σ₀.fieldRange`. Rewrite using `[hinf k]`. Use `prod_mem fun τ _ => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `he j τ`.

Establish `hn2 : n τ = 2 * (-z)`. Use `hn τ` as an intermediate fact. Simplify using `only [hz] at this`. Conclude with `this` after adjusting the coercions. Rewrite using `[hn2, zpow_mul, GlobalTheory.TameVal.sq_div_norm ((map_ne_zero _).2 k.ne_zero), ← hX.conjE]`.

Conclude with `zpow_mem (σ₀.fieldRange.div_mem ⟨_, rfl⟩ ⟨_, rfl⟩) _`.
-/
theorem locK_mem_of_tied (hX : X.Ok) (hPr : Pr.Ok) {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : Fin m → X.Tau → ℚ}
    {m0 : Fin m → Formalism.L2.Host.HChar X.E} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied σ₀ e m0 eta)
    (he : ∀ j τ, ∃ z : ℤ, e j τ = z) (j : Fin m) (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ) :
    ∃ k : X.K, σ₀ k = (((m0 j).locK P x : ℂˣ) : ℂ) := by
  have hm := hT.mu0 j
  have hg : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (hPr.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (hPr.g_prime 1).ne_zero)
  have hoff : ∀ v : HeightOneSpectrum (𝓞 X.E),
      v ∉ divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E)) → ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal := by
    intro v hv i hi
    apply hv
    rw [Formalism.L2.Col.mem_divs hg]
    fin_cases i
    · exact v.asIdeal.mul_mem_right _ hi
    · exact v.asIdeal.mul_mem_left _ hi
  refine GlobalTheory.TameVal.locK_mem (m0 j) (GlobalTheory.TameVal.unitsIn σ₀.fieldRange) _ hm.tame (fun v hv => hm.unr v (hoff v hv))
    (fun v hv => ⟨_, hT.muVal j v (hoff v hv)⟩) (fun k => ?_) P x
  obtain ⟨n, hn, hinf⟩ := hm.inf
  change (((m0 j).inf k : ℂˣ) : ℂ) ∈ σ₀.fieldRange
  rw [hinf k]
  refine prod_mem fun τ _ => ?_
  obtain ⟨z, hz⟩ := he j τ
  have hn2 : n τ = 2 * (-z) := by
    have := hn τ
    simp only [hz] at this
    exact_mod_cast this
  rw [hn2, zpow_mul, GlobalTheory.TameVal.sq_div_norm ((map_ne_zero _).2 k.ne_zero), ← hX.conjE]
  exact zpow_mem (σ₀.fieldRange.div_mem ⟨_, rfl⟩ ⟨_, rfl⟩) _

/- English proof (translation)
Use `w.1.isMaximal` as an intermediate fact. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (redP w.1 xi0)`. Take `⟨c, hc⟩` from `Ideal.Quotient.exists_inv (hy ▸ hxi : Ideal.Quotient.mk w.1.asIdeal y ≠ 0)`. Use `⟨Ch.psi0 w c, ?_⟩` and prove the remaining obligations. Rewrite using `[hW w c 1 (by rw [← hy, hc, Int.cast_one])]`.

Simplify using the standard rewrite rules.
-/
theorem exists_root_vGs {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {xi0 : X.E} (hW : Ch.WeilTied σ₀ xi0)
    (w : {w // w ∈ Pr.vGs}) (hxi : redP w.1 xi0 ≠ 0) :
    ∃ ω : X.K, σ₀ ω = Complex.exp (2 * Real.pi * Complex.I / ((qOf w.1 ^ 1 : ℕ) : ℂ)) := by
  have := w.1.isMaximal
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (redP w.1 xi0)
  obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (hy ▸ hxi : Ideal.Quotient.mk w.1.asIdeal y ≠ 0)
  refine ⟨Ch.psi0 w c, ?_⟩
  rw [hW w c 1 (by rw [← hy, hc, Int.cast_one])]
  simp

open Classical in

/- English proof (translation)
Set `D : rowSG Pr sel mu → ℕ` to `fun P => if P.1 ∈ Pr.vGs then 1 else Dq`. Establish `hD1 : ∀ P, 1 ≤ D P` using `fun P => by`. Simplify using `only [D]`. Use `split_ifs`. Use `exacts [le_rfl, hD]`.

Establish `hω : ∀ P : rowSG Pr sel mu, ∃ ω : X.K, G.σ₀ ω = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ D P : ℕ) : ℂ))` using `fun P => by`. Simplify using `only [D]`. Use `split_ifs with h`. Conclude with `exists_root_vGs hW ⟨P.1, h⟩ (hxi P).2`. Take `⟨ζ, hζ⟩` from `hroot P h`.

Conclude with `exists_root_exp G.σ₀ (pow_ne_zero _ (hdeg P).1.ne_zero) hζ`. Use `choose ω hω using hω`. Use `choose ψ hadd hint hne htie using fun P : rowSG Pr sel mu => exists_psi G.σ₀ (hdeg P) (hD1 P) (hxi P).1 (hxi P).2 (hω P)`. Use `choose sq hsq using hsq`. Establish `hq : ∀ P : HeightOneSpectrum (𝓞 X.E), (qOf P : X.E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero`.

Use `choose k hk using fun (j : Fin R.m) (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ Pr.vGs) => hval j P h (Units.mk0 _ (hq P)) rfl`. Use `⟨⟨ψ, D, sq, fun j P => if h : j - 1 < R.m then (if hP : P.1 ∈ Pr.vGs then (k ⟨j - 1, h⟩ P.1 hP)⁻¹ * (((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K) else (((Ch.muVal ⟨j - 1, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) else 1, A, B, M, sharp⟩, ⟨hadd, hint …` and prove the remaining obligations. Establish `hi' : i + 1 - 1 < R.m` using `hi`. Simplify using `only [dif_pos hi', dif_neg hP]`. Both sides reduce to the same expression.

Take `rfl : qu = Units.mk0 _ (hq P.1)` from `Units.ext hqu`. Establish `hi' : i + 1 - 1 < R.m` using `hi`. Simplify using `only [dif_pos hi', dif_pos hP]`. Rewrite using `[map_mul, map_inv₀, hk]`. Both sides reduce to the same expression.

Establish `hDP : D P = 1` using `if_pos hP`. Establish `h1 : IntAt P.1 ((qOf P.1 : X.E) ^ D P * (a / (qOf P.1 : X.E)))`. Rewrite using `[hDP, pow_one, mul_div_cancel₀ _ (hq P.1)]`. Conclude with `ha`. Take `⟨b, hb⟩` from `exists_int_sub_div (hdeg P) _ (hxi P).1 h1`.

Establish `h2` using `htie P _ b hb`. Rewrite `hb`, `h2` using `[hDP, pow_one]`. Establish `h3 : redP P.1 (G.xi0 * a + ((-b : ℤ) : X.E)) = 0`. Apply `reduction_eq_zero_of_integral_div_absNorm` to reduce the goal to its premises. Use `hb using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : redP P.1 ((-b : ℤ) : X.E) = ((-b : ℤ) : 𝓞 X.E ⧸ P.1.asIdeal)`. Use `reduction_coe P.1 ((-b : ℤ) : 𝓞 X.E)` as an intermediate fact. Rewrite `this` using `[map_intCast, map_intCast]`. Then use the resulting hypothesis.

Rewrite `h3` using `[reduction_add ((hxi P).1.mul ha) (GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int _ _), reduction_mul (hxi P).1 ha, h4, Int.cast_neg, add_neg_eq_zero]`. Apply `G.σ₀.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `G.σ₀ (ψ P _) = _`. Rewrite using `[h2, psi0P, dif_pos hP]`. Conclude with `(hW ⟨P.1, hP⟩ _ b h3).symm`.
-/
theorem exists_locCst_of_values (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (G : ChGlob X R.m) (hdeg : ∀ P : rowSG Pr sel mu, DegOneUnram P.1)
    (hW : Ch.WeilTied G.σ₀ G.xi0) (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0)
    (hval : ∀ (j : Fin R.m), ∀ P ∈ Pr.vGs, ∀ qu : X.Eˣ, (qu : X.E) = (qOf P : X.E) →
      ∃ k : X.K, G.σ₀ k = (((G.mu0 j).locK P qu : ℂˣ) : ℂ))
    (M A B Dq : ℕ) (hM : 1 ≤ M) (hA : M ≤ A) (hB : M ≤ B) (hD : 1 ≤ Dq) (sharp : Bool)
    (hsq : ∀ P : rowSG Pr sel mu, ∃ s : X.K, s ^ 2 = (qOf P.1 : X.K))
    (hroot : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ ζ : X.K, IsPrimitiveRoot ζ (qOf P.1 ^ Dq)) :
    ∃ cst : LocCst X (rowSG Pr sel mu), cst.Ok ∧ cst.WeilTied G.σ₀ G.xi0 ∧ cst.sharp = sharp ∧
      cst.M = M ∧ cst.A = A ∧ cst.B = B ∧
      (∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
        cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) ∧
      (∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
        G.σ₀ (cst.muq (i + 1) P) =
          (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K)) ∧
      (∀ (P : rowSG Pr sel mu) (a : X.E), P.1 ∈ Pr.vGs → IntAt P.1 a →
        cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → cst.D P = 1) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.D P = Dq) := by
  let D : rowSG Pr sel mu → ℕ := fun P => if P.1 ∈ Pr.vGs then 1 else Dq
  have hD1 : ∀ P, 1 ≤ D P := fun P => by
    simp only [D]
    split_ifs
    exacts [le_rfl, hD]
  have hω : ∀ P : rowSG Pr sel mu, ∃ ω : X.K,
      G.σ₀ ω = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ D P : ℕ) : ℂ)) := fun P => by
    simp only [D]
    split_ifs with h
    · exact exists_root_vGs hW ⟨P.1, h⟩ (hxi P).2
    · obtain ⟨ζ, hζ⟩ := hroot P h
      exact exists_root_exp G.σ₀ (pow_ne_zero _ (hdeg P).1.ne_zero) hζ
  choose ω hω using hω
  choose ψ hadd hint hne htie using fun P : rowSG Pr sel mu =>
    exists_psi G.σ₀ (hdeg P) (hD1 P) (hxi P).1 (hxi P).2 (hω P)
  choose sq hsq using hsq
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), (qOf P : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero
  choose k hk using fun (j : Fin R.m) (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ Pr.vGs) =>
    hval j P h (Units.mk0 _ (hq P)) rfl
  refine ⟨⟨ψ, D, sq, fun j P => if h : j - 1 < R.m then
      (if hP : P.1 ∈ Pr.vGs then (k ⟨j - 1, h⟩ P.1 hP)⁻¹ * (((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)
      else (((Ch.muVal ⟨j - 1, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) else 1, A, B, M, sharp⟩,
    ⟨hadd, hint, hne, hD1, hsq, hM, hA, hB, hM.trans hB⟩, fun P a b _ hb => htie P a b hb, rfl, rfl, rfl, rfl,
    fun i hi P hP => ?_, fun i hi P hP qu hqu => ?_, fun P a hP ha => ?_, fun P hP => if_pos hP, fun P hP => if_neg hP⟩
  · have hi' : i + 1 - 1 < R.m := hi
    simp only [dif_pos hi', dif_neg hP]
    rfl
  · obtain rfl : qu = Units.mk0 _ (hq P.1) := Units.ext hqu
    have hi' : i + 1 - 1 < R.m := hi
    simp only [dif_pos hi', dif_pos hP]
    rw [map_mul, map_inv₀, hk]
    rfl
  · have hDP : D P = 1 := if_pos hP
    have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ D P * (a / (qOf P.1 : X.E))) := by
      rw [hDP, pow_one, mul_div_cancel₀ _ (hq P.1)]
      exact ha
    obtain ⟨b, hb⟩ := exists_int_sub_div (hdeg P) _ (hxi P).1 h1
    have h2 := htie P _ b hb
    rw [hDP, pow_one] at hb h2
    have h3 : redP P.1 (G.xi0 * a + ((-b : ℤ) : X.E)) = 0 := by
      apply reduction_eq_zero_of_integral_div_absNorm
      convert hb using 1
      push_cast
      ring
    have h4 : redP P.1 ((-b : ℤ) : X.E) = ((-b : ℤ) : 𝓞 X.E ⧸ P.1.asIdeal) := by
      have := reduction_coe P.1 ((-b : ℤ) : 𝓞 X.E)
      rwa [map_intCast, map_intCast] at this
    rw [reduction_add ((hxi P).1.mul ha) (GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int _ _), reduction_mul (hxi P).1 ha, h4, Int.cast_neg,
      add_neg_eq_zero] at h3
    apply G.σ₀.injective
    change G.σ₀ (ψ P _) = _
    rw [h2, psi0P, dif_pos hP]
    exact (hW ⟨P.1, hP⟩ _ b h3).symm

/- English proof (translation)
Take `⟨cst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩` from `exists_locCst_of_values Ch sel mu G (degOneUnram_rowSG hX hPr hsel mu) hW hxi (fun j P _ qu _ => locK_mem_of_tied hX hPr hT he j P qu) M A B Dq hM hA hB (by omega) true hsq hroot`. Conclude with `⟨cst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun P hP => by rw [h4, h11 P hP]; exact hD, fun P hP => by rw [h11 P hP]; exact hD', h11⟩`.
-/
theorem exists_locCst (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (hsel : IsSel X sel) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (G : ChGlob X R.m) (e : Fin R.m → X.Tau → ℚ) (he : ∀ j τ, ∃ z : ℤ, e j τ = z)
    (eta : Formalism.L2.Host.HChar X.E) (hT : Ch.Tied G.σ₀ e G.mu0 eta)
    (hW : Ch.WeilTied G.σ₀ G.xi0) (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0)
    (M A B Dq : ℕ) (hM : 1 ≤ M) (hA : M ≤ A) (hB : M ≤ B) (hD : 2 * M ≤ Dq) (hD' : 2 * (R.m - 1) + 1 ≤ Dq)
    (hsq : ∀ P : rowSG Pr sel mu, ∃ s : X.K, s ^ 2 = (qOf P.1 : X.K))
    (hroot : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ ζ : X.K, IsPrimitiveRoot ζ (qOf P.1 ^ Dq)) :
    ∃ cst : LocCst X (rowSG Pr sel mu), cst.Ok ∧ cst.WeilTied G.σ₀ G.xi0 ∧ cst.sharp = true ∧
      cst.M = M ∧ cst.A = A ∧ cst.B = B ∧
      (∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
        cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) ∧
      (∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
        G.σ₀ (cst.muq (i + 1) P) =
          (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K)) ∧
      (∀ (P : rowSG Pr sel mu) (a : X.E), P.1 ∈ Pr.vGs → IntAt P.1 a →
        cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → cst.D P = 1) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) ∧
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.D P = Dq) := by
  obtain ⟨cst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := exists_locCst_of_values Ch sel mu G
    (degOneUnram_rowSG hX hPr hsel mu) hW hxi (fun j P _ qu _ => locK_mem_of_tied hX hPr hT he j P qu) M A B Dq hM hA hB
    (by omega) true hsq hroot
  exact ⟨cst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun P hP => by rw [h4, h11 P hP]; exact hD,
    fun P hP => by rw [h11 P hP]; exact hD', h11⟩

/- English proof (translation)
The claim follows from `(hT.mu0 j).atg w x y c hx hc`.
-/
theorem tameHeckeCharLocal_eq_inv_typeCharacter {Ch : Chars X Pr R.m} {G : ChGlob X R.m} {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E}
    (hT : Ch.Tied G.σ₀ e G.mu0 eta) (j : Fin R.m) (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ)
    (hx : (x : X.E) = (y : X.E)) (hc : (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y) :
    (((G.mu0 j).locK w.1 x : ℂˣ) : ℂ) = G.σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K) := (hT.mu0 j).atg w x y c hx hc

end Global

end GlobalTheory.Mem.Col2

end
