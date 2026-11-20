import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongJac
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongPrin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hA0 : A ≠ 0`. Introduce `h`. Rewrite `hA` using `[h, map_zero]`. Conclude with `zero_ne_one hA`. Establish `hx0 : x ≠ 0`.

Introduce `h`. Rewrite `hx` using `[h, map_zero]`. Conclude with `zero_ne_one hx`. Establish `hζ0 : ζ ≠ 0`. Introduce `h`.

Rewrite `hζ` using `[h, map_zero]`. Conclude with `zero_ne_one hζ`. Establish `hB : w B = 1`. Establish `e : B = (B - A) + A` using `by ring`. Rewrite using `[e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hA]), hA]`.

Establish `hAx : w (A / x) = 1` using `by rw [map_div₀, hA, hx, div_one]`. Establish `hz : w z = 1`. Establish `h3 : w (ζ * (B / z)) = 1`. Establish `e : ζ * (B / z) = (ζ * (B / z) - A / x) + A / x` using `by ring`. Rewrite using `[e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hAx]), hAx]`.

Rewrite `h3` using `[map_mul, map_div₀, hζ, hB, one_mul, one_div]`. Conclude with `inv_eq_one.mp h3`. Establish `hz0 : z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, map_zero]`.

Conclude with `zero_ne_one hz`. Establish `e : x - ζ⁻¹ * z = x * (A - B) / A - (A / x - ζ * (B / z)) * (x * z * ζ⁻¹ / A)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `lt_of_le_of_lt (w.map_sub _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_div₀, map_mul, hx, hA, one_mul, div_one]`. Conclude with `h1`. Rewrite using `[map_mul, map_div₀, map_mul, map_mul, map_inv₀, hx, hz, hζ, hA]`. Simplify using `using h2`.
-/
private theorem alg_step {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (A B x z ζ : L)
    (hA : w A = 1) (hx : w x = 1) (hζ : w ζ = 1) (h1 : w (A - B) < 1) (h2 : w (A / x - ζ * (B / z)) < 1) :
    w (x - ζ⁻¹ * z) < 1 := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hA
    exact zero_ne_one hA
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact zero_ne_one hζ
  have hB : w B = 1 := by
    have e : B = (B - A) + A := by ring
    rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hA]), hA]
  have hAx : w (A / x) = 1 := by rw [map_div₀, hA, hx, div_one]
  have hz : w z = 1 := by
    have h3 : w (ζ * (B / z)) = 1 := by
      have e : ζ * (B / z) = (ζ * (B / z) - A / x) + A / x := by ring
      rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hAx]), hAx]
    rw [map_mul, map_div₀, hζ, hB, one_mul, one_div] at h3
    exact inv_eq_one.mp h3
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have e : x - ζ⁻¹ * z = x * (A - B) / A - (A / x - ζ * (B / z)) * (x * z * ζ⁻¹ / A) := by
    field_simp
    ring
  rw [e]
  refine lt_of_le_of_lt (w.map_sub _ _) (max_lt ?_ ?_)
  · rw [map_div₀, map_mul, hx, hA, one_mul, div_one]
    exact h1
  · rw [map_mul, map_div₀, map_mul, map_mul, map_inv₀, hx, hz, hζ, hA]
    simpa using h2

/- English proof (translation)
Use `haveI := v.isPrime`. Take `⟨a, ha, c, hc', hac⟩` from `Ideal.isCoprime_iff_exists.mp hc`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hc'`. Establish `hne : ∀ t, conjI N K 𝔞 t ≠ ⊥`. Introduce `t hb`.

Take `⟨e, he, he0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Establish `hm : (sgO N K t).symm e ∈ conjI N K 𝔞 t`. Rewrite using `[mem_conjI, RingEquiv.apply_symm_apply]`. Conclude with `he`. Rewrite `hm` using `[hb, Ideal.mem_bot]`.

Conclude with `he0 (by simpa using hm)`. Establish `hnle : ∀ t, ¬ conjI N K 𝔞 t ≤ v.asIdeal`. Introduce `t ht'`. Establish `ha' : (sgO N K t).symm a ∈ v.asIdeal`. Apply `ht'` to reduce the goal to its premises.

Rewrite using `[mem_conjI, RingEquiv.apply_symm_apply]`. Conclude with `ha`. Establish `hc'' : (sgO N K t).symm (r * (q : 𝓞 K)) ∈ v.asIdeal`. Rewrite using `[map_mul, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ hv`.

Establish `h1 : (1 : 𝓞 K) ∈ v.asIdeal`. Establish `e : (1 : 𝓞 K) = (sgO N K t).symm a + (sgO N K t).symm (r * (q : 𝓞 K))`. Rewrite using `[← map_add, hac, map_one]`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ ha' hc''`.

Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Establish `hcount : ∀ t, FractionalIdeal.count K v ((conjI N K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0`. Introduce `t`. Rewrite using `[FractionalIdeal.count_coe K v (hne t), Nat.cast_eq_zero]`. Assume the negation of the conclusion as `hc0`.

Establish `hdvd` using `(Associates.count_ne_zero_iff_dvd (hne t) v.irreducible).mp hc0`. Conclude with `hnle t (Ideal.le_of_dvd hdvd)`. Establish `hX0 : X ≠ 0`. Introduce `h`. Establish `h1` using `hX.1`.

Rewrite `h1` using `[h, zero_mul]`. Conclude with `zero_ne_one h1`. Establish `hcs` using `GroundTheory.Global.count_spanSingleton v hX0`. Rewrite `hcs` using `[hX.2, FractionalIdeal.count_prod K v _ _ (fun t _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne t))), Finset.sum_eq_zero (fun t _ => by rw [FractionalIdeal.count_zpow, hcount t, mul_zero])]`. Establish `hv0 : v.valuation K X ≠ 0` using `(Valuation.ne_zero_iff _).mpr hX0`.

Establish `hl : WithZero.log (v.valuation K X) = 0` using `by linarith`. Rewrite using `[← WithZero.exp_log hv0, hl, WithZero.exp_zero]`.
-/
private theorem isX_unit (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]
    (b q : ℕ) (𝔞 : Ideal (𝓞 K)) (X : K) (h0 : 𝔞 ≠ ⊥) (hc : IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K)})) (hX : IsX N K b 𝔞 X)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (q : 𝓞 K) ∈ v.asIdeal) : v.valuation K X = 1 := by
  haveI := v.isPrime
  obtain ⟨a, ha, c, hc', hac⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hc'
  have hne : ∀ t, conjI N K 𝔞 t ≠ ⊥ := by
    intro t hb
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hm : (sgO N K t).symm e ∈ conjI N K 𝔞 t := by
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact he
    rw [hb, Ideal.mem_bot] at hm
    exact he0 (by simpa using hm)
  have hnle : ∀ t, ¬ conjI N K 𝔞 t ≤ v.asIdeal := by
    intro t ht'
    have ha' : (sgO N K t).symm a ∈ v.asIdeal := by
      apply ht'
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact ha
    have hc'' : (sgO N K t).symm (r * (q : 𝓞 K)) ∈ v.asIdeal := by
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ hv
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have e : (1 : 𝓞 K) = (sgO N K t).symm a + (sgO N K t).symm (r * (q : 𝓞 K)) := by
        rw [← map_add, hac, map_one]
      rw [e]
      exact Ideal.add_mem _ ha' hc''
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hcount : ∀ t, FractionalIdeal.count K v ((conjI N K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro t
    rw [FractionalIdeal.count_coe K v (hne t), Nat.cast_eq_zero]
    by_contra hc0
    have hdvd := (Associates.count_ne_zero_iff_dvd (hne t) v.irreducible).mp hc0
    exact hnle t (Ideal.le_of_dvd hdvd)
  have hX0 : X ≠ 0 := by
    intro h
    have h1 := hX.1
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hcs := GroundTheory.Global.count_spanSingleton v hX0
  rw [hX.2, FractionalIdeal.count_prod K v _ _
    (fun t _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne t))),
    Finset.sum_eq_zero (fun t _ => by rw [FractionalIdeal.count_zpow, hcount t, mul_zero])] at hcs
  have hv0 : v.valuation K X ≠ 0 := (Valuation.ne_zero_iff _).mpr hX0
  have hl : WithZero.log (v.valuation K X) = 0 := by linarith
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

/- English proof (translation)
Introduce `M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hbM hbq 𝔞 X' X hc hX' hX`. Establish `key : ∀ I : Ideal (𝓞 K'), IsCoprime I (Ideal.span {(q : 𝓞 K')}) → ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → ¬ I ≤ v.asIdeal`. Introduce `I hI v hv hle`. Rewrite `hI` using `[Ideal.isCoprime_iff_sup_eq]`. Apply `v.isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[eq_top_iff, ← hI]`. Conclude with `sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hv)`. Distinguish the cases in `h0 : 𝔞 = ⊥`. Use `⟨1, one_pow _, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `(key 𝔞 hc v hv (by rw [h0]; exact bot_le)).elim`.

Establish `h𝔞nz : 𝔞 ∈ (Ideal (𝓞 K'))⁰` using `mem_nonZeroDivisors_of_ne_zero h0`. Establish `hS : {v : HeightOneSpectrum (𝓞 K') | ((q * M : ℕ) : 𝓞 K') ∈ v.asIdeal}.Finite`. Establish `hne : Ideal.span {((q * M : ℕ) : 𝓞 K')} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.mpr (NeZero.ne _)`.

Conclude with `(Ideal.finite_factors hne).subset (fun v hv => Ideal.dvd_span_singleton.mpr hv)`. Take `⟨P, hPS, hPp, hPcl⟩` from `degOne K' _ hS (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹`. Use `set p := Ideal.absNorm P.asIdeal with hpdef`. Use `haveI : Fact p.Prime := ⟨hPp⟩`. Take `⟨π, hπ⟩` from `(red K' p P.asIdeal).1 rfl`.

Establish `hPnz : P.asIdeal ∈ (Ideal (𝓞 K'))⁰` using `mem_nonZeroDivisors_of_ne_zero P.ne_bot`. Establish `hprin : Submodule.IsPrincipal (P.asIdeal * 𝔞)`. Rewrite using `[← ClassGroup.mk0_eq_one_iff (mul_mem hPnz h𝔞nz)]`. Establish `hm : ClassGroup.mk0 ⟨P.asIdeal * 𝔞, mul_mem hPnz h𝔞nz⟩ = ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ * ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩`. Rewrite using `[← map_mul]`.

Both sides reduce to the same expression. Establish `hcl : ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ = (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹` using `hPcl`. Rewrite using `[hm, hcl, inv_mul_cancel]`. Take `⟨⟨y, hy⟩⟩` from `hprin`. Rewrite `hy` using `[Ideal.submodule_span_eq]`.

Establish `hy0 : y ≠ 0`. Introduce `h`. Rewrite `hy` using `[h, Ideal.span_singleton_eq_bot.mpr rfl]`. Conclude with `(Ideal.mul_eq_bot.mp hy).elim P.ne_bot h0`. Establish `hPc : IsCoprime P.asIdeal (Ideal.span {(q : 𝓞 K')})`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`. Establish `heq` using `P.isMaximal.eq_of_le hne le_sup_left`. Establish `hqP : (q : 𝓞 K') ∈ P.asIdeal`. Rewrite using `[heq]`.

Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Apply `hPS` to reduce the goal to its premises. Use `show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal`. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hqP`.

Establish `hpcop : p.Coprime (q * M)`. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hPp]`. Introduce and unpack `⟨k, hk⟩`. Apply `hPS` to reduce the goal to its premises. Use `show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal`.

Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ ((red K' p P.asIdeal).2 π hπ).2.2.2`. Take `⟨-, hm2, -, -, hm5⟩` from `xMul (q * M) K' b`. Take `⟨-, hn2, -, -, hn5⟩` from `xMul M K b`. Establish `hA : IsX (q * M) K' b (Ideal.span {y}) (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t)` using `hm5 y hy0`.

Establish `hXP'` using `hm2 P.asIdeal 𝔞 _ X' P.ne_bot h0 (by rw [hy]; exact hA) hX'`. Establish `hrel : Ideal.relNorm (𝓞 K) (Ideal.span {y}) ≠ ⊥`. Rewrite using `[Ne, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hy0`. Establish `hB : IsX M K b (Ideal.relNorm (𝓞 K) (Ideal.span {y})) (∏ t, ((sg M K) t)⁻¹ (Algebra.norm K (y : K')) ^ th M b ↑t)`.

Rewrite `hrel`, the goal using `[Ideal.relNorm_singleton]`. Establish `hn0 : Algebra.intNorm (𝓞 K) (𝓞 K') y ≠ 0`. Introduce `h`. Apply `hrel` to reduce the goal to its premises. Rewrite using `[h]`.

Conclude with `Ideal.span_singleton_eq_bot.mpr rfl`. Establish `h5` using `hn5 _ hn0`. Establish `hcoe : ((Algebra.intNorm (𝓞 K) (𝓞 K') y : 𝓞 K) : K) = Algebra.norm K (y : K')` using `Algebra.algebraMap_intNorm y`. Rewrite `h5` using `[hcoe]`. Conclude with `h5`.

Establish `hXP` using `hn2 _ _ _ X (mt Ideal.relNorm_eq_bot_iff.mp P.ne_bot) (mt Ideal.relNorm_eq_bot_iff.mp h0) (by rw [← map_mul, hy]; exact hB) hX`. Take `⟨ζ1, hζ1, hjac⟩` from `xCongJac M q K K' hq u hu b hbM p π hpcop _ _ (by rw [hπ]; exact hXP') (by rw [hπ]; exact hXP)`. Use `⟨ζ1⁻¹, by rw [inv_pow, hζ1, inv_one], fun v hv => ?_⟩` and prove the remaining obligations. Establish `hyv : ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal`. Introduce `v hv hyv`.

Apply `key _ (IsCoprime.mul_left hPc hc) v hv` to reduce the goal to its premises. Rewrite using `[hy, Ideal.span_singleton_le_iff_mem]`. Conclude with `hyv`. Establish `hpr` using `xCongPrin M q K K' hq u hu b hbq y hyv v hv`. Establish `hX'1` using `isX_unit (q * M) K' b q 𝔞 X' h0 hc hX' v hv`.

Establish `hP1` using `isX_unit (q * M) K' b q P.asIdeal _ P.ne_bot hPc hXP' v hv`. Establish `hX'0 : X' ≠ 0`. Introduce `h`. Rewrite `hX'1` using `[h, map_zero]`. Conclude with `zero_ne_one hX'1`.

Establish `hAv : v.valuation K' (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) = 1`. Rewrite using `[← div_mul_cancel₀ (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) hX'0, map_mul, hP1, hX'1, one_mul]`. Establish `hζv : v.valuation K' ζ1 = 1`. Establish `h` using `congrArg (v.valuation K') hζ1`. Rewrite `h` using `[map_pow, map_one]`.

Conclude with `(pow_eq_one_iff.mp h).resolve_right (mul_ne_zero two_ne_zero (NeZero.ne _))`. Establish `h2` using `hjac v hv`. Rewrite `h2` using `[map_div₀, map_div₀]`. Conclude with `alg_step (v.valuation K') _ _ X' _ ζ1 hAv hX'1 hζv hpr h2`.
-/
theorem UpperTheory.V.ML.xCong :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < M → b < q → ∀ (𝔞 : Ideal (𝓞 K')) (X' : K') (X : K), IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K')}) →
    IsX (q * M) K' b 𝔞 X' → IsX M K b (Ideal.relNorm (𝓞 K) 𝔞) X →
    ∃ ζ : K', ζ ^ (2 * (q * M)) = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → v.valuation K' (X' - ζ * algebraMap K K' ((sg M K u)⁻¹ X)) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hbM hbq 𝔞 X' X hc hX' hX
  have key : ∀ I : Ideal (𝓞 K'), IsCoprime I (Ideal.span {(q : 𝓞 K')}) →
      ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → ¬ I ≤ v.asIdeal := by
    intro I hI v hv hle
    rw [Ideal.isCoprime_iff_sup_eq] at hI
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← hI]
    exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨1, one_pow _, fun v hv => ?_⟩
    exact (key 𝔞 hc v hv (by rw [h0]; exact bot_le)).elim
  have h𝔞nz : 𝔞 ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero h0
  have hS : {v : HeightOneSpectrum (𝓞 K') | ((q * M : ℕ) : 𝓞 K') ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {((q * M : ℕ) : 𝓞 K')} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (NeZero.ne _)
    exact (Ideal.finite_factors hne).subset (fun v hv => Ideal.dvd_span_singleton.mpr hv)
  obtain ⟨P, hPS, hPp, hPcl⟩ := degOne K' _ hS (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹
  set p := Ideal.absNorm P.asIdeal with hpdef
  haveI : Fact p.Prime := ⟨hPp⟩
  obtain ⟨π, hπ⟩ := (red K' p P.asIdeal).1 rfl
  have hPnz : P.asIdeal ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hprin : Submodule.IsPrincipal (P.asIdeal * 𝔞) := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem hPnz h𝔞nz)]
    have hm : ClassGroup.mk0 ⟨P.asIdeal * 𝔞, mul_mem hPnz h𝔞nz⟩ =
        ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ * ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩ := by
      rw [← map_mul]
      rfl
    have hcl : ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ = (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹ := hPcl
    rw [hm, hcl, inv_mul_cancel]
  obtain ⟨⟨y, hy⟩⟩ := hprin
  rw [Ideal.submodule_span_eq] at hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hy
    exact (Ideal.mul_eq_bot.mp hy).elim P.ne_bot h0
  have hPc : IsCoprime P.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := P.isMaximal.eq_of_le hne le_sup_left
    have hqP : (q : 𝓞 K') ∈ P.asIdeal := by
      rw [heq]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqP
  have hpcop : p.Coprime (q * M) := by
    rw [Nat.Prime.coprime_iff_not_dvd hPp]
    rintro ⟨k, hk⟩
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ ((red K' p P.asIdeal).2 π hπ).2.2.2
  obtain ⟨-, hm2, -, -, hm5⟩ := xMul (q * M) K' b
  obtain ⟨-, hn2, -, -, hn5⟩ := xMul M K b
  have hA : IsX (q * M) K' b (Ideal.span {y}) (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) :=
    hm5 y hy0
  have hXP' := hm2 P.asIdeal 𝔞 _ X' P.ne_bot h0 (by rw [hy]; exact hA) hX'
  have hrel : Ideal.relNorm (𝓞 K) (Ideal.span {y}) ≠ ⊥ := by
    rw [Ne, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot]
    exact hy0
  have hB : IsX M K b (Ideal.relNorm (𝓞 K) (Ideal.span {y}))
      (∏ t, ((sg M K) t)⁻¹ (Algebra.norm K (y : K')) ^ th M b ↑t) := by
    rw [Ideal.relNorm_singleton] at hrel ⊢
    have hn0 : Algebra.intNorm (𝓞 K) (𝓞 K') y ≠ 0 := by
      intro h
      apply hrel
      rw [h]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have h5 := hn5 _ hn0
    have hcoe : ((Algebra.intNorm (𝓞 K) (𝓞 K') y : 𝓞 K) : K) = Algebra.norm K (y : K') :=
      Algebra.algebraMap_intNorm y
    rw [hcoe] at h5
    exact h5
  have hXP := hn2 _ _ _ X (mt Ideal.relNorm_eq_bot_iff.mp P.ne_bot) (mt Ideal.relNorm_eq_bot_iff.mp h0)
    (by rw [← map_mul, hy]; exact hB) hX
  obtain ⟨ζ1, hζ1, hjac⟩ := xCongJac M q K K' hq u hu b hbM p π hpcop _ _
    (by rw [hπ]; exact hXP') (by rw [hπ]; exact hXP)
  refine ⟨ζ1⁻¹, by rw [inv_pow, hζ1, inv_one], fun v hv => ?_⟩
  have hyv : ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal := by
    intro v hv hyv
    apply key _ (IsCoprime.mul_left hPc hc) v hv
    rw [hy, Ideal.span_singleton_le_iff_mem]
    exact hyv
  have hpr := xCongPrin M q K K' hq u hu b hbq y hyv v hv
  have hX'1 := isX_unit (q * M) K' b q 𝔞 X' h0 hc hX' v hv
  have hP1 := isX_unit (q * M) K' b q P.asIdeal _ P.ne_bot hPc hXP' v hv
  have hX'0 : X' ≠ 0 := by
    intro h
    rw [h, map_zero] at hX'1
    exact zero_ne_one hX'1
  have hAv : v.valuation K' (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) = 1 := by
    rw [← div_mul_cancel₀ (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) hX'0, map_mul, hP1, hX'1, one_mul]
  have hζv : v.valuation K' ζ1 = 1 := by
    have h := congrArg (v.valuation K') hζ1
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff.mp h).resolve_right (mul_ne_zero two_ne_zero (NeZero.ne _))
  have h2 := hjac v hv
  rw [map_div₀, map_div₀] at h2
  exact alg_step (v.valuation K') _ _ X' _ ζ1 hAv hX'1 hζv hpr h2
