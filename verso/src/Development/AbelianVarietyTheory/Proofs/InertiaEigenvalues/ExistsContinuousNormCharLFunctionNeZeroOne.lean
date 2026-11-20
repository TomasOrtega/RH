import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacterStatement

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory
namespace NormCharL

/- English proof (translation)
Take `⟨γ, hγ⟩` from `Ideal.mem_span_singleton'.1 h`. Establish `hβ : β = 1 + (m : 𝓞 K) * γ` using `by rw [mul_comm, hγ]; ring`. Set `b` to `Module.Free.chooseBasis ℤ (𝓞 K)`. Establish `key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1`. Rewrite using `[hβ, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Establish `h2` using `(Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)`. Rewrite `h2` using `[key, Matrix.det_one, ← Algebra.norm_eq_matrix_det]`. Simplify using `using h2`.
-/
theorem norm_cast_eq_one (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h hdvd`. Take `⟨i, hi, y, hy, hiy⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)}`.

Rewrite using `[Ideal.mem_span_singleton']`. Conclude with `⟨-z, by rw [← hiy]; ring⟩`. Establish `h1` using `GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem`. Establish `hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs`. Rewrite using `[← Ideal.absNorm_span_singleton]`.

Conclude with `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)`. Establish `hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `Int.natCast_dvd.2 (hdvd.trans hd)`. Rewrite `h1` using `[hz]`.

Establish `: Fact m.Prime` using `⟨hm⟩`. Conclude with `zero_ne_one h1`. Introduce `h`. Establish `hc : Nat.Coprime (Ideal.absNorm I) m` using `(Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hc`.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K)`. Use `congrArg (Int.cast : ℤ → 𝓞 K) huv` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this.symm`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I))) (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))`.
-/
theorem sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by
  constructor
  · intro h hdvd
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨-z, by rw [← hiy]; ring⟩
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem
    have hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs := by
      rw [← Ideal.absNorm_span_singleton]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 (hdvd.trans hd)
    rw [hz] at h1
    have : Fact m.Prime := ⟨hm⟩
    exact zero_ne_one h1
  · intro h
    have hc : Nat.Coprime (Ideal.absNorm I) m := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this
      exact this.symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

/- English proof (translation)
Introduce `K _ _ m hm χ cl hcl hχ`. Establish `: Fact m.Prime` using `⟨hm⟩`. Use `set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef`. Set `ψ : ZMod m → ℂ` to `fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)`. Establish `hψ0 : ψ 0 = 0` using `by simp [ψ]`.

Establish `hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y`. Introduce `x y`. Distinguish the cases in `hx : x = 0`. Simplify using `[ψ, hx]`. Distinguish the cases in `hy : y = 0`.

Simplify using `[ψ, hy]`. Establish `hxy : x * y ≠ 0` using `mul_ne_zero hx hy`. Simplify using `only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]`. Rewrite using `[← Units.val_mul, ← map_mul]`. Use `congr 3`.

Use `ext`. Simplify using the standard rewrite rules. Establish `hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ)`. Introduce `u`. Simplify using `only [ψ, dif_neg u.ne_zero]`.

Use `congr 3`. Use `ext`. Simplify using the standard rewrite rules. Set `X : Ideal (𝓞 K) → ℂ` to `fun I => ψ (Ideal.absNorm I : ZMod m)`. Establish `hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0`.

Introduce `I`. Rewrite using `[GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]`. Establish `hM0 : M ≠ ⊥`. Rewrite using `[hMdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hm.ne_zero` after adjusting the coercions.

Establish `hX0 : X ⊥ = 0` using `by simp [X, hψ0]`. Establish `hXmul : ∀ I J, X (I * J) = X I * X J`. Introduce `I J`. Simplify using `only [X, map_mul, Nat.cast_mul, hψmul]`. Establish `hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1`.

Introduce `I _ hI`. Establish `hne` using `(hcop I).1 hI`. Simplify using `only [X, ψ, dif_neg hne]`. Conclude with `GlobalTheory.Mem.RayPrimes.norm_char χ _`. Establish `hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0`.

Introduce `I hI`. Establish `: (Ideal.absNorm I : ZMod m) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hI ((hcop I).2 h)`. Simplify using `[X, this, hψ0]`.

Use `set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε`. Establish `hεε : ε * ε = 1`. Rewrite using `[hε, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Take `⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩` from `GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε`.

Establish `hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β)`. Introduce `β hβ0 hβ1`. Rewrite using `[hφβ β hβ0]`. Establish `h1` using `GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1`. Establish `hN0 : Algebra.norm ℤ β ≠ 0`.

Rewrite using `[Ne, Algebra.norm_eq_zero_iff]`. Conclude with `hβ0`. Simplify using `only [X, Ideal.absNorm_span_singleton]`. Use `split_ifs with hpos`. Establish `: (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1`.

Rewrite using `[← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]`. Rewrite using `[this, ← Units.val_one, hψunit]`. Simplify using the standard rewrite rules. Establish `hneg : Algebra.norm ℤ β ≤ 0` using `le_of_not_gt hpos`. Establish `: (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m)`.

Rewrite using `[← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]`. Simplify using the standard rewrite rules. Rewrite using `[this, hψunit]`. Take `⟨P, hPm, hPχ⟩` from `hχ`. Establish `hPtop : P.asIdeal ⊔ M = ⊤` using `(GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm`.

Establish `hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) : X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ)` using `by show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _`. Rewrite using `[← hcl Q hQ, hψunit]`. Establish `hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1`. Use `⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩` and prove the remaining obligations. Rewrite using `[hclX P hPm]`.

Introduce `h`. Conclude with `hPχ (Units.val_eq_one.1 h)`. Set `c : HeightOneSpectrum (𝓞 K) → ℂ` to `fun Q => ((χ (cl Q) : ℂˣ) : ℂ)`. Establish `hc : ∀ Q, ‖c Q‖ ≤ 1` using `fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le`. Establish `hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal`.

Introduce `Q hQ`. Establish `hmax : Q.asIdeal.IsMaximal` using `Q.isMaximal`. Establish `htop : Q.asIdeal ⊔ M = ⊤`. Use `hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)` and prove the remaining obligations. Introduce `h`.

Conclude with `hQ (h ▸ le_sup_right)`. Rewrite using `[hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]`. Take `⟨L, hLd, hLe, hL1⟩` from `GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX`. Use `⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_) show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re` and prove the remaining obligations.

Rewrite using `[Complex.ofReal_re]`. Conclude with `lt_of_lt_of_le one_pos (le_max_right _ _)`. Simplify using `using hL1`. Introduce `s hs`. Establish `hmax : max (s : ℂ).re 1 = s`.

Rewrite using `[Complex.ofReal_re]`. Conclude with `max_eq_left hs.le`. Simplify using `only [hmax]`. Conclude with `(hLe s (by rwa [Complex.ofReal_re])).symm`.
-/
theorem exists_continuous_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  intro K _ _ m hm χ cl hcl hχ
  have : Fact m.Prime := ⟨hm⟩
  set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef
  let ψ : ZMod m → ℂ := fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x = 0
    · simp [ψ, hx]
    by_cases hy : y = 0
    · simp [ψ, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp
  have hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ) := by
    intro u
    simp only [ψ, dif_neg u.ne_zero]
    congr 3
    ext
    simp
  let X : Ideal (𝓞 K) → ℂ := fun I => ψ (Ideal.absNorm I : ZMod m)
  have hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0 := by
    intro I
    rw [GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]
  have hM0 : M ≠ ⊥ := by
    rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hX0 : X ⊥ = 0 := by simp [X, hψ0]
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    simp only [X, map_mul, Nat.cast_mul, hψmul]
  have hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1 := by
    intro I _ hI
    have hne := (hcop I).1 hI
    simp only [X, ψ, dif_neg hne]
    exact GlobalTheory.Mem.RayPrimes.norm_char χ _
  have hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0 := by
    intro I hI
    have : (Ideal.absNorm I : ZMod m) = 0 := by
      by_contra h
      exact hI ((hcop I).2 h)
    simp [X, this, hψ0]
  set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← Units.val_mul, ← map_mul]
    simp
  obtain ⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩ := GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε
  have hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β) := by
    intro β hβ0 hβ1
    rw [hφβ β hβ0]
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1
    have hN0 : Algebra.norm ℤ β ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hβ0
    simp only [X, Ideal.absNorm_span_singleton]
    split_ifs with hpos
    · have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1 := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]
      rw [this, ← Units.val_one, hψunit]
      simp
    · have hneg : Algebra.norm ℤ β ≤ 0 := le_of_not_gt hpos
      have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]
        simp
      rw [this, hψunit]
  obtain ⟨P, hPm, hPχ⟩ := hχ
  have hPtop : P.asIdeal ⊔ M = ⊤ := (GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm
  have hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) :
      X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ) := by
    show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _
    rw [← hcl Q hQ, hψunit]
  have hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1 := by
    refine ⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩
    rw [hclX P hPm]
    intro h
    exact hPχ (Units.val_eq_one.1 h)
  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun Q => ((χ (cl Q) : ℂˣ) : ℂ)
  have hc : ∀ Q, ‖c Q‖ ≤ 1 := fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le
  have hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal := by
    intro Q hQ
    have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
    have htop : Q.asIdeal ⊔ M = ⊤ := by
      refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro h
      exact hQ (h ▸ le_sup_right)
    rw [hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]
  obtain ⟨L, hLd, hLe, hL1⟩ := GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul
    hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX
  refine ⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · refine hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_)
    show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · simpa using hL1
  · intro s hs
    have hmax : max (s : ℂ).re 1 = s := by
      rw [Complex.ofReal_re]
      exact max_eq_left hs.le
    simp only [hmax]
    exact (hLe s (by rwa [Complex.ofReal_re])).symm

end NormCharL
end GlobalTheory
