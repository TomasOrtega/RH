import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMaxHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ P hP hT`. Set `KO` to `FractionRing O`. Set `S` to `MRing ι O`. Set `MainNotions` to `MRing ι KO`. Set `φ : S →+* MainNotions` to `algebraMap S MainNotions`.

Set `M : Submonoid S` to `(nonZeroDivisors O).map (C : O →+* S)`. Establish `: IsLocalization M MainNotions` using `MvPolynomial.isLocalization (nonZeroDivisors O) KO`. Establish `hPker : ∀ f ∈ P, constantCoeff f = 0`. Introduce `f hf`. Establish `h0` using `hP.multiHomog f hf 0`.

Rewrite `h0` using `[weightedHomogeneousComponent_zero]`. Establish `: coeff 0 f ∈ P.comap (C : O →+* S)` using `h0`. Rewrite `this` using `[hT, Ideal.mem_bot]`. Rewrite using `[constantCoeff_eq]`. Conclude with `this`.

Introduce `v h`. Use `congrFun h v.1` as an intermediate fact. Simplify using `[blockWeight] at this`. Establish `hdisj : Disjoint (M : Set S) (P : Set S)`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ hmem`. Establish `: a ∈ P.comap (C : O →+* S)` using `hmem`. Rewrite `this` using `[hT, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero ha this`. Establish `hPK : (genFib P).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj`.

Set `N : Ideal MainNotions` to `RingHom.ker (constantCoeff : MainNotions →+* KO)`. Establish `hNmax : N.IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩`. Establish `hPN : genFib P ≤ N`. Rewrite using `[genFib, Ideal.map_le_iff_le_comap]`. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]`. Set `A` to `MainNotions ⧸ genFib P`. Set `mk : MainNotions →+* A` to `Ideal.Quotient.mk (genFib P)`. Establish `hmk : Function.Surjective mk` using `Ideal.Quotient.mk_surjective`. Establish `hcomapN : (N.map mk).comap mk = N`.

Rewrite using `[Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]`. Set `m : Ideal A` to `N.map mk`. Establish `hm : m.IsMaximal`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `: N = ⊤` using `by rw [← hcomapN, h, Ideal.comap_top]`. Conclude with `hNmax.ne_top this`. Conclude with `h`. Establish `: Algebra.FiniteType KO A` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P)) (Ideal.Quotient.mkₐ_surjective KO _)`. Establish `hht : (m.height : WithBot ℕ∞) = ringKrullDim A` using `hmax KO A m hm`.

Set `g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R` to `S) (P : Set S) := fun x => ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by`. Rewrite using `[PrimeSpectrum.mem_zeroLocus]`. Introduce `f hf`. Use `show mk (φ f) ∈ x.asIdeal`. Establish `h0 : mk (φ f) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)`.

Rewrite using `[h0]`. Conclude with `x.asIdeal.zero_mem⟩`. Establish `hg : StrictMono g`. Introduce `x y hxy`. Establish `h1 : x.asIdeal.comap mk < y.asIdeal.comap mk` using `lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h => hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))`.

Conclude with `(IsLocalization.orderEmbedding M MainNotions).strictMono h1`. Establish `hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0`. Introduce `f`. Rewrite using `[hcomapN, Ideal.mem_comap, RingHom.mem_ker]`. Use `show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _`.

Rewrite using `[constantCoeff_map]`. Conclude with `⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Set `M1 : Ideal S` to `(IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)`. Set `top : PrimeSpectrum.zeroLocus (R` to `S) (P : Set S) := ⟨⟨M1, inferInstance⟩, by`.

Rewrite using `[PrimeSpectrum.mem_zeroLocus]`. Introduce `f hf`. Use `show constantCoeff f ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[hPker f hf]`. Conclude with `Ideal.zero_mem _⟩`.

Establish `htop : g ⟨m, hm.isPrime⟩ < top` using `by show (m.comap mk).comap φ < M1`. Use `lt_of_le_of_ne (fun f hf => ?_) fun h => ?_` and prove the remaining obligations. Use `show constantCoeff f ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[(hlastN f).mp hf]`. Conclude with `Ideal.zero_mem _`.

Establish `hC : (C ϖ : S) ∈ M1` using `by show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[constantCoeff_C]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit`. Rewrite `hC` using `[← h, hlastN, constantCoeff_C]`. Conclude with `hϖ.ne_zero hC`.

Establish `key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R` using `S) (P : Set S)) := by`. Introduce `n hn`. Rewrite `hn` using `[show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩]`. Take `⟨p, hplast, hplen⟩` from `Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn`. Establish `hlt : (p.map g hg).last < top`.

Rewrite using `[LTSeries.last_map, hplast]`. Conclude with `htop`. Use `Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)` as an intermediate fact. Simplify `this` using `[hplen]`. Rewrite using `[← hht, ringKrullDim_quotient P]`.

Establish `h1` using `key 0 (by simp)`. Establish `hne : Order.krullDim (PrimeSpectrum.zeroLocus (R` using `S) (P : Set S)) ≠ ⊥ := fun h => by`. Rewrite `h1` using `[h]`. Simplify using `at h1`. Take `⟨d, hd⟩` from `WithBot.ne_bot_iff_exists.mp hne`.

Rewrite `key`, the goal using `[← hd]`. Rewrite using `[← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]`. Use `ENat.forall_natCast_le_iff_le.mp fun a ha => ?_` and prove the remaining obligations. Break down `a with _ | k` into its components or cases. Simplify using the standard rewrite rules.

Establish `hk : (k : ℕ∞) ≤ m.height`. Establish `: (k : ℕ∞) + 1 ≤ m.height + 1` using `by exact_mod_cast ha`. Conclude with `(ENat.add_le_add_iff_right ENat.one_ne_top).mp this`. Use `key k hk` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem GenericDimBound.proof (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : coeff 0 f ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  have key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height →
      ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) := by
    intro n hn
    rw [show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩] at hn
    obtain ⟨p, hplast, hplen⟩ :=
      Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn
    have hlt : (p.map g hg).last < top := by
      rw [LTSeries.last_map, hplast]
      exact htop
    have := Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)
    simpa [hplen] using this

  rw [← hht, ringKrullDim_quotient P]
  have h1 := key 0 (by simp)
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) ≠ ⊥ := fun h => by
    rw [h] at h1; simp at h1
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at key ⊢
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases a with _ | k
  · simp
  · have hk : (k : ℕ∞) ≤ m.height := by
      have : (k : ℕ∞) + 1 ≤ m.height + 1 := by exact_mod_cast ha
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
    have := key k hk
    exact_mod_cast this

end GroundTheory.Heights₂.Heights.NumbersDVR
