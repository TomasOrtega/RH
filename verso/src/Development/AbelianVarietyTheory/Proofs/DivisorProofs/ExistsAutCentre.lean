import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.ThmAMove

section Val

variable {K : Type} [Field K] (A : ValuationSubring K)

/- English proof (translation)
Set `k : FractionRing R →+* FractionRing S` to `IsFractionRing.map (j := algebraMap R S) hinj`. Use `letI : Algebra (FractionRing R) (FractionRing S) := k.toAlgebra`. Use `letI : Algebra (FractionRing R) K := jk.toAlgebra`. Establish `hi : ∀ a : S, IsIntegral (FractionRing R) (algebraMap S (FractionRing S) a)` using `fun a => IsIntegral.map_of_comp_eq (algebraMap R (FractionRing R)) (algebraMap S (FractionRing S)) (RingHom.ext fun r => by show k (algebraMap R _ r) = _`. Simplify using `[k, IsFractionRing.map]) (Algebra.IsIntegral.isIntegral a)`.

Use `haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := ⟨fun x => by`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := S) x`. Rewrite using `[div_eq_mul_inv]`. Conclude with `((hi a).mul (hi b).inv).isAlgebraic⟩`. Set `j : FractionRing S →ₐ[FractionRing R] K` to `IsAlgClosed.lift`.

Conclude with `⟨j.toRingHom, fun x => j.commutes x⟩`.
-/
theorem exists_ext {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [IsAlgClosed K] (jk : FractionRing R →+* K) :
    ∃ je : FractionRing S →+* K, ∀ x, je (IsFractionRing.map (j := algebraMap R S) hinj x) = jk x := by
  let k : FractionRing R →+* FractionRing S := IsFractionRing.map (j := algebraMap R S) hinj
  letI : Algebra (FractionRing R) (FractionRing S) := k.toAlgebra
  letI : Algebra (FractionRing R) K := jk.toAlgebra
  have hi : ∀ a : S, IsIntegral (FractionRing R) (algebraMap S (FractionRing S) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap R (FractionRing R)) (algebraMap S (FractionRing S))
      (RingHom.ext fun r => by
        show k (algebraMap R _ r) = _
        simp [k, IsFractionRing.map]) (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    rw [div_eq_mul_inv]
    exact ((hi a).mul (hi b).inv).isAlgebraic⟩
  let j : FractionRing S →ₐ[FractionRing R] K := IsAlgClosed.lift
  exact ⟨j.toRingHom, fun x => j.commutes x⟩

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `using h`. Establish `hy' : A.valuation (je y) ≠ 0` using `by simpa using hy`.

Establish `h1 : A.valuation (je (x / y)) = 1` using `by rw [map_div₀, map_div₀, h, div_self hy']`. Break down `ValuationRing.isInteger_or_isInteger S (x / y) with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Take `⟨u, rfl⟩` from `hu a (by rw [ha, h1])`. Conclude with `⟨u, by rw [ha, div_mul_cancel₀ _ hy]⟩`. Take `⟨u, rfl⟩` from `hu a (by rw [ha, map_inv₀, map_inv₀, h1, inv_one])`.

Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, ha, inv_inv, div_mul_cancel₀ _ hy]`.
-/
theorem exists_unit {S : Type} [CommRing S] [IsDomain S] [ValuationRing S] (je : FractionRing S →+* K)
    (hA : ∀ a : S, je (algebraMap S _ a) ∈ A) (hu : ∀ a : S, A.valuation (je (algebraMap S _ a)) = 1 → IsUnit a)
    {x y : FractionRing S} (h : A.valuation (je x) = A.valuation (je y)) : ∃ u : Sˣ, x = algebraMap S _ (u : S) * y := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨1, ?_⟩
    simpa using h
  have hy' : A.valuation (je y) ≠ 0 := by simpa using hy
  have h1 : A.valuation (je (x / y)) = 1 := by rw [map_div₀, map_div₀, h, div_self hy']
  rcases ValuationRing.isInteger_or_isInteger S (x / y) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, h1])
    exact ⟨u, by rw [ha, div_mul_cancel₀ _ hy]⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, map_inv₀, map_inv₀, h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, ha, inv_inv, div_mul_cancel₀ _ hy]

/- English proof (translation)
Establish `hle : ∀ r, A.valuation (f r) ≤ 1` using `fun r => (A.valuation_le_one_iff _).2 (hf r)`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `h0 : (l : R) ≠ 0` using `fun h => hl0 (by rw [← map_natCast f, h, map_zero])`.

Take `⟨n, u, hn⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`. Rewrite `ha` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Establish `hd : (l : R) ∣ a ^ n`. Rewrite using `[hn, Units.mul_left_dvd]`. Conclude with `pow_dvd_pow_of_dvd ha n`.

Take `⟨c, hc⟩` from `hd`. Use `lt_of_le_of_ne (hle a) fun h1 => ?_` and prove the remaining obligations. Establish `h2` using `congrArg (fun r => A.valuation (f r)) hc`. Simplify using `only [map_pow, map_mul, map_natCast, h1, one_pow] at h2`. Conclude with `absurd h2 (mul_lt_one_of_lt_of_le hl (hle c)).ne'`.

Introduce `h`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, rfl⟩`. Establish `h2 : A.valuation (f u) * A.valuation (f (u⁻¹ : Rˣ)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`.

Conclude with `absurd h2 (mul_lt_one_of_lt_of_le h (hle _)).ne`.
-/
theorem mem_max_iff {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : R →+* K) (hf : ∀ r, f r ∈ A) {l : ℕ}
    (hl0 : (l : K) ≠ 0) (hl : A.valuation (l : K) < 1) (a : R) :
    a ∈ IsLocalRing.maximalIdeal R ↔ A.valuation (f a) < 1 := by
  have hle : ∀ r, A.valuation (f r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hf r)
  constructor
  · intro ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have h0 : (l : R) ≠ 0 := fun h => hl0 (by rw [← map_natCast f, h, map_zero])
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    have hd : (l : R) ∣ a ^ n := by
      rw [hn, Units.mul_left_dvd]
      exact pow_dvd_pow_of_dvd ha n
    obtain ⟨c, hc⟩ := hd
    refine lt_of_le_of_ne (hle a) fun h1 => ?_
    have h2 := congrArg (fun r => A.valuation (f r)) hc
    simp only [map_pow, map_mul, map_natCast, h1, one_pow] at h2
    exact absurd h2 (mul_lt_one_of_lt_of_le hl (hle c)).ne'
  · intro h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h2 : A.valuation (f u) * A.valuation (f (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_lt_of_le h (hle _)).ne

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Rewrite using `[A.valuation_le_one_iff]`. Establish `h : IsIntegral A (β x)` using `IsIntegral.map_of_comp_eq (Int.castRingHom A) β (RingHom.ext_int _ _) x.isIntegral_coe`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Conclude with `hy ▸ y.2`.
-/
theorem int_le_one (β : L →+* K) (x : 𝓞 L) : A.valuation (β x) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  have h : IsIntegral A (β x) := IsIntegral.map_of_comp_eq (Int.castRingHom A) β (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact hy ▸ y.2

/- English proof (translation)
Take `⟨n, d, e⟩` from `P.exists_primeCompl_mul_eq_of_integer y hy.le`. Establish `h1 : ∀ x : 𝓞 L, x ∉ P.asIdeal → A.valuation (β x) = 1` using `fun x hx => le_antisymm (int_le_one A β x) (not_lt.1 fun h' => hx ((h x).1 h'))`. Establish `hd : P.valuation L (algebraMap (𝓞 L) L d) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 d.2`.

Establish `hn : n ∉ P.asIdeal`. Rewrite using `[← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]`. Use `show P.valuation L (algebraMap (𝓞 L) L n) = 1`. Rewrite using `[← e, map_mul, hy, hd, one_mul]`. Establish `h2` using `congrArg (fun r => A.valuation (β r)) e`.

Simplify using `only [map_mul] at h2`. Rewrite `h2` using `[show A.valuation (β (algebraMap (𝓞 L) L d)) = 1 from h1 _ d.2, show A.valuation (β (algebraMap (𝓞 L) L n)) = 1 from h1 _ hn, mul_one]`. Conclude with `h2`.
-/
theorem unit_of_centre (β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) (h : ∀ x : 𝓞 L, A.valuation (β x) < 1 ↔ x ∈ P.asIdeal)
    (y : L) (hy : P.valuation L y = 1) : A.valuation (β y) = 1 := by
  obtain ⟨n, d, e⟩ := P.exists_primeCompl_mul_eq_of_integer y hy.le
  have h1 : ∀ x : 𝓞 L, x ∉ P.asIdeal → A.valuation (β x) = 1 := fun x hx =>
    le_antisymm (int_le_one A β x) (not_lt.1 fun h' => hx ((h x).1 h'))
  have hd : P.valuation L (algebraMap (𝓞 L) L d) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 d.2
  have hn : n ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show P.valuation L (algebraMap (𝓞 L) L n) = 1
    rw [← e, map_mul, hy, hd, one_mul]
  have h2 := congrArg (fun r => A.valuation (β r)) e
  simp only [map_mul] at h2
  rw [show A.valuation (β (algebraMap (𝓞 L) L d)) = 1 from h1 _ d.2, show A.valuation (β (algebraMap (𝓞 L) L n)) = 1 from h1 _ hn,
    mul_one] at h2
  exact h2

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hl1 : (l : L) ≠ 0` using `Nat.cast_ne_zero.2 hl0`. Establish `e1 : P.valuation L x = WithZero.exp (WithZero.log (P.valuation L x))` using `(WithZero.exp_log (by simpa using hx)).symm`. Establish `e2 : P.valuation L (l : L) = WithZero.exp (WithZero.log (P.valuation L (l : L)))` using `(WithZero.exp_log (by simpa using hl1)).symm`.

Generalize the expression as in `WithZero.log (P.valuation L x) = n at e1`. Generalize the expression as in `WithZero.log (P.valuation L (l : L)) = e at e2`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Conclude with `hl e2`.

Establish `hy : P.valuation L (x ^ e * (l : L) ^ (-n)) = 1`. Rewrite using `[map_mul, map_zpow₀, map_zpow₀, e1, e2, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]`. Simplify using `[mul_comm]`. Establish `h1` using `(hα _ hy).trans (hβ _ hy).symm`. Simplify using `only [map_mul, map_zpow₀, map_natCast] at h1`.

Establish `h0 : A.valuation (l : K) ^ (-n) ≠ 0` using `zpow_ne_zero _ (by`. Rewrite using `[← map_natCast α, map_ne_zero, map_ne_zero]`. Conclude with `hl1)`. Conclude with `(zpow_left_inj₀ zero_le' zero_le' he).1 (mul_right_cancel₀ h0 h1)`.
-/
theorem val_eq_of_unit (α β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) {l : ℕ} (hl0 : l ≠ 0) (hl : P.valuation L (l : L) ≠ 1)
    (hα : ∀ y, P.valuation L y = 1 → A.valuation (α y) = 1) (hβ : ∀ y, P.valuation L y = 1 → A.valuation (β y) = 1) (x : L) :
    A.valuation (α x) = A.valuation (β x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hl1 : (l : L) ≠ 0 := Nat.cast_ne_zero.2 hl0
  have e1 : P.valuation L x = WithZero.exp (WithZero.log (P.valuation L x)) := (WithZero.exp_log (by simpa using hx)).symm
  have e2 : P.valuation L (l : L) = WithZero.exp (WithZero.log (P.valuation L (l : L))) :=
    (WithZero.exp_log (by simpa using hl1)).symm
  generalize WithZero.log (P.valuation L x) = n at e1
  generalize WithZero.log (P.valuation L (l : L)) = e at e2
  have he : e ≠ 0 := by
    rintro rfl
    exact hl e2
  have hy : P.valuation L (x ^ e * (l : L) ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, map_zpow₀, e1, e2, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [mul_comm]
  have h1 := (hα _ hy).trans (hβ _ hy).symm
  simp only [map_mul, map_zpow₀, map_natCast] at h1
  have h0 : A.valuation (l : K) ^ (-n) ≠ 0 := zpow_ne_zero _ (by
    rw [← map_natCast α, map_ne_zero, map_ne_zero]; exact hl1)
  exact (zpow_left_inj₀ zero_le' zero_le' he).1 (mul_right_cancel₀ h0 h1)

/- English proof (translation)
Set `f : 𝓞 L →+* A` to `(β.comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (int_le_one A β x)`. Set `P' : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP' : ∀ x : 𝓞 L, x ∈ P' ↔ A.valuation (β x) < 1` using `fun x => A.valuation_lt_one_iff (f x)`. Use `haveI : P'.IsPrime := Ideal.comap_isPrime _ _`. Use `haveI := P.isPrime`.

Use `haveI : P'.LiesOver (P.asIdeal.under (𝓞 L0)) := ⟨Ideal.ext fun x => ((hP' (algebraMap (𝓞 L0) (𝓞 L) x)).trans (h x)).symm⟩`. Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (P.asIdeal.under (𝓞 L0)) P.asIdeal P' (L ≃ₐ[L0] L)`. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, hP']`. Both sides reduce to the same expression.
-/
theorem exists_aut_centre [IsGalois ℚ L] (L0 : IntermediateField ℚ L) (β : L →+* K) (P : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L0, A.valuation (β ((x : L0) : L)) < 1 ↔ algebraMap (𝓞 L0) (𝓞 L) x ∈ P.asIdeal) :
    ∃ σ : L ≃ₐ[L0] L, ∀ x : 𝓞 L, A.valuation (β (σ x)) < 1 ↔ x ∈ P.asIdeal := by
  let f : 𝓞 L →+* A := (β.comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (int_le_one A β x)
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP' : ∀ x : 𝓞 L, x ∈ P' ↔ A.valuation (β x) < 1 := fun x => A.valuation_lt_one_iff (f x)
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI := P.isPrime
  haveI : P'.LiesOver (P.asIdeal.under (𝓞 L0)) := ⟨Ideal.ext fun x => ((hP' (algebraMap (𝓞 L0) (𝓞 L) x)).trans (h x)).symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.asIdeal.under (𝓞 L0)) P.asIdeal P' (L ≃ₐ[L0] L)
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, hP']
  rfl

end Val

/- English proof (translation)
Take `⟨x, hx⟩` from `ha.quot.surjective (toAb K Ω σ)⁻¹`. Set `t : (Af K)ˣ` to `Units.map (MonoidHom.snd (InfiniteAdeleRing K) (Af K)) x`. Set `y : (InfiniteAdeleRing K)ˣ` to `Units.map (MonoidHom.fst (InfiniteAdeleRing K) (Af K)) x`. Establish `hy : y ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ`. Set `T : Set (InfiniteAdeleRing K)` to `Set.univ.pi fun w => {0}ᶜ`.

Establish `hS : ∀ w : InfinitePlace K, IsPreconnected ({0}ᶜ : Set w.Completion)` using `fun w => by`. Establish `hw` using `IsTotallyComplex.isComplex w`. Use `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2 (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`.

Conclude with `(map_ne_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)).symm`. Establish `hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T)`. Rewrite using `[← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]`. Conclude with `isPreconnected_univ_pi hS`. Introduce `y hy`.

Establish `: IsUnit y` using `Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ (hy w trivial)`. Conclude with `this`. Establish `hm : ∀ u : (InfiniteAdeleRing K)ˣ, u ∈ (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T` using `fun u w _ => (Pi.isUnit_iff.1 u.isUnit w).ne_zero`. Conclude with `hp.subset_connectedComponent (hm 1) (hm y)`. Set `y' : Ideles K` to `Units.map (MonoidHom.inl (InfiniteAdeleRing K) (Af K)) y`.

Establish `h1 : art y' = 1`. Rewrite using `[← MonoidHom.mem_ker, ha.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)`. Establish `e : x = y' * finIdele K t`. Use extensionality with `: 1`.

Apply `Prod.ext` to reduce the goal to its premises. Use `show _ = _ * 1`. Rewrite using `[mul_one]`. Both sides reduce to the same expression. Use `show _ = 1 * _`.

Rewrite using `[one_mul]`. Both sides reduce to the same expression. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol, inv_eq_iff_eq_inv, ← hx]`. Use `conv_rhs => rw [e, map_mul, h1, one_mul]`.
-/
theorem exists_symbol {K Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (σ : Formalism.ConjugateSelfDual.G K Ω) :
    ∃ t, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ := by
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω σ)⁻¹
  let t : (Af K)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing K) (Af K)) x
  let y : (InfiniteAdeleRing K)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing K) (Af K)) x
  have hy : y ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ := by
    let T : Set (InfiniteAdeleRing K) := Set.univ.pi fun w => {0}ᶜ
    have hS : ∀ w : InfinitePlace K, IsPreconnected ({0}ᶜ : Set w.Completion) := fun w => by
      have hw := IsTotallyComplex.isComplex w
      have := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
        (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected
      convert this using 1
      ext z
      exact (map_ne_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)).symm
    have hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T) := by
      rw [← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
      · exact isPreconnected_univ_pi hS
      · intro y hy
        have : IsUnit y := Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ (hy w trivial)
        exact this
    have hm : ∀ u : (InfiniteAdeleRing K)ˣ, u ∈ (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T :=
      fun u w _ => (Pi.isUnit_iff.1 u.isUnit w).ne_zero
    exact hp.subset_connectedComponent (hm 1) (hm y)
  let y' : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (Af K)) y
  have h1 : art y' = 1 := by
    rw [← MonoidHom.mem_ker, ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
  have e : x = y' * finIdele K t := by
    ext : 1
    apply Prod.ext
    · show _ = _ * 1
      rw [mul_one]; rfl
    · show _ = 1 * _
      rw [one_mul]; rfl
  refine ⟨t, ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol, inv_eq_iff_eq_inv, ← hx]
  conv_rhs => rw [e, map_mul, h1, one_mul]

/- English proof (translation)
Establish `hN : l ^ (n + 1) ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Use `haveI : NeZero (l ^ (n + 1)) := ⟨hN⟩`. Establish `hζ` using `Complex.isPrimitiveRoot_exp _ hN`. Generalize the expression as in `Complex.exp _ = ζ at hζ`. Establish `hg : IsPrimitiveRoot (g ζ) (l ^ (n + 1))` using `hζ.map_of_injective g.injective`.

Take `⟨e, -, he⟩` from `hζ.eq_pow_of_pow_eq_one hg.pow_eq_one`. Establish `hec : e.Coprime (l ^ (n + 1))` using `(hζ.pow_iff_coprime (Nat.pos_of_ne_zero hN) e).1 (he ▸ hg)`. Establish `hel : IsCoprime (e : ℤ) (l : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff n.succ_pos _ _).1 hec)`. Take `⟨u, v, huv⟩ : IsCoprime c ((l : ℤ) ^ (n + 1))` from `hc.pow_right`. Establish `hu : IsCoprime u (l : ℤ)` using `⟨c, v * l ^ n, by rw [← huv]; ring⟩`.

Use `⟨u * e, hu.mul_left hel, MonoidHom.ext fun q => ?_⟩` and prove the remaining obligations. Establish `h1 : ψ q ^ l ^ (n + 1) = 1` using `by rw [pow_succ, pow_mul, h, one_pow]`. Establish `h2 : ψ q ^ (c * (u * e)) = ψ q ^ e`. Rewrite using `[show c * (u * e) = e + ((l ^ (n + 1) : ℕ) : ℤ) * (-(v * e)) by push_cast; linear_combination (e : ℤ) * huv, zpow_add, zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]`. Take `⟨k, -, hk⟩` from `hζ.eq_pow_of_pow_eq_one (ξ := (ψ q : ℂ)) (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])`.

Use `Eq.trans (Units.ext ?_) h2.symm` and prove the remaining obligations. Use `show g (ψ q : ℂ) = _`. Rewrite using `[Units.val_pow_eq_pow_val, ← hk, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem exists_exponent {G : Type} [CommGroup G] (ψ : G →* ℂˣ) {l n : ℕ} (hl : l.Prime) (h : ∀ q, ψ q ^ l ^ n = 1) (g : ℂ ≃+* ℂ)
    {c : ℤ} (hc : IsCoprime c (l : ℤ)) :
    ∃ a : ℤ, IsCoprime a (l : ℤ) ∧ (Units.map g.toRingHom.toMonoidHom).comp ψ = ψ ^ (c * a) := by
  have hN : l ^ (n + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨hN⟩
  have hζ := Complex.isPrimitiveRoot_exp _ hN
  generalize Complex.exp _ = ζ at hζ
  have hg : IsPrimitiveRoot (g ζ) (l ^ (n + 1)) := hζ.map_of_injective g.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hec : e.Coprime (l ^ (n + 1)) := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero hN) e).1 (he ▸ hg)
  have hel : IsCoprime (e : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff n.succ_pos _ _).1 hec)
  obtain ⟨u, v, huv⟩ : IsCoprime c ((l : ℤ) ^ (n + 1)) := hc.pow_right
  have hu : IsCoprime u (l : ℤ) := ⟨c, v * l ^ n, by rw [← huv]; ring⟩
  refine ⟨u * e, hu.mul_left hel, MonoidHom.ext fun q => ?_⟩
  have h1 : ψ q ^ l ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, h, one_pow]
  have h2 : ψ q ^ (c * (u * e)) = ψ q ^ e := by
    rw [show c * (u * e) = e + ((l ^ (n + 1) : ℕ) : ℤ) * (-(v * e)) by push_cast; linear_combination (e : ℤ) * huv, zpow_add,
      zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (ψ q : ℂ)) (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  refine Eq.trans (Units.ext ?_) h2.symm
  show g (ψ q : ℂ) = _
  rw [Units.val_pow_eq_pow_val, ← hk, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols in

/- English proof (translation)
Take `⟨T₀', T', a1, -, a2, -, a3⟩` from `hG E K d δ ι I φ s κ 𝔣 Q χ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11`. Take `rfl : T₀' = T₀` from `a1.unique hT₀`. Take `rfl : T' = T` from `funext fun ψ => (a2 ψ).unique (hT ψ)`. Use `haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by`. Establish `h` using `congrArg (InfinitePlace.embedding_of_isReal hw) h4`.

Rewrite `h` using `[map_pow, map_neg, map_natCast]`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast h3`. Use polynomial arithmetic with `[sq_nonneg (InfinitePlace.embedding_of_isReal hw δ)]⟩`. Set `Ω` to `AlgebraicClosure K`. Use `letI : Algebra K ℂ := ι.toAlgebra`.

Set `j : Ω →ₐ[K] ℂ` to `IsAlgClosed.lift`. Use `letI : Algebra Ω ℂ := j.toRingHom.toAlgebra`. Use `haveI : IsScalarTower K Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`. Establish `hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x` using `fun x => by`. Express the relevant statement in the definitionally equal form `g (ι x) = ι x`.

Rewrite using `[← h6 (Classical.arbitrary I)]`. Conclude with `hφ _ _`. Set `gK : ℂ ≃ₐ[K] ℂ` to `AlgEquiv.ofRingEquiv (f := g) hg`. Take `⟨art, ha⟩` from `hA K Ω`. Take `⟨t, ht⟩` from `exists_symbol ha (gK.restrictNormal Ω)`.

Take `⟨b1, b2⟩` from `a3 Ω j.toRingHom art (RingHom.ext j.commutes) ha g _ t hφ hχ (gK.restrictNormal_commutes Ω) ht ψ`. Conclude with `⟨_, b2, b1⟩`.
-/
theorem ratio_conj (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : ToricRatioConjugates)
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] [Nonempty I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (h1 : UnramFin E) (h2 : Module.finrank ℚ K = 2) (h3 : 0 < d) (h4 : δ ^ 2 = -(d : K))
    (h5 : IsCMType φ) (h6 : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (h7 : 1 ≤ s) (h8 : ∀ i, 1 ≤ κ i) (h9 : IsBaseCond 𝔣) (h10 : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h11 : IsValChar φ s κ 𝔣 ∅ χ)
    {T₀ : ℂ} {T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ} (hT₀ : IsToricSum φ s κ 𝔣 χ T₀)
    (hT : ∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) (g : ℂ ≃+* ℂ)
    (hφ : ∀ i x, g (φ i x) = φ i x) (hχ : ∀ y, g (lamF χ s y) = lamF χ s y) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) :
    ∃ ζ : ℂˣ, IsOfFinOrder ζ ∧ g (T ψ / T₀) = (ζ : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) := by
  obtain ⟨T₀', T', a1, -, a2, -, a3⟩ := hG E K d δ ι I φ s κ 𝔣 Q χ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain rfl : T₀' = T₀ := a1.unique hT₀
  obtain rfl : T' = T := funext fun ψ => (a2 ψ).unique (hT ψ)
  haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by
    have h := congrArg (InfinitePlace.embedding_of_isReal hw) h4
    rw [map_pow, map_neg, map_natCast] at h
    have : (0 : ℝ) < d := by exact_mod_cast h3
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw δ)]⟩
  let Ω := AlgebraicClosure K
  letI : Algebra K ℂ := ι.toAlgebra
  let j : Ω →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← h6 (Classical.arbitrary I)]
    exact hφ _ _
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨art, ha⟩ := hA K Ω
  obtain ⟨t, ht⟩ := exists_symbol ha (gK.restrictNormal Ω)
  obtain ⟨b1, b2⟩ := a3 Ω j.toRingHom art (RingHom.ext j.commutes) ha g _ t hφ hχ (gK.restrictNormal_commutes Ω) ht ψ
  exact ⟨_, b2, b1⟩

end GlobalTheory.ThmAMove
