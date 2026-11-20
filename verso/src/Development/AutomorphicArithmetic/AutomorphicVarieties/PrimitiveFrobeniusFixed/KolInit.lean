import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ M F r a _ _ hM hr hrF ζ hζ δ hδ y hy0 hyfix κ hκ A₀ hA₀ k hk ρ hρ t ht htρ c σ hσ`. Establish `pb` using `placeBasic Ω`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hM0 : M ≠ 0` using `NeZero.ne M`. Establish `hr0 : (r : Ω) ≠ 0` using `by exact_mod_cast hr.ne_zero`.

Establish `hρ0 : ρ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hρ` using `[zero_pow hM0]`. Conclude with `hr0 hρ.symm`. Establish `hFr : F.Coprime r` using `hrF.symm`.

Establish `hMr : M.Coprime r` using `(hrF.coprime_dvd_right hM).symm`. Establish `hnotF : ¬ Over A₀ F` using `fun h => pb.2.2.2.1 A₀ F r hFr h hA₀`. Establish `hnotM : ¬ Over A₀ M` using `fun h => pb.2.2.2.1 A₀ M r hMr h hA₀`. Establish `hIneF : Ine (F` using `ℚ) A₀ ≤ fixMu ℚ Ω F := pb.2.2.2.2.1 A₀ F hnotF`. Establish `hconj : ∀ (h τ : G ℚ Ω), h ∈ fixMu ℚ Ω F → τ⁻¹ * h * τ ∈ fixMu ℚ Ω F`.

Introduce `h τ hh x hx`. Establish `h1 : h (τ x) = τ x` using `hh _ (by rw [← map_pow, hx, map_one])`. Simplify using `[AlgEquiv.mul_apply, h1]`. Establish `htF : t ∈ fixMu ℚ Ω F` using `hIneF ht`. Establish `hg : σ⁻¹ * t * σ ∈ fixMu ℚ Ω F` using `hconj t σ htF`.

Take `⟨Y, hYM, hK⟩` from `hκ`. Take `⟨z, -, hzM, hζκ⟩` from `hK _ hg`. Rewrite `hzM` using `[hyfix _ hg, div_self hy0]`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hzM` using `[zero_pow hM0]`. Conclude with `zero_ne_one hzM`. Establish `hPz : opP δ a z = 1`. Unfold `opP`. Rewrite using `[hδ z hzM, div_self (pow_ne_zero _ hz0)]`.

Rewrite `hζκ` using `[hPz, div_one]`. Establish `hY0 : Y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hYM` using `[zero_pow hM0]`. Conclude with `hy0 hYM.symm`.

Use `set w := opP δ a Y with hw`. Establish `hw0 : w ≠ 0`. Rewrite using `[hw]`. Unfold `opP`. Conclude with `div_ne_zero (by simpa using hY0) (pow_ne_zero _ hY0)`.

Establish `hζF : ζ ^ F = 1` using `(hζ.pow_eq_one_iff_dvd F).mpr hM`. Establish `hσζ : σ ζ = ζ ^ (c : ZMod F).val` using `hσ ζ hζF`. Establish `h1 : ζ ^ ((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val) = t (σ w) / σ w`. Rewrite using `[pow_mul, ← hσζ, ← map_pow, hζκ, map_div₀]`. Use `congr 1`.

Simplify using `[AlgEquiv.mul_apply]`. Use `set W := σ w with hW`. Establish `hW0 : W ≠ 0` using `by simpa [hW] using hw0`. Establish `hWM : W ^ M = σ (opP δ a y)`. Rewrite using `[hW, ← map_pow, hw]`.

Unfold `opP`. Rewrite using `[div_pow, ← map_pow, ← pow_mul, mul_comm a M, pow_mul, hYM]`. Establish `hPfix : ∀ h ∈ fixMu ℚ Ω F, h (opP δ a y) = opP δ a y`. Introduce `h hh`. Unfold `opP`.

Rewrite using `[map_div₀, map_pow, hyfix h hh]`. Use `congr 1`. Establish `h2` using `congrArg δ (hyfix _ (hconj h δ hh))`. Simplify `h2` using `[AlgEquiv.mul_apply]`. Establish `hXt : t (σ (opP δ a y)) = σ (opP δ a y)`.

Establish `h2` using `congrArg σ (hPfix _ hg)`. Simplify `h2` using `[AlgEquiv.mul_apply]`. Use `set e := W / ρ ^ (k c) with he`. Establish `heM : e ^ M = σ (opP δ a y) / (r : Ω) ^ (k c)`. Rewrite using `[he, div_pow, hWM, ← zpow_natCast (ρ ^ k c) M, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]`.

Establish `hvr0 : A₀.valuation (r : Ω) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hr0`. Establish `hveM : A₀.valuation e ^ M = 1`. Rewrite using `[← map_pow, heM, map_div₀, map_zpow₀, hk c σ hσ, div_self (zpow_ne_zero _ hvr0)]`. Establish `hve : A₀.valuation e = 1`. Break down `lt_trichotomy (A₀.valuation e) 1 with hlt | heq | hgt` into its components or cases.

Conclude with `absurd hveM (ne_of_lt (pow_lt_one₀ zero_le' hlt hM0))`. Conclude with `heq`. Conclude with `absurd hveM (ne_of_gt (one_lt_pow₀ hgt hM0))`. Establish `he0 : e ≠ 0`. Introduce and unpack `h0`.

Rewrite `hve` using `[h0, map_zero]`. Conclude with `zero_ne_one hve`. Establish `hteM : (t e / e) ^ M = 1`. Establish `hX0 : σ (opP δ a y) / (r : Ω) ^ (k c) ≠ 0`. Rewrite using `[← heM]`.

Conclude with `pow_ne_zero M he0`. Rewrite using `[div_pow, ← map_pow, heM, map_div₀, hXt, map_zpow₀, map_natCast]`. Conclude with `div_self hX0`. Establish `hin : A₀.valuation (t e - e) < 1` using `ht.2 e hve.le`. Establish `hte1 : A₀.valuation (t e / e - 1) < 1`.

Rewrite using `[div_sub_one he0, map_div₀, hve, div_one]`. Conclude with `hin`. Establish `hte : t e = e`. Establish `h3` using `pb.2.2.2.2.2.1 A₀ M (t e / e) hnotM hteM hte1`. Rewrite `h3` using `[div_eq_one_iff_eq he0]`. Then use the resulting hypothesis.

Establish `hWe : W = e * ρ ^ (k c)`. Rewrite using `[he, div_mul_cancel₀ _ (zpow_ne_zero _ hρ0)]`. Establish `htW : t W / W = ζ ^ (k c)`. Rewrite using `[div_eq_iff hW0]`. Use `conv_lhs => rw [hWe]`.

Rewrite using `[map_mul, map_zpow₀, hte, htρ, mul_zpow, hWe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[htW, ← zpow_natCast]`. Establish `hdvd : (M : ℤ) ∣ (k c) - (((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val : ℕ) : ℤ)`. Rewrite using `[← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hM0), ← h1, div_self (zpow_ne_zero _ (hζ.ne_zero hM0))]`.

Establish `h4` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mpr hdvd`. Move the coercions through the operations in `at h4`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ← h4, ZMod.natCast_zmod_val, mul_comm]`.
-/
theorem UpperTheory.V.ML.kolInit :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F r a : ℕ) [NeZero M] [NeZero F] (hM : M ∣ F), r.Prime → r.Coprime F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω F, h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F 1 ζ δ a y κ → ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ k : (ZMod F)ˣ → ℤ, HasOrd F r A₀ (opP δ a y) k →
    ∀ ρ : Ω, ρ ^ M = (r : Ω) → ∀ t ∈ Ine (F := ℚ) A₀, t ρ = ζ * ρ → ∀ (c : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F c σ →
    κ (σ⁻¹ * t * σ) * ZMod.castHom hM (ZMod M) (c : ZMod F) = (k c : ZMod M) := by
  intro Ω _ _ _ M F r a _ _ hM hr hrF ζ hζ δ hδ y hy0 hyfix κ hκ A₀ hA₀ k hk ρ hρ t ht htρ c σ hσ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hM0 : M ≠ 0 := NeZero.ne M
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hFr : F.Coprime r := hrF.symm
  have hMr : M.Coprime r := (hrF.coprime_dvd_right hM).symm
  have hnotF : ¬ Over A₀ F := fun h => pb.2.2.2.1 A₀ F r hFr h hA₀
  have hnotM : ¬ Over A₀ M := fun h => pb.2.2.2.1 A₀ M r hMr h hA₀
  have hIneF : Ine (F := ℚ) A₀ ≤ fixMu ℚ Ω F := pb.2.2.2.2.1 A₀ F hnotF
  have hconj : ∀ (h τ : G ℚ Ω), h ∈ fixMu ℚ Ω F → τ⁻¹ * h * τ ∈ fixMu ℚ Ω F := by
    intro h τ hh x hx
    have h1 : h (τ x) = τ x := hh _ (by rw [← map_pow, hx, map_one])
    simp [AlgEquiv.mul_apply, h1]
  have htF : t ∈ fixMu ℚ Ω F := hIneF ht
  have hg : σ⁻¹ * t * σ ∈ fixMu ℚ Ω F := hconj t σ htF
  obtain ⟨Y, hYM, hK⟩ := hκ
  obtain ⟨z, -, hzM, hζκ⟩ := hK _ hg
  rw [hyfix _ hg, div_self hy0] at hzM
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hzM
    exact zero_ne_one hzM
  have hPz : opP δ a z = 1 := by
    unfold opP
    rw [hδ z hzM, div_self (pow_ne_zero _ hz0)]
  rw [hPz, div_one] at hζκ
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hYM
    exact hy0 hYM.symm
  set w := opP δ a Y with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    unfold opP
    exact div_ne_zero (by simpa using hY0) (pow_ne_zero _ hY0)
  have hζF : ζ ^ F = 1 := (hζ.pow_eq_one_iff_dvd F).mpr hM
  have hσζ : σ ζ = ζ ^ (c : ZMod F).val := hσ ζ hζF
  have h1 : ζ ^ ((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val) = t (σ w) / σ w := by
    rw [pow_mul, ← hσζ, ← map_pow, hζκ, map_div₀]
    congr 1
    simp [AlgEquiv.mul_apply]
  set W := σ w with hW
  have hW0 : W ≠ 0 := by simpa [hW] using hw0
  have hWM : W ^ M = σ (opP δ a y) := by
    rw [hW, ← map_pow, hw]
    unfold opP
    rw [div_pow, ← map_pow, ← pow_mul, mul_comm a M, pow_mul, hYM]
  have hPfix : ∀ h ∈ fixMu ℚ Ω F, h (opP δ a y) = opP δ a y := by
    intro h hh
    unfold opP
    rw [map_div₀, map_pow, hyfix h hh]
    congr 1
    have h2 := congrArg δ (hyfix _ (hconj h δ hh))
    simpa [AlgEquiv.mul_apply] using h2
  have hXt : t (σ (opP δ a y)) = σ (opP δ a y) := by
    have h2 := congrArg σ (hPfix _ hg)
    simpa [AlgEquiv.mul_apply] using h2
  set e := W / ρ ^ (k c) with he
  have heM : e ^ M = σ (opP δ a y) / (r : Ω) ^ (k c) := by
    rw [he, div_pow, hWM, ← zpow_natCast (ρ ^ k c) M, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]
  have hvr0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have hveM : A₀.valuation e ^ M = 1 := by
    rw [← map_pow, heM, map_div₀, map_zpow₀, hk c σ hσ, div_self (zpow_ne_zero _ hvr0)]
  have hve : A₀.valuation e = 1 := by
    rcases lt_trichotomy (A₀.valuation e) 1 with hlt | heq | hgt
    · exact absurd hveM (ne_of_lt (pow_lt_one₀ zero_le' hlt hM0))
    · exact heq
    · exact absurd hveM (ne_of_gt (one_lt_pow₀ hgt hM0))
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hve
    exact zero_ne_one hve
  have hteM : (t e / e) ^ M = 1 := by
    have hX0 : σ (opP δ a y) / (r : Ω) ^ (k c) ≠ 0 := by
      rw [← heM]
      exact pow_ne_zero M he0
    rw [div_pow, ← map_pow, heM, map_div₀, hXt, map_zpow₀, map_natCast]
    exact div_self hX0
  have hin : A₀.valuation (t e - e) < 1 := ht.2 e hve.le
  have hte1 : A₀.valuation (t e / e - 1) < 1 := by
    rw [div_sub_one he0, map_div₀, hve, div_one]
    exact hin
  have hte : t e = e := by
    have h3 := pb.2.2.2.2.2.1 A₀ M (t e / e) hnotM hteM hte1
    rwa [div_eq_one_iff_eq he0] at h3
  have hWe : W = e * ρ ^ (k c) := by
    rw [he, div_mul_cancel₀ _ (zpow_ne_zero _ hρ0)]
  have htW : t W / W = ζ ^ (k c) := by
    rw [div_eq_iff hW0]
    conv_lhs => rw [hWe]
    rw [map_mul, map_zpow₀, hte, htρ, mul_zpow, hWe]
    ring
  rw [htW, ← zpow_natCast] at h1
  have hdvd : (M : ℤ) ∣ (k c) - (((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val : ℕ) : ℤ) := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hM0), ← h1, div_self (zpow_ne_zero _ (hζ.ne_zero hM0))]
  have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mpr hdvd
  push_cast at h4
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← h4, ZMod.natCast_zmod_val, mul_comm]
