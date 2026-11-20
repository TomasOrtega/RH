import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FreeEtaleSheafZmodExistsHomSendingGenerator

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Establish `h2 : IsUnit (2 : ℤ_[l])`. Assume the negation of the conclusion as `hn`. Establish `hl : (l : ℤ) ∣ 2`. Rewrite `hn` using `[PadicInt.isUnit_iff]`. Establish `hlt : ‖((2 : ℤ) : ℤ_[l])‖ < 1` using `lt_of_le_of_ne (PadicInt.norm_le_one _) (by simpa using hn)`.

Conclude with `PadicInt.norm_int_lt_one_iff_dvd 2 |>.1 hlt`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] O)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`.

Establish `e` using `PadicInt.unitCoeff_spec hx0`. Rewrite `hx` using `[e, map_mul, map_pow, map_natCast]`. Break down `mul_eq_zero.1 hx with h1 | h1` into its components or cases. Conclude with `((Units.isUnit _).map (algebraMap ℤ_[l] O)).ne_zero h1`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1`.

Use `haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Conclude with `hn (isUnit_of_map_unit (algebraMap ℤ_[l] O) 2 (by rwa [map_ofNat]))`. Establish `h3 : ‖(2 : ℚ_[l])‖ = 1`. Use `PadicInt.isUnit_iff.1 h2` as an intermediate fact. Rewrite `this` using `[PadicInt.norm_def]`.

Conclude with `this` after adjusting the coercions. Rewrite using `[← map_ofNat (algebraMap ℚ_[l] (PadicAlgCl l)) 2, norm_algebraMap', h3]`.
-/
private theorem norm_two_eq_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (h : IsUnit (2 : O)) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hl : (l : ℤ) ∣ 2 := by
      rw [PadicInt.isUnit_iff] at hn
      have hlt : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) (by simpa using hn)
      exact PadicInt.norm_int_lt_one_iff_dvd 2 |>.1 hlt
    have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      have e := PadicInt.unitCoeff_spec hx0
      rw [e, map_mul, map_pow, map_natCast] at hx
      rcases mul_eq_zero.1 hx with h1 | h1
      · exact ((Units.isUnit _).map (algebraMap ℤ_[l] O)).ne_zero h1
      · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    exact hn (isUnit_of_map_unit (algebraMap ℤ_[l] O) 2 (by rwa [map_ofNat]))
  have h3 : ‖(2 : ℚ_[l])‖ = 1 := by
    have := PadicInt.isUnit_iff.1 h2
    rw [PadicInt.norm_def] at this
    exact_mod_cast this
  rw [← map_ofNat (algebraMap ℚ_[l] (PadicAlgCl l)) 2, norm_algebraMap', h3]

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr r' hr' hI hiso`. Take `⟨m, n, -, hz, hz1, -⟩` from `isCharZeroPt_basic F hF g₁ hg r hr`. Take `⟨m', n', -, hz', hz1', -⟩` from `isCharZeroPt_basic F hF g₁ hg r' hr'`. Use `conjBy_tor_of_iso F.η r r' F.c g₁ two_ne_zero m m' hF.ηc hg.1 n n' ?_ ?_ ?_ (Or.inl hI) hiso` and prove the remaining obligations. Rewrite using `[← norm_ne_zero_iff, hz1]`.

Conclude with `one_ne_zero`. Rewrite using `[← norm_ne_zero_iff, hz1']`. Conclude with `one_ne_zero`. Introduce `e`. Establish `h2` using `norm_two_eq_one (l := l) hF.two`.

Establish `hle` using `IsUltrametricDist.norm_add_le_max (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))) (-(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))))`. Rewrite `hle` using `[norm_neg]`. Establish `hlt` using `lt_of_le_of_lt hle (max_lt hz hz')`. Establish `e2 : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) + -(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))) = 2 * zeta F.c g₁ r`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hlt` using `[e2, norm_mul, h2, hz1, mul_one]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.conj_of_matIso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → ∀ r' : Γ →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r' → TypeI F.η r → MatIso F.η.ker (mats r) (mats r') → ∃ t, r' = conjBy (tor (PadicAlgCl l) t) r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr r' hr' hI hiso
  obtain ⟨m, n, -, hz, hz1, -⟩ := isCharZeroPt_basic F hF g₁ hg r hr
  obtain ⟨m', n', -, hz', hz1', -⟩ := isCharZeroPt_basic F hF g₁ hg r' hr'
  refine conjBy_tor_of_iso F.η r r' F.c g₁ two_ne_zero m m' hF.ηc hg.1 n n' ?_ ?_ ?_ (Or.inl hI) hiso
  · rw [← norm_ne_zero_iff, hz1]; exact one_ne_zero
  · rw [← norm_ne_zero_iff, hz1']; exact one_ne_zero
  · intro e
    have h2 := norm_two_eq_one (l := l) hF.two
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)))
      (-(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))))
    rw [norm_neg] at hle
    have hlt := lt_of_le_of_lt hle (max_lt hz hz')
    have e2 : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) +
        -(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))) = 2 * zeta F.c g₁ r := by
      rw [e]; ring
    rw [e2, norm_mul, h2, hz1, mul_one] at hlt
    exact lt_irrefl _ hlt
