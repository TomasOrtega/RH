import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

/- English proof (translation)
Set `R : Subring Ω` to `(Int.castRingHom Ω).range`. Establish `hI : Ideal.span {((p : ℕ) : R)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]`. Introduce and unpack `⟨⟨_, k, rfl⟩, hk⟩`. Establish `h1 : ((p : ℕ) : Ω) * ((k : ℤ) : Ω) = 1` using `congrArg Subtype.val hk`.

Establish `h2 : ((p : ℕ) : ℤ) * k = 1` using `by exact_mod_cast h1`. Establish `h3 : ((p : ℕ) : ℤ) = 1` using `Int.eq_one_of_mul_eq_one_right (by positivity) h2`. Conclude with `hp.one_lt.ne' (by exact_mod_cast h3)`. Take `⟨A, -, hA⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hI`. Conclude with `⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : R), Ideal.mem_span_singleton_self _, by simp⟩)⟩`.
-/
private theorem eisReg_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hI : Ideal.span {((p : ℕ) : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, k, rfl⟩, hk⟩
    have h1 : ((p : ℕ) : Ω) * ((k : ℤ) : Ω) = 1 := congrArg Subtype.val hk
    have h2 : ((p : ℕ) : ℤ) * k = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : R), Ideal.mem_span_singleton_self _, by simp⟩)⟩

/- English proof (translation)
Establish `e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly = (r : Matrix (Fin 2) (Fin 2) K).charpoly`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv]`. Conclude with `Matrix.charpoly_units_conj g _`. Rewrite using `[← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two, ← ha, ← hb]`.
-/
private theorem eisReg_charpoly {K : Type} [Field K] (g r : GL (Fin 2) K) (a b : K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0)
    (ha : (g * r * g⁻¹ : GL (Fin 2) K) 0 0 = a) (hb : (g * r * g⁻¹ : GL (Fin 2) K) 1 1 = b) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C a) * (X - C b) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two, ← ha, ← hb]

/- English proof (translation)
Introduce `l hl Ω _ _ _ ι φ θ k hk ρ hρ H hH`. Take `⟨A, hA⟩` from `eisReg_place (Ω := Ω) l hl.out`. Take `⟨κ, ⟨g, hg⟩, hκ, -⟩` from `hρ.above A hA`. Take `⟨u, hu⟩` from `GlobalTheory.CycDec.exists_unit_infinite_order l`. Take `⟨σ, hσ, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u`.

Use `haveI : IsGalois ℚ Ω := {}`. Use `haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH`. Use `haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Take `⟨n, hn, -, hnH⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero σ`. Establish `hs : σ ^ n ∈ Ine (F` using `ℚ) A := pow_mem hσ n`.

Set `s : ↥(Dec (F` to `ℚ) A) := ⟨σ ^ n, Ine_le_Dec A hs⟩`. Use `⟨σ ^ n, hnH, cycBar ℚ Ω l (σ ^ n) ^ ((k : ℤ) - 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isOfFinOrder_iff_pow_eq_one]`. Introduce and unpack `⟨m, hm, h⟩`. Establish `hinj : Function.Injective (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom)` using `Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)`.

Use `hu ((n : ℤ) * ((k : ℤ) - 1) * m) ?_ (hinj ?_)` and prove the remaining obligations. Establish `: (0 : ℤ) < (k : ℤ) - 1` using `by omega`. Check the signs of the components of the expression. Rewrite using `[map_one, ← h, cycBar, MonoidHom.comp_apply, map_pow, hσu, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, map_pow, map_zpow]`. Use `eisReg_charpoly g (ρ (σ ^ n)) _ _ (hg s).1 ?_ ?_` and prove the remaining obligations.

Rewrite using `[show ρ (σ ^ n) = ρ s from rfl, (hg s).2 0, hκ 0 s hs]`. Both sides reduce to the same expression. Rewrite using `[show ρ (σ ^ n) = ρ s from rfl, (hg s).2 1, hκ 1 s hs]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Sd.eisReg :
    UpperTheory.V.Sd.EisReg := by
  intro l hl Ω _ _ _ ι φ θ k hk ρ hρ H hH
  obtain ⟨A, hA⟩ := eisReg_place (Ω := Ω) l hl.out
  obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := hρ.above A hA
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  haveI : IsGalois ℚ Ω := {}
  haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hnH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero σ
  have hs : σ ^ n ∈ Ine (F := ℚ) A := pow_mem hσ n
  let s : ↥(Dec (F := ℚ) A) := ⟨σ ^ n, Ine_le_Dec A hs⟩
  refine ⟨σ ^ n, hnH, cycBar ℚ Ω l (σ ^ n) ^ ((k : ℤ) - 1), ?_, ?_⟩
  · rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨m, hm, h⟩
    have hinj : Function.Injective
        (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
      Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
    refine hu ((n : ℤ) * ((k : ℤ) - 1) * m) ?_ (hinj ?_)
    · have : (0 : ℤ) < (k : ℤ) - 1 := by omega
      positivity
    · rw [map_one, ← h, cycBar, MonoidHom.comp_apply, map_pow, hσu, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
        map_pow, map_zpow]
  · refine eisReg_charpoly g (ρ (σ ^ n)) _ _ (hg s).1 ?_ ?_
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 0, hκ 0 s hs]; rfl
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 1, hκ 1 s hs]; simp
