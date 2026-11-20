import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `Ω _ _ _ H hH`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem`. Use `set U : Subgroup (G ℚ Ω) := N.toOpenSubgroup.toSubgroup with hUdef`. Use `haveI : U.Normal := N.isNormal'`. Establish `hUo : IsOpen (U : Set (G ℚ Ω))` using `N.isOpen'`.

Establish `hUH : U ≤ H` using `fun x hx => hN hx`. Introduce `hfin`. Use `set M : ℕ := ∏ q ∈ hfin.toFinset, q with hM`. Establish `hM0 : M ≠ 0`. Rewrite using `[hM, Finset.prod_ne_zero_iff]`.

Introduce `q hq`. Conclude with `((hfin.mem_toFinset.mp hq).1).ne_zero`. Take `⟨w, A, p, σ, -, hp, hpM, -, hpw, hnorm, -, hpl, hIne, hfr, hσ⟩` from `UpperTheory.V.Loc.v00 (F := ℚ) U hUo 1 ∅ M hM0`. Establish `hσU : σ ∈ U` using `by simpa using hσ`. Establish `hDecU : Dec (F` using `ℚ) A ≤ U := UpperTheory.V.Kum.decGen ℚ Ω A w σ U hpl (by rw [hnorm]; exact hfr) hUo hIne hσU`.

Establish `hAp : A.valuation (p : Ω) < 1`. Use `(hpl (p : 𝓞 ℚ)).mpr hpw` as an intermediate fact. Simplify using `using this`. Establish `hmem : p ∈ {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F` using `ℚ) A ≤ H} := by`. Use `⟨hp, fun A' hA' y hy => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, -⟩` from `((UpperTheory.V.Chr.placesQ Ω).2.2) p A' A hp hA' hAp`. Establish `h1 : u⁻¹ * y * u ∈ U` using `hDecU (hu y hy)`. Establish `h2 : y ∈ U`. Use `(inferInstance : U.Normal).conj_mem _ h1 u` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Conclude with `hUH h2`. Conclude with `hpM (hM ▸ Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hmem))`.
-/
theorem UpperTheory.V.Ws.Gys.splitPrimes :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
      Set.Infinite {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
  intro Ω _ _ _ H hH
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  set U : Subgroup (G ℚ Ω) := N.toOpenSubgroup.toSubgroup with hUdef
  haveI : U.Normal := N.isNormal'
  have hUo : IsOpen (U : Set (G ℚ Ω)) := N.isOpen'
  have hUH : U ≤ H := fun x hx => hN hx
  intro hfin
  set M : ℕ := ∏ q ∈ hfin.toFinset, q with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro q hq
    exact ((hfin.mem_toFinset.mp hq).1).ne_zero
  obtain ⟨w, A, p, σ, -, hp, hpM, -, hpw, hnorm, -, hpl, hIne, hfr, hσ⟩ :=
    UpperTheory.V.Loc.v00 (F := ℚ) U hUo 1 ∅ M hM0
  have hσU : σ ∈ U := by simpa using hσ
  have hDecU : Dec (F := ℚ) A ≤ U :=
    UpperTheory.V.Kum.decGen ℚ Ω A w σ U hpl (by rw [hnorm]; exact hfr) hUo hIne hσU
  have hAp : A.valuation (p : Ω) < 1 := by
    have := (hpl (p : 𝓞 ℚ)).mpr hpw
    simpa using this
  have hmem : p ∈ {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
    refine ⟨hp, fun A' hA' y hy => ?_⟩
    obtain ⟨u, hu, -⟩ := ((UpperTheory.V.Chr.placesQ Ω).2.2) p A' A hp hA' hAp
    have h1 : u⁻¹ * y * u ∈ U := hDecU (hu y hy)
    have h2 : y ∈ U := by
      have := (inferInstance : U.Normal).conj_mem _ h1 u
      simpa [mul_assoc] using this
    exact hUH h2
  exact hpM (hM ▸ Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hmem))
