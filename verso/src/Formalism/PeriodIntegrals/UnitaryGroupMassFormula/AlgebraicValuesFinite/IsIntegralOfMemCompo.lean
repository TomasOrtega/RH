import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

def compo (L : Type) [Field L] [NumberField L] : IntermediateField ℚ ℂ :=
  ⨆ φ : L →+* ℂ, φ.toRatAlgHom.fieldRange

instance (φ : L →+* ℂ) : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange :=
  LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv

instance : FiniteDimensional ℚ (compo L) := by
  unfold compo; infer_instance

/- English proof (translation)
The claim follows from `(le_iSup (fun ψ : L →+* ℂ => ψ.toRatAlgHom.fieldRange) φ) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)`.
-/
theorem mem_compo (φ : L →+* ℂ) (x : L) : φ x ∈ compo L :=
  (le_iSup (fun ψ : L →+* ℂ => ψ.toRatAlgHom.fieldRange) φ) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)

/- English proof (translation)
The claim follows from `prod_mem fun φ _ => zpow_mem (mem_compo φ k) _`.
-/
theorem prod_mem_compo (m : (L →+* ℂ) → ℤ) (k : L) : ∏ φ : L →+* ℂ, φ k ^ m φ ∈ compo L :=
  prod_mem fun φ _ => zpow_mem (mem_compo φ k) _

/- English proof (translation)
Establish `h` using `(IsIntegral.of_finite ℚ (⟨y, hy⟩ : compo L)).map (compo L).val`. Conclude with `h`.
-/
theorem isIntegral_of_mem_compo {y : ℂ} (hy : y ∈ compo L) : IsIntegral ℚ y := by
  have h := (IsIntegral.of_finite ℚ (⟨y, hy⟩ : compo L)).map (compo L).val
  exact h

/- English proof (translation)
Establish `hb : b ≠ 0` using `by rintro rfl; simp at e`. Establish `hP : P ≠ 0` using `by rintro rfl; simp at e`. Establish `hz : z ≠ 0` using `by rintro rfl; simp at e`. Clear the denominators using the available nonvanishing facts. Clear denominators, using `at e` for the nonvanishing conditions.

Take the linear combination `e`.
-/
theorem eq_of_key {a b P z : ℂ} (e : a * b⁻¹ * P * z = 1) : a = b * (P * z)⁻¹ := by
  have hb : b ≠ 0 := by rintro rfl; simp at e
  have hP : P ≠ 0 := by rintro rfl; simp at e
  have hz : z ≠ 0 := by rintro rfl; simp at e
  field_simp
  field_simp at e
  linear_combination e

/- English proof (translation)
Introduce `hTors hKey hPow hSame χ s m hm`. Take `⟨N, hN0, hN⟩` from `hTors χ`. Take `⟨h, hh0, hk⟩` from `hPow`. Take `⟨ι, hι, c, hc⟩` from `hSame`. Use `haveI := hι`.

Establish `hz : ∀ r ∈ UFin L, ((χ.1 r : ℂˣ) : ℂ) ^ N = 1`. Introduce `r hr`. Rewrite using `[← Units.val_pow_eq_pow_val, hN r hr, Units.val_one]`. Set `U` to `{i : ι // ∃ v, c v = i ∧ χ.UnrAt v}`. Set `f : U → ℂ` to `fun i => χ.valTw s i.2.choose`.

Set `S : Set ℂ` to `((Polynomial.nthRoots N (1 : ℂ)).toFinset : Set ℂ) ∪ Set.range f`. Use `haveI : Finite S := ((Set.toFinite _).union (Set.finite_range f)).to_subtype`. Establish `hA : ∀ v, χ.UnrAt v → ∃ P ∈ compo L, ∃ z : ℂ, z ^ N = 1 ∧ χ.valTw s v ^ h * (P * z) = 1`. Introduce `v hv`. Take `⟨kv, hkv⟩` from `hk v`.

Establish `h1 : ∀ u, u ∉ ({v} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u kv = 0`. Introduce `u hu`. Rewrite using `[hkv u, if_neg (fun h' => hu (Finset.mem_singleton.mpr h'))]`. Establish `h2 : ∀ u ∈ ({v} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u`. Introduce `u hu`.

Rewrite using `[Finset.mem_singleton.mp hu]`. Conclude with `hv`. Take `⟨r, hr, e⟩` from `hKey χ s m hm kv {v} h1 h2`. Use `⟨_, prod_mem_compo m (kv : L), _, hz r hr, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[Finset.prod_singleton, hkv v, if_pos rfl, zpow_natCast]`.

Rewrite using `[← mul_assoc]`. Conclude with `e`. Set `C : IntermediateField ℚ ℂ` to `compo L ⊔ IntermediateField.adjoin ℚ S`. Establish `hCcompo : compo L ≤ C` using `le_sup_left`. Establish `hSsub : ∀ x ∈ S, x ∈ C` using `fun x hx => (le_sup_right : IntermediateField.adjoin ℚ S ≤ C) (IntermediateField.subset_adjoin ℚ S hx)`.

Establish `hmu : ∀ z : ℂ, z ^ N = 1 → z ∈ C` using `fun z hz' => hSsub z (Or.inl (by simp [Polynomial.mem_nthRoots hN0, hz']))`. Establish `hf : ∀ i : U, f i ∈ C` using `fun i => hSsub _ (Or.inr ⟨i, rfl⟩)`. Establish `hval : ∀ v, χ.UnrAt v → χ.valTw s v ∈ C`. Introduce `v hv`. Establish `hex : ∃ v', c v' = c v ∧ χ.UnrAt v'` using `⟨v, rfl, hv⟩`.

Establish `hw` using `hex.choose_spec`. Establish `hwC : χ.valTw s hex.choose ∈ C` using `hf ⟨c v, hex⟩`. Distinguish the cases in `hvw : v = hex.choose`. Rewrite using `[hvw]`. Conclude with `hwC`.

Take `⟨k, hkk⟩` from `hc v hex.choose hw.1.symm`. Establish `h1 : ∀ u, u ∉ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u k = 0`. Introduce `u hu`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu`. Rewrite using `[hkk u, if_neg hu.1, if_neg hu.2, sub_zero]`.

Establish `h2 : ∀ u ∈ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u`. Introduce `u hu`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hu`. Break down `hu with rfl | rfl` into its components or cases. Conclude with `hv`.

Conclude with `hw.2`. Take `⟨r, hr, e⟩` from `hKey χ s m hm k {v, hex.choose} h1 h2`. Establish `o1 : ordF v k = 1` using `by rw [hkk]; simp [hvw]`. Establish `o2 : ordF hex.choose k = -1` using `by rw [hkk]; simp [Ne.symm hvw]`. Rewrite `e` using `[Finset.prod_pair hvw, o1, o2, zpow_one, zpow_neg_one]`.

Rewrite using `[eq_of_key e]`. Conclude with `C.mul_mem hwC (C.inv_mem (C.mul_mem (hCcompo (prod_mem_compo m (k : L))) (hmu _ (hz r hr))))`. Establish `hint : ∀ x ∈ S, IsIntegral ℚ x`. Introduce `x hx`. Break down `hx with hx | ⟨i, rfl⟩` into its components or cases.

Establish `hx' : x ^ N = 1` using `by simpa [Polynomial.mem_nthRoots hN0] using hx`. Conclude with `IsIntegral.of_pow hN0 (by rw [hx']; exact isIntegral_one)`. Take `⟨P, hP, z, hzN, e⟩` from `hA _ i.2.choose_spec.2`. Establish `hpow : (f i) ^ (h * N) ∈ compo L`. Establish `e1 : (f i) ^ h = (P * z)⁻¹` using `eq_inv_of_mul_eq_one_left e`.

Rewrite using `[pow_mul, e1, inv_pow, mul_pow, hzN, mul_one]`. Conclude with `inv_mem (pow_mem hP N)`. Conclude with `IsIntegral.of_pow (Nat.mul_pos hh0 hN0) (isIntegral_of_mem_compo hpow)`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hint`. Use `haveI hC : FiniteDimensional ℚ C := IntermediateField.finiteDimensional_sup _ _`.

Use `⟨C.toSubfield, ?_, fun v hv => ⟨⟨χ.valTw s v, hval v hv⟩, rfl⟩⟩` and prove the remaining obligations. Set `e : C ≃ₗ[ℚ] C.toSubfield` to `{ toFun := fun x => ⟨x.1, x.2⟩ invFun := fun x => ⟨x.1, x.2⟩ map_add' := fun x y => rfl map_smul' := fun q x => rfl left_inv := fun x => rfl right_inv := fun x => rfl }`. Conclude with `LinearEquiv.finiteDimensional e`.
-/
theorem assemble : Assemble L := by
  classical
  intro hTors hKey hPow hSame χ s m hm
  obtain ⟨N, hN0, hN⟩ := hTors χ
  obtain ⟨h, hh0, hk⟩ := hPow
  obtain ⟨ι, hι, c, hc⟩ := hSame
  haveI := hι
  have hz : ∀ r ∈ UFin L, ((χ.1 r : ℂˣ) : ℂ) ^ N = 1 := by
    intro r hr
    rw [← Units.val_pow_eq_pow_val, hN r hr, Units.val_one]
  let U := {i : ι // ∃ v, c v = i ∧ χ.UnrAt v}
  let f : U → ℂ := fun i => χ.valTw s i.2.choose
  let S : Set ℂ := ((Polynomial.nthRoots N (1 : ℂ)).toFinset : Set ℂ) ∪ Set.range f
  haveI : Finite S := ((Set.toFinite _).union (Set.finite_range f)).to_subtype
  have hA : ∀ v, χ.UnrAt v → ∃ P ∈ compo L, ∃ z : ℂ, z ^ N = 1 ∧ χ.valTw s v ^ h * (P * z) = 1 := by
    intro v hv
    obtain ⟨kv, hkv⟩ := hk v
    have h1 : ∀ u, u ∉ ({v} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u kv = 0 := by
      intro u hu
      rw [hkv u, if_neg (fun h' => hu (Finset.mem_singleton.mpr h'))]
    have h2 : ∀ u ∈ ({v} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
      intro u hu
      rw [Finset.mem_singleton.mp hu]
      exact hv
    obtain ⟨r, hr, e⟩ := hKey χ s m hm kv {v} h1 h2
    refine ⟨_, prod_mem_compo m (kv : L), _, hz r hr, ?_⟩
    rw [Finset.prod_singleton, hkv v, if_pos rfl, zpow_natCast] at e
    rw [← mul_assoc]
    exact e
  let C : IntermediateField ℚ ℂ := compo L ⊔ IntermediateField.adjoin ℚ S
  have hCcompo : compo L ≤ C := le_sup_left
  have hSsub : ∀ x ∈ S, x ∈ C := fun x hx => (le_sup_right : IntermediateField.adjoin ℚ S ≤ C)
    (IntermediateField.subset_adjoin ℚ S hx)
  have hmu : ∀ z : ℂ, z ^ N = 1 → z ∈ C := fun z hz' =>
    hSsub z (Or.inl (by simp [Polynomial.mem_nthRoots hN0, hz']))
  have hf : ∀ i : U, f i ∈ C := fun i => hSsub _ (Or.inr ⟨i, rfl⟩)
  have hval : ∀ v, χ.UnrAt v → χ.valTw s v ∈ C := by
    intro v hv
    have hex : ∃ v', c v' = c v ∧ χ.UnrAt v' := ⟨v, rfl, hv⟩
    have hw := hex.choose_spec
    have hwC : χ.valTw s hex.choose ∈ C := hf ⟨c v, hex⟩
    by_cases hvw : v = hex.choose
    · rw [hvw]
      exact hwC
    · obtain ⟨k, hkk⟩ := hc v hex.choose hw.1.symm
      have h1 : ∀ u, u ∉ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u k = 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
        rw [hkk u, if_neg hu.1, if_neg hu.2, sub_zero]
      have h2 : ∀ u ∈ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hv
        · exact hw.2
      obtain ⟨r, hr, e⟩ := hKey χ s m hm k {v, hex.choose} h1 h2
      have o1 : ordF v k = 1 := by rw [hkk]; simp [hvw]
      have o2 : ordF hex.choose k = -1 := by rw [hkk]; simp [Ne.symm hvw]
      rw [Finset.prod_pair hvw, o1, o2, zpow_one, zpow_neg_one] at e
      rw [eq_of_key e]
      exact C.mul_mem hwC (C.inv_mem (C.mul_mem (hCcompo (prod_mem_compo m (k : L))) (hmu _ (hz r hr))))
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · have hx' : x ^ N = 1 := by simpa [Polynomial.mem_nthRoots hN0] using hx
      exact IsIntegral.of_pow hN0 (by rw [hx']; exact isIntegral_one)
    · obtain ⟨P, hP, z, hzN, e⟩ := hA _ i.2.choose_spec.2
      have hpow : (f i) ^ (h * N) ∈ compo L := by
        have e1 : (f i) ^ h = (P * z)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [pow_mul, e1, inv_pow, mul_pow, hzN, mul_one]
        exact inv_mem (pow_mem hP N)
      exact IsIntegral.of_pow (Nat.mul_pos hh0 hN0) (isIntegral_of_mem_compo hpow)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  haveI hC : FiniteDimensional ℚ C := IntermediateField.finiteDimensional_sup _ _
  refine ⟨C.toSubfield, ?_, fun v hv => ⟨⟨χ.valTw s v, hval v hv⟩, rfl⟩⟩
  let e : C ≃ₗ[ℚ] C.toSubfield :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun q x => rfl
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  exact LinearEquiv.finiteDimensional e

end PI.AlgValsFin.W
