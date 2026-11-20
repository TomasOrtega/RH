import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Introduce `k hk` and use `by have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib] exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm`.
-/
private theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

/- English proof (translation)
Use `Subtype.ext (MonoidHom.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1`. Rewrite using `[← map_pow, Int.units_sq, map_one]`.
-/
private theorem quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

/- English proof (translation)
Rewrite using `[← v.mk_embedding, ← v'.mk_embedding]`. Use `congr 1`. Use extensionality with `x`. Take `⟨q, rfl⟩` from `h x`. Simplify using the standard rewrite rules.
-/
private theorem place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

/- English proof (translation)
Take `⟨v₀⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h2 : χ.locInf v₀ (-1) ^ 2 = 1` using `by rw [← map_pow, neg_one_sq, map_one]`. Establish `h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1` using `by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]`. Break down `sq_eq_one_iff.1 h3 with e | e` into its components or cases. Conclude with `⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩`.

Conclude with `⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩`.
-/
private theorem exists_sign {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) : ∃ m : ℕ, ∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩
  · exact ⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩

/- English proof (translation)
Introduce `E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n`. Take `⟨m, hm⟩` from `exists_sign (surjective_algebraMap_real E hE) χ`. Establish `ho : (quadChar E ^ (m + n)).OrderDvd 2`. Use `quadChar_order E` as an intermediate fact. Unfold `HChar.OrderDvd at this ⊢`.

Rewrite using `[← pow_mul, mul_comm, pow_mul, this, one_pow]`. Establish `hη` using `isAlgPos_zero_of_orderDvd two_pos ho`. Take `⟨δ, hδc, hδ⟩` from `ha.exists_isLAdicOf ι hη`. Establish `h0 : (1 : HChar E).IsAbsPow 0` using `⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc], fun k => by simp [HChar.inf]⟩`. Establish `h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹`.

Rewrite using `[map_one, one_mul, eq_comm, inv_eq_one]`. Conclude with `Subtype.ext (MonoidHom.ext fun x => inv_one)`. Establish `hres` using `GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)`. Use `⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]`.

Rewrite using `[MonoidHom.mul_comp, hres, zpow_zero, mul_one]`. Rewrite using `[HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.heckeChar_sign_fixed :
    UpperTheory.V.Af.Bc.SignFix := by
  intro E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n
  obtain ⟨m, hm⟩ := exists_sign (surjective_algebraMap_real E hE) χ
  have ho : (quadChar E ^ (m + n)).OrderDvd 2 := by
    have := quadChar_order E
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hη := isAlgPos_zero_of_orderDvd two_pos ho
  obtain ⟨δ, hδc, hδ⟩ := ha.exists_isLAdicOf ι hη
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  have h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹ := by
    rw [map_one, one_mul, eq_comm, inv_eq_one]
    exact Subtype.ext (MonoidHom.ext fun x => inv_one)
  have hres := GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)
  refine ⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  · rw [MonoidHom.mul_comp, hres, zpow_zero, mul_one]
  · rw [HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
