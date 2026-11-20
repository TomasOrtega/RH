import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `k hk` and use `by have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib] exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm`.
-/
private theorem sf_isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

/- English proof (translation)
Use `Subtype.ext (MonoidHom.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1`. Rewrite using `[← map_pow, Int.units_sq, map_one]`.
-/
private theorem sf_quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

/- English proof (translation)
Use extensionality with `x`. Take `⟨q, rfl⟩` from `h x`. Simplify using the standard rewrite rules.
-/
private theorem sf_emb_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (φ φ' : F →+* ℂ) : φ = φ' := by
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

/- English proof (translation)
Rewrite using `[← v.mk_embedding, ← v'.mk_embedding, sf_emb_eq h v.embedding v'.embedding]`.
-/
private theorem sf_place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding, sf_emb_eq h v.embedding v'.embedding]

/- English proof (translation)
Establish `e : atInf v (-1) = -1` using `Units.ext (by simp [atInf])`. Unfold `HChar.inf HChar.locInf infDiag`. Rewrite using `[Finset.prod_eq_single v (fun w _ hw => absurd (sf_place_eq h w v) hw) (fun hv => absurd (Finset.mem_univ v) hv)]`. Simplify using `only [MonoidHom.comp_apply, e]`.
-/
private theorem sf_inf_neg_one {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) (v : InfinitePlace F) : χ.inf (-1) = χ.locInf v (-1) := by
  have e : atInf v (-1) = -1 := Units.ext (by simp [atInf])
  unfold HChar.inf HChar.locInf infDiag
  rw [Finset.prod_eq_single v (fun w _ hw => absurd (sf_place_eq h w v) hw) (fun hv => absurd (Finset.mem_univ v) hv)]
  simp only [MonoidHom.comp_apply, e]

/- English proof (translation)
Use `haveI : Unique (F →+* ℂ) := ⟨⟨φ₀⟩, fun w => sf_emb_eq h w φ₀⟩`. Introduce `k`. Take `⟨q, hq⟩` from `h (k : F)`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Conclude with `k.ne_zero (by rw [← hq, map_zero])`. Break down `lt_or_gt_of_ne hq0 with hneg | hpos` into its components or cases. Establish `h1` using `hχ (-k) (fun φ => by`. Rewrite using `[Units.val_neg, ← hq, map_neg]`. Simplify using `using hneg)`.

Establish `e : k = (-1) * (-k)` using `by simp`. Rewrite `h1`, the goal using `[Fintype.prod_unique]`. Use `conv_lhs => rw [e, map_mul, Units.val_mul, hs, h1]`. Rewrite using `[← mul_zpow]`. Simplify using the standard rewrite rules.

Conclude with `hχ k (fun φ => by`. Rewrite using `[← hq]`. Simplify using `using hpos)`.
-/
private theorem sf_isAlg {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) (b : ℤ) (hχ : IsAlgPos χ (fun _ => b)) (φ₀ : F →+* ℂ) (hs : ((χ.inf (-1) : ℂˣ) : ℂ) = (-1) ^ b) :
    χ.IsAlg (fun _ => b) := by
  haveI : Unique (F →+* ℂ) := ⟨⟨φ₀⟩, fun w => sf_emb_eq h w φ₀⟩
  intro k
  obtain ⟨q, hq⟩ := h (k : F)
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hq, map_zero])
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · have h1 := hχ (-k) (fun φ => by
      rw [Units.val_neg, ← hq, map_neg]
      simpa using hneg)
    have e : k = (-1) * (-k) := by simp
    rw [Fintype.prod_unique] at h1 ⊢
    conv_lhs => rw [e, map_mul, Units.val_mul, hs, h1]
    rw [← mul_zpow]
    simp
  · exact hχ k (fun φ => by
      rw [← hq]
      simpa using hpos)

/- English proof (translation)
Introduce `E _ _ _ hE ψ a ha`. Establish `h` using `surjective_algebraMap_real E hE`. Take `⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield E))` from `inferInstance`. Establish `ea : a = fun _ => a v.embedding` using `funext fun φ => by rw [sf_emb_eq h φ v.embedding]`. Use `set b := a v.embedding with hb`.

Establish `hpos : ∀ k : ℕ, IsAlgPos (ψ * quadChar E ^ k) (fun _ => b)` using `fun k => by`. Establish `ho : (quadChar E ^ k).OrderDvd 2`. Use `sf_quadChar_order E` as an intermediate fact. Unfold `HChar.OrderDvd at this ⊢`. Rewrite using `[← pow_mul, mul_comm, pow_mul, this, one_pow]`.

Use `sf_isAlgPos_mul ha (isAlgPos_zero_of_orderDvd two_pos ho)` as an intermediate fact. Rewrite `this` using `[add_zero, ea]`. Then use the resulting hypothesis. Establish `hval : ∀ k : ℕ, (((ψ * quadChar E ^ k).inf (-1) : ℂˣ) : ℂ) = (ψ.locInf v (-1) : ℂˣ) * (-1) ^ k` using `fun k => by`. Rewrite using `[sf_inf_neg_one h _ v, HChar.locInf_mul, locInf_pow, quadChar_locInf]`. Simplify using the standard rewrite rules.

Establish `h2 : ψ.locInf v (-1) ^ 2 = 1` using `by rw [← map_pow, neg_one_sq, map_one]`. Establish `h3 : ((ψ.locInf v (-1) : ℂˣ) : ℂ) ^ 2 = 1` using `by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]`. Apply the tactic sequence `rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb'`. Conclude with `⟨0, b, sf_isAlg h _ b (hpos 0) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩`. Conclude with `⟨1, b, sf_isAlg h _ b (hpos 1) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩`.

Conclude with `⟨1, b, sf_isAlg h _ b (hpos 1) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩`. Conclude with `⟨0, b, sf_isAlg h _ b (hpos 0) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩`.
-/
theorem UpperTheory.V.Af.Cq.signFix :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Module.finrank ℚ E = 2 → ∀ (ψ : HChar (maximalRealSubfield E))
        (a : (maximalRealSubfield E →+* ℂ) → ℤ), IsAlgPos ψ a → ∃ (k : ℕ) (b : ℤ), (ψ * quadChar E ^ k).IsAlg (fun _ => b) := by
  intro E _ _ _ hE ψ a ha
  have h := surjective_algebraMap_real E hE
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
  have ea : a = fun _ => a v.embedding := funext fun φ => by rw [sf_emb_eq h φ v.embedding]
  set b := a v.embedding with hb
  have hpos : ∀ k : ℕ, IsAlgPos (ψ * quadChar E ^ k) (fun _ => b) := fun k => by
    have ho : (quadChar E ^ k).OrderDvd 2 := by
      have := sf_quadChar_order E
      unfold HChar.OrderDvd at this ⊢
      rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
    have := sf_isAlgPos_mul ha (isAlgPos_zero_of_orderDvd two_pos ho)
    rwa [add_zero, ea] at this
  have hval : ∀ k : ℕ, (((ψ * quadChar E ^ k).inf (-1) : ℂˣ) : ℂ) = (ψ.locInf v (-1) : ℂˣ) * (-1) ^ k := fun k => by
    rw [sf_inf_neg_one h _ v, HChar.locInf_mul, locInf_pow, quadChar_locInf]
    simp
  have h2 : ψ.locInf v (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((ψ.locInf v (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb'
  · exact ⟨0, b, sf_isAlg h _ b (hpos 0) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩
  · exact ⟨1, b, sf_isAlg h _ b (hpos 1) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩
  · exact ⟨1, b, sf_isAlg h _ b (hpos 1) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩
  · exact ⟨0, b, sf_isAlg h _ b (hpos 0) v.embedding (by rw [hval, e, hb'.neg_one_zpow]; simp)⟩
