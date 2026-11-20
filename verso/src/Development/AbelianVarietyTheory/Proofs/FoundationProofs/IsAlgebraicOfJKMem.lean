import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
open scoped MatrixGroups

open Polynomial

namespace GlobalTheory.K4.LevNormal

open GlobalTheory.KZ

/- English proof (translation)
Rewrite using `[normal_iff]`. Introduce `x`. Establish `hx : IsIntegral F x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `hfin : (Set.range fun σ : L ≃ₐ[F] L => σ x).Finite`.

Use `((minpoly F x).rootSet_finite L).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, rfl⟩`. Rewrite using `[mem_rootSet]`. Use `⟨minpoly.ne_zero hx, ?_⟩` and prove the remaining obligations. Use `show aeval (σ x) (minpoly F x) = 0`.

Rewrite using `[aeval_algHom_apply, minpoly.aeval, map_zero]`. Use `set O := hfin.toFinset with hO`. Use `set P : L[X] := ∏ g ∈ O, (X - C g) with hP`. Establish `hmap : ∀ σ : L ≃ₐ[F] L, P.map (σ : L →+* L) = P`. Introduce `σ`.

Rewrite using `[hP, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, map_X, map_C]`. Use `Finset.prod_bijective σ σ.bijective ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `g`. Simplify using `only [hO, Set.Finite.mem_toFinset, Set.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, rfl⟩`. Conclude with `⟨σ * τ, rfl⟩`. Introduce and unpack `⟨τ, hτ⟩`. Use `⟨σ⁻¹ * τ, ?_⟩` and prove the remaining obligations.

Use `show σ.symm (τ x) = g`. Rewrite using `[hτ, σ.symm_apply_apply]`. Establish `hl : P ∈ lifts (algebraMap F L)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`.

Apply `h` to reduce the goal to its premises. Introduce `σ`. Use `congrArg (fun Q => coeff Q n) (hmap σ)` as an intermediate fact. Simplify `this` using `[coeff_map]`. Establish `hmon : P.Monic` using `monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g`.

Take `⟨Q, hQ⟩` from `(mem_lifts P).1 hl`. Establish `h0 : aeval x Q = 0`. Rewrite using `[aeval_def, ← eval_map, hQ, hP, eval_prod]`. Use `Finset.prod_eq_zero (i := x) ?_ (by simp)` and prove the remaining obligations. Simplify using `only [hO, Set.Finite.mem_toFinset, Set.mem_range]`.

Conclude with `⟨1, rfl⟩`. Establish `hd : (minpoly F x).map (algebraMap F L) ∣ P`. Rewrite using `[← hQ]`. Conclude with `Polynomial.map_dvd _ (minpoly.dvd F x h0)`. Establish `hs : P.Splits` using `Splits.prod fun g _ => Splits.X_sub_C g`.

Conclude with `hs.of_dvd hmon.ne_zero hd`.
-/
theorem normal_of_fixed (F L : Type) [Field F] [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]
    (h : ∀ x : L, (∀ σ : L ≃ₐ[F] L, σ x = x) → x ∈ Set.range (algebraMap F L)) : Normal F L := by
  classical
  rw [normal_iff]
  intro x
  have hx : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨hx, ?_⟩
  have hfin : (Set.range fun σ : L ≃ₐ[F] L => σ x).Finite := by
    refine ((minpoly F x).rootSet_finite L).subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    show aeval (σ x) (minpoly F x) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  set O := hfin.toFinset with hO
  set P : L[X] := ∏ g ∈ O, (X - C g) with hP
  have hmap : ∀ σ : L ≃ₐ[F] L, P.map (σ : L →+* L) = P := by
    intro σ
    rw [hP, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_bijective σ σ.bijective ?_ (fun _ _ => rfl)
    intro g
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨σ * τ, rfl⟩
    · rintro ⟨τ, hτ⟩
      refine ⟨σ⁻¹ * τ, ?_⟩
      show σ.symm (τ x) = g
      rw [hτ, σ.symm_apply_apply]
  have hl : P ∈ lifts (algebraMap F L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply h
    intro σ
    have := congrArg (fun Q => coeff Q n) (hmap σ)
    simpa [coeff_map] using this
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  obtain ⟨Q, hQ⟩ := (mem_lifts P).1 hl
  have h0 : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ, hP, eval_prod]
    refine Finset.prod_eq_zero (i := x) ?_ (by simp)
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, rfl⟩
  have hd : (minpoly F x).map (algebraMap F L) ∣ P := by
    rw [← hQ]
    exact Polynomial.map_dvd _ (minpoly.dvd F x h0)
  have hs : P.Splits := Splits.prod fun g _ => Splits.X_sub_C g
  exact hs.of_dvd hmon.ne_zero hd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective`. Set `A : IntermediateField F X.K` to `algebraicClosure F X.K`. Establish `hc : ∀ c : Ω, algebraMap Ω X.K c ∈ A`. Introduce `c`.

Rewrite using `[mem_algebraicClosure_iff]`. Establish `h1 : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Establish `h2 : IsAlgebraic ℤ (algebraMap Ω X.K c)` using `h1.algHom (algebraMap Ω X.K).toIntAlgHom`. Conclude with `h2.extendScalars (R := ℤ) (S := F) (RingHom.injective_int _)`. Set `B : IntermediateField Ω X.K` to `A.toSubfield.toIntermediateField hc`.

Establish `hle : IntermediateField.adjoin Ω {X.jK} ≤ B`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `A.algebraMap_mem ⟨X.jK, hj⟩`. Establish `h3 : IsAlgebraic A f`. Take `⟨p, hp, h0⟩` from `X.alg_j f`.

Set `φ : IntermediateField.adjoin Ω {X.jK} →+* A` to `(IntermediateField.adjoin Ω {X.jK}).toSubfield.subtype.codRestrict A fun y => hle y.2`. Use `⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_def, eval₂_map]`. Conclude with `h0`. Conclude with `h3.restrictScalars F`.
-/
theorem isAlgebraic_of_jK_mem [Algebra.IsAlgebraic ℚ Ω] (X : Tower Ω ε) (F : Subfield X.K) (hj : X.jK ∈ F) (f : X.K) :
    IsAlgebraic F f := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  let A : IntermediateField F X.K := algebraicClosure F X.K
  have hc : ∀ c : Ω, algebraMap Ω X.K c ∈ A := by
    intro c
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
    have h2 : IsAlgebraic ℤ (algebraMap Ω X.K c) := h1.algHom (algebraMap Ω X.K).toIntAlgHom
    exact h2.extendScalars (R := ℤ) (S := F) (RingHom.injective_int _)
  let B : IntermediateField Ω X.K := A.toSubfield.toIntermediateField hc
  have hle : IntermediateField.adjoin Ω {X.jK} ≤ B := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact A.algebraMap_mem ⟨X.jK, hj⟩
  have h3 : IsAlgebraic A f := by
    obtain ⟨p, hp, h0⟩ := X.alg_j f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* A :=
      (IntermediateField.adjoin Ω {X.jK}).toSubfield.subtype.codRestrict A fun y => hle y.2
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp, ?_⟩
    rw [aeval_def, eval₂_map]
    exact h0
  exact h3.restrictScalars F

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_lev_iff]`. Introduce `γ hγ`. Use `X.recip m f hm (fun δ hδ => hf δ (hΓ hδ)) ζ hζ s 1 (by simpa using hs) γ γ (by simp)` as an intermediate fact. Rewrite using `[← this, hf γ hγ]`.
-/
theorem gal_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    (hΓ : CongruenceSubgroup.Gamma m ≤ Γ') (s : Ω ≃ₐ[ℚ] Ω) (hs : s ζ = ζ) (f : X.K) (hf : f ∈ lev X Γ') :
    X.gal s f ∈ lev X Γ' := by
  rw [mem_lev_iff] at hf ⊢
  intro γ hγ
  have := X.recip m f hm (fun δ hδ => hf δ (hΓ hδ)) ζ hζ s 1 (by simpa using hs) γ γ (by simp)
  rw [← this, hf γ hγ]

/- English proof (translation)
Introduce `Ω _ _ _ ε X Γ' m ζ hm hζ hΓ`. Use `set S := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup with hS`. Use `letI := algMdl X Γ' S`. Use `haveI := isScalarTower_mdl X Γ' S`. Use `haveI : Algebra.IsAlgebraic (mdl X Γ' S) (lev X Γ') := ⟨fun f => (isAlgebraic_algebraMap_iff (A := X.K) (lev X Γ').subtype.injective).1 (isAlgebraic_of_jK_mem X _ (jK_mem_mdl X Γ' S) (f : X.K))⟩`.

Apply `normal_of_fixed` to reduce the goal to its premises. Introduce `x hx`. Use `⟨⟨x, (mem_mdl_iff X Γ' S _).2 ⟨x.2, fun s hs => ?_⟩⟩, rfl⟩` and prove the remaining obligations. Establish `hsζ : s ζ = ζ` using `hs ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} rfl⟩`. Set `φ : lev X Γ' →ₐ[mdl X Γ' S] lev X Γ'` to `{ ((X.gal s).toRingHom.comp (lev X Γ').subtype).codRestrict (lev X Γ') (fun f => gal_mem_lev X Γ' m ζ hm hζ hΓ s hsζ f f.2) with commutes' := fun y => Subtype.ext (((mem_mdl_iff X Γ' S _).1 y.2).2 s hs) }`.

Conclude with `congrArg Subtype.val (hx (AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)))`.
-/
theorem normal : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω), 0 < m → IsPrimitiveRoot ζ m → CongruenceSubgroup.Gamma m ≤ Γ' → letI := GlobalTheory.K4.algMdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup; Normal (GlobalTheory.K4.mdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ ε X Γ' m ζ hm hζ hΓ
  set S := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup with hS
  letI := algMdl X Γ' S
  haveI := isScalarTower_mdl X Γ' S
  haveI : Algebra.IsAlgebraic (mdl X Γ' S) (lev X Γ') := ⟨fun f =>
    (isAlgebraic_algebraMap_iff (A := X.K) (lev X Γ').subtype.injective).1
      (isAlgebraic_of_jK_mem X _ (jK_mem_mdl X Γ' S) (f : X.K))⟩
  apply normal_of_fixed
  intro x hx
  refine ⟨⟨x, (mem_mdl_iff X Γ' S _).2 ⟨x.2, fun s hs => ?_⟩⟩, rfl⟩
  have hsζ : s ζ = ζ := hs ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} rfl⟩
  let φ : lev X Γ' →ₐ[mdl X Γ' S] lev X Γ' :=
    { ((X.gal s).toRingHom.comp (lev X Γ').subtype).codRestrict (lev X Γ')
        (fun f => gal_mem_lev X Γ' m ζ hm hζ hΓ s hsζ f f.2) with
      commutes' := fun y => Subtype.ext (((mem_mdl_iff X Γ' S _).1 y.2).2 s hs) }
  exact congrArg Subtype.val (hx (AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)))

end GlobalTheory.K4.LevNormal
