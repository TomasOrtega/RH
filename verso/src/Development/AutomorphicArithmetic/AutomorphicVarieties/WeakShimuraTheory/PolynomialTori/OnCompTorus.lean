import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `e1 : Units.map (F : A →* B) t.1 = s.1` using `Units.ext h1`. Establish `e2 : Units.map (F : A →* B) t.2 = s.2` using `Units.ext h2`. Establish `: Units.map (F : A →* B) (wv t w) = wv s w`. Unfold `wv`. Rewrite using `[map_mul, map_zpow, map_zpow, e1, e2]`.

Conclude with `congrArg Units.val this`.
-/
private theorem wv_map {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ) (s : Bˣ × Bˣ)
    (h1 : F t.1 = s.1) (h2 : F t.2 = s.2) (w : ℤ × ℤ) : F (wv t w : Aˣ) = (wv s w : Bˣ) := by
  have e1 : Units.map (F : A →* B) t.1 = s.1 := Units.ext h1
  have e2 : Units.map (F : A →* B) t.2 = s.2 := Units.ext h2
  have : Units.map (F : A →* B) (wv t w) = wv s w := by
    unfold wv
    rw [map_mul, map_zpow, map_zpow, e1, e2]
  exact congrArg Units.val this

/- English proof (translation)
Rewrite using `[wv_map F t (1, 1) h1 h2]`. Simplify using `[wv]`.
-/
private theorem wv_one {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ)
    (h1 : F t.1 = 1) (h2 : F t.2 = 1) (w : ℤ × ℤ) : F (wv t w : Aˣ) = 1 := by
  rw [wv_map F t (1, 1) h1 h2]
  simp [wv]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩` from `grp R`. Use `⟨{ hom := ⟨⟨fun g => tconj s (r.hom g), by rw [map_one, hone]⟩, fun g h => ?_⟩ cont := fun a b N => ?_ red := fun g a b => ?_ }, fun _ => rfl⟩` and prove the remaining obligations. Use `show tconj s _ = _`. Rewrite using `[map_mul, hmul]`. Use `show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R) * r.hom g a b)`.

Simplify using `only [map_mul]`. Conclude with `(IsLocallyConstant.const _).mul (r.cont a b N)`. Use `show res _ _ ((wv s (wt a b) : R) * r.hom g a b) = _`. Use `wv_one (res O R : R →+* ResidueField O) s h1 h2 (wt a b)` as an intermediate fact. Rewrite `this` using `[RingHom.coe_coe]`.

Rewrite using `[map_mul, this, one_mul, r.red]`.
-/
private theorem conj_lift {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {rbar : Γ →* M4 (ResidueField O)} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R)
    (s : Rˣ × Rˣ) (h1 : res O R s.1 = 1) (h2 : res O R s.2 = 1) :
    ∃ r' : Lift O rbar R, ∀ g, r'.hom g = tconj s (r.hom g) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp R
  refine ⟨{ hom := ⟨⟨fun g => tconj s (r.hom g), by rw [map_one, hone]⟩, fun g h => ?_⟩
            cont := fun a b N => ?_
            red := fun g a b => ?_ }, fun _ => rfl⟩
  · show tconj s _ = _
    rw [map_mul, hmul]
  · show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R) * r.hom g a b)
    simp only [map_mul]
    exact (IsLocallyConstant.const _).mul (r.cont a b N)
  · show res _ _ ((wv s (wt a b) : R) * r.hom g a b) = _
    have := wv_one (res O R : R →+* ResidueField O) s h1 h2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [map_mul, this, one_mul, r.red]

/- English proof (translation)
Introduce `O _ _ _ _ Γ _ _ rbar P ρ₀ hmap htor R _ _ _ r r' s h1 h2 hr ⟨B, _, _, _, _, ρ, hP, ⟨x, hx⟩, y, hy⟩`. Use `haveI : IsCO O (MvPowerSeries (Fin 2) B) := co_mvps O B (Fin 2)`. Use `haveI : IsDomain (MvPowerSeries (Fin 2) B) := NoZeroDivisors.to_isDomain _`. Set `c : B →ₐ[O] MvPowerSeries (Fin 2) B` to `IsScalarTower.toAlgHom O B _`. Establish `hu : ∀ i : Fin 2, IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin 2) B)` using `fun i => by`.

Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Set `t : (MvPowerSeries (Fin 2) B)ˣ × (MvPowerSeries (Fin 2) B)ˣ` to `((hu 0).unit, (hu 1).unit)`. Establish `ht1 : (t.1 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 0` using `rfl`. Establish `ht2 : (t.2 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 1` using `rfl`.

Take `⟨x', ⟨xC, xX⟩, -⟩` from `co_ev O B O (Fin 2) x (fun _ => 0) fun _ => zero_mem _`. Establish `x1 : x' t.1 = 1` using `by rw [ht1, map_add, map_one, xX, add_zero]`. Establish `x2 : x' t.2 = 1` using `by rw [ht2, map_add, map_one, xX, add_zero]`. Take `⟨y', ⟨yC, yX⟩, -⟩` from `co_ev O B R (Fin 2) y ![(s.1 : R) - 1, (s.2 : R) - 1] fun i => by`. Rewrite using `[← res_eq_zero_iff O]`.

Use `fin_cases i`. Simplify using `[h1]`. Simplify using `[h2]`. Establish `y1 : y' t.1 = s.1` using `by rw [ht1, map_add, map_one, yX]; simp`. Establish `y2 : y' t.2 = s.2` using `by rw [ht2, map_add, map_one, yX]; simp`.

Take `⟨ρ', hρ'⟩` from `conj_lift (ρ.map c) t (by rw [← res_map x', x1, map_one]) (by rw [← res_map x', x2, map_one])`. Establish `he : ∀ g a b, ρ'.hom g a b = (wv t (wt a b)).val * MvPowerSeries.C (ρ.hom g a b)` using `fun g a b => by rw [hρ']; rfl`. Use `⟨MvPowerSeries (Fin 2) B, inferInstance, inferInstance, inferInstance, inferInstance, ρ', htor _ _ _ t hρ' (hmap _ _ c ρ hP), ⟨x', fun g a b => ?_⟩, y', ?_⟩` and prove the remaining obligations. Use `wv_one (x' : MvPowerSeries (Fin 2) B →+* O) t x1 x2 (wt a b)` as an intermediate fact. Rewrite `this` using `[RingHom.coe_coe]`.

Rewrite using `[he, map_mul, this, one_mul, xC, hx]`. Use extensionality with `g a b`. Use `wv_map (y' : MvPowerSeries (Fin 2) B →+* R) t s y1 y2 (wt a b)` as an intermediate fact. Rewrite `this` using `[RingHom.coe_coe]`. Rewrite using `[Lift.map_hom, he, map_mul, this, yC, hr, ← hy]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.Po.onCompTorus :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      (rbar : Γ →* M4 (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* M4 O),
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (r : Lift O rbar R), P R r → P R' (r.map f)) →
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), (∀ g, r'.hom g = tconj s (r.hom g)) → P R r → P R r') →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), res O R s.1 = 1 → res O R s.2 = 1 →
        (∀ g, r'.hom g = tconj s (r.hom g)) → OnComp P ρ₀ r → OnComp P ρ₀ r' := by
  intro O _ _ _ _ Γ _ _ rbar P ρ₀ hmap htor R _ _ _ r r' s h1 h2 hr ⟨B, _, _, _, _, ρ, hP, ⟨x, hx⟩, y, hy⟩
  haveI : IsCO O (MvPowerSeries (Fin 2) B) := co_mvps O B (Fin 2)
  haveI : IsDomain (MvPowerSeries (Fin 2) B) := NoZeroDivisors.to_isDomain _
  let c : B →ₐ[O] MvPowerSeries (Fin 2) B := IsScalarTower.toAlgHom O B _
  have hu : ∀ i : Fin 2, IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin 2) B) := fun i => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  let t : (MvPowerSeries (Fin 2) B)ˣ × (MvPowerSeries (Fin 2) B)ˣ := ((hu 0).unit, (hu 1).unit)
  have ht1 : (t.1 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 0 := rfl
  have ht2 : (t.2 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 1 := rfl
  obtain ⟨x', ⟨xC, xX⟩, -⟩ := co_ev O B O (Fin 2) x (fun _ => 0) fun _ => zero_mem _
  have x1 : x' t.1 = 1 := by rw [ht1, map_add, map_one, xX, add_zero]
  have x2 : x' t.2 = 1 := by rw [ht2, map_add, map_one, xX, add_zero]
  obtain ⟨y', ⟨yC, yX⟩, -⟩ := co_ev O B R (Fin 2) y ![(s.1 : R) - 1, (s.2 : R) - 1] fun i => by
    rw [← res_eq_zero_iff O]
    fin_cases i
    · simp [h1]
    · simp [h2]
  have y1 : y' t.1 = s.1 := by rw [ht1, map_add, map_one, yX]; simp
  have y2 : y' t.2 = s.2 := by rw [ht2, map_add, map_one, yX]; simp
  obtain ⟨ρ', hρ'⟩ := conj_lift (ρ.map c) t (by rw [← res_map x', x1, map_one]) (by rw [← res_map x', x2, map_one])
  have he : ∀ g a b, ρ'.hom g a b = (wv t (wt a b)).val * MvPowerSeries.C (ρ.hom g a b) :=
    fun g a b => by rw [hρ']; rfl
  refine ⟨MvPowerSeries (Fin 2) B, inferInstance, inferInstance, inferInstance, inferInstance, ρ',
    htor _ _ _ t hρ' (hmap _ _ c ρ hP), ⟨x', fun g a b => ?_⟩, y', ?_⟩
  · have := wv_one (x' : MvPowerSeries (Fin 2) B →+* O) t x1 x2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [he, map_mul, this, one_mul, xC, hx]
  · ext g a b
    have := wv_map (y' : MvPowerSeries (Fin 2) B →+* R) t s y1 y2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [Lift.map_hom, he, map_mul, this, yC, hr, ← hy]
    rfl
