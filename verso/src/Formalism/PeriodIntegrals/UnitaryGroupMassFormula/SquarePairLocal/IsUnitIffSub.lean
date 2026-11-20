import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.MemFixSub

noncomputable section
open Polynomial IsLocalRing

namespace PI.SqPairLocal.FixD

variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)

/- English proof (translation)
Take `⟨u, hu⟩` from `hu`. Establish `hx : σ (x : R) = x` using `(mem_fixSub σ x).1 x.2`. Establish `hinv : (↑u⁻¹ : R) ∈ fixSub σ`. Rewrite using `[mem_fixSub]`. Establish `h1 : σ (↑u⁻¹ : R) * (x : R) = 1`.

Rewrite using `[← hx, ← map_mul, ← hu, Units.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation. Use `isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (x : R) * ↑u⁻¹ = 1`. Rewrite using `[← hu, Units.mul_inv]`.
-/
theorem isUnit_sub {x : fixSub σ} (hu : IsUnit (x : R)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hu
  have hx : σ (x : R) = x := (mem_fixSub σ x).1 x.2
  have hinv : (↑u⁻¹ : R) ∈ fixSub σ := by
    rw [mem_fixSub]
    have h1 : σ (↑u⁻¹ : R) * (x : R) = 1 := by
      rw [← hx, ← map_mul, ← hu, Units.inv_mul, map_one]
    calc σ (↑u⁻¹ : R) = σ (↑u⁻¹ : R) * ((x : R) * ↑u⁻¹) := by rw [← hu, Units.mul_inv, mul_one]
      _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  show (x : R) * ↑u⁻¹ = 1
  rw [← hu, Units.mul_inv]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.map (fixSub σ).subtype, isUnit_sub σ⟩`.
-/
theorem isUnit_iff_sub (x : fixSub σ) : IsUnit x ↔ IsUnit (x : R) :=
  ⟨fun h => h.map (fixSub σ).subtype, isUnit_sub σ⟩

/- English proof (translation)
Use `⟨fun hu => hϖ.not_isUnit ((isUnit_iff_sub σ _).1 hu), fun a b hab => ?_⟩` and prove the remaining obligations. Establish `h' : ϖ = (a : R) * b` using `congrArg Subtype.val hab`. Break down `hϖ.isUnit_or_isUnit h' with ha | hb` into its components or cases. Conclude with `Or.inl (isUnit_sub σ ha)`. Conclude with `Or.inr (isUnit_sub σ hb)`.
-/
theorem irr_sub {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ) :
    Irreducible (⟨ϖ, h⟩ : fixSub σ) := by
  refine ⟨fun hu => hϖ.not_isUnit ((isUnit_iff_sub σ _).1 hu), fun a b hab => ?_⟩
  have h' : ϖ = (a : R) * b := congrArg Subtype.val hab
  rcases hϖ.isUnit_or_isUnit h' with ha | hb
  · exact Or.inl (isUnit_sub σ ha)
  · exact Or.inr (isUnit_sub σ hb)

/- English proof (translation)
Establish `hne : (x : R) ≠ 0` using `fun h0 => hx (Subtype.ext h0)`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne hϖ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hx' : σ (x : R) = x` using `(mem_fixSub σ x).1 x.2`. Establish `hϖ' : σ ϖ = ϖ` using `(mem_fixSub σ ϖ).1 h`.

Establish `hmem : (u : R) ∈ fixSub σ`. Rewrite using `[mem_fixSub]`. Establish `h2 : (x : R) * σ u = (x : R) * u`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_left_cancel₀ hne h2`.

Establish `hU : IsUnit (⟨u, hmem⟩ : fixSub σ)` using `isUnit_sub σ u.isUnit`. Use `Associated.symm (⟨hU.unit, Subtype.ext ?_⟩ : Associated x ((⟨ϖ, h⟩ : fixSub σ) ^ n))` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`. Simplify using `using hu`.
-/
theorem assoc_sub [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ)
    {x : fixSub σ} (hx : x ≠ 0) : ∃ n : ℕ, Associated ((⟨ϖ, h⟩ : fixSub σ) ^ n) x := by
  have hne : (x : R) ≠ 0 := fun h0 => hx (Subtype.ext h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  refine ⟨n, ?_⟩
  have hx' : σ (x : R) = x := (mem_fixSub σ x).1 x.2
  have hϖ' : σ ϖ = ϖ := (mem_fixSub σ ϖ).1 h
  have hmem : (u : R) ∈ fixSub σ := by
    rw [mem_fixSub]
    have h2 : (x : R) * σ u = (x : R) * u := by
      calc (x : R) * σ u = σ (x : R) * σ u := by rw [hx']
        _ = σ ((x : R) * u) := (map_mul σ _ _).symm
        _ = σ (ϖ ^ n) := by rw [hu]
        _ = ϖ ^ n := by rw [map_pow, hϖ']
        _ = (x : R) * u := hu.symm
    exact mul_left_cancel₀ hne h2
  have hU : IsUnit (⟨u, hmem⟩ : fixSub σ) := isUnit_sub σ u.isUnit
  refine Associated.symm (⟨hU.unit, Subtype.ext ?_⟩ : Associated x ((⟨ϖ, h⟩ : fixSub σ) ^ n))
  rw [IsUnit.unit_spec]
  simpa using hu

/- English proof (translation)
The claim follows from `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨⟨ϖ, h⟩, irr_sub σ hϖ h, fun hx => assoc_sub σ hϖ h hx⟩`.
-/
theorem dvr_sub [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ) :
    IsDiscreteValuationRing (fixSub σ) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨ϖ, h⟩, irr_sub σ hϖ h, fun hx => assoc_sub σ hϖ h hx⟩

/- English proof (translation)
Simplify using `only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_sub]`.
-/
theorem mem_max_sub [IsLocalRing R] [IsLocalRing (fixSub σ)] (x : fixSub σ) :
    x ∈ maximalIdeal (fixSub σ) ↔ (x : R) ∈ maximalIdeal R := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_sub]

/- English proof (translation)
Take `⟨k, hk⟩` from `g.binomExpansion c (b - c)`. Establish `e : c + (b - c) = b` using `by ring`. Rewrite `hk` using `[e, hb.eq_zero, hc.eq_zero, zero_add]`. Establish `hfac : (b - c) * (g.derivative.eval c + k * (b - c)) = 0`. Rewrite using `[hk]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm : g.derivative.eval c - g.derivative.eval a₀ ∈ maximalIdeal R`. Take `⟨d, hd'⟩` from `Polynomial.sub_dvd_eval_sub c a₀ g.derivative`. Rewrite using `[hd']`. Conclude with `Ideal.mul_mem_right _ _ hca`.

Establish `hbc : b - c ∈ maximalIdeal R`. Establish `h3` using `Ideal.sub_mem _ hba hca`. Rewrite `h3` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `hu : IsUnit (g.derivative.eval c + k * (b - c))`. Assume the negation of the conclusion as `hnu`.

Establish `h1 : g.derivative.eval c + k * (b - c) ∈ maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Establish `h2 : k * (b - c) ∈ maximalIdeal R` using `Ideal.mul_mem_left _ _ hbc`. Establish `h3` using `Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) hm`. Use `(IsLocalRing.mem_maximalIdeal _).1 ?_ hd` and prove the remaining obligations. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hfac)`.
-/
theorem root_unique [IsLocalRing R] (g : R[X]) (a₀ b c : R) (hb : g.IsRoot b) (hc : g.IsRoot c)
    (hba : b - a₀ ∈ maximalIdeal R) (hca : c - a₀ ∈ maximalIdeal R)
    (hd : IsUnit (g.derivative.eval a₀)) : b = c := by
  obtain ⟨k, hk⟩ := g.binomExpansion c (b - c)
  have e : c + (b - c) = b := by ring
  rw [e, hb.eq_zero, hc.eq_zero, zero_add] at hk
  have hfac : (b - c) * (g.derivative.eval c + k * (b - c)) = 0 := by
    rw [hk]
    ring
  have hm : g.derivative.eval c - g.derivative.eval a₀ ∈ maximalIdeal R := by
    obtain ⟨d, hd'⟩ := Polynomial.sub_dvd_eval_sub c a₀ g.derivative
    rw [hd']
    exact Ideal.mul_mem_right _ _ hca
  have hbc : b - c ∈ maximalIdeal R := by
    have h3 := Ideal.sub_mem _ hba hca
    rwa [sub_sub_sub_cancel_right] at h3
  have hu : IsUnit (g.derivative.eval c + k * (b - c)) := by
    by_contra hnu
    have h1 : g.derivative.eval c + k * (b - c) ∈ maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : k * (b - c) ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hbc
    have h3 := Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) hm
    refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hd
    convert h3 using 1
    ring
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hfac)

/- English proof (translation)
Use `set φ : fixSub σ →+* R := (fixSub σ).subtype with hφ`. Use `set g : R[X] := f.map φ with hgdef`. Establish `hev : ∀ a : fixSub σ, g.eval (a : R) = φ (f.eval a)` using `fun a => by`. Rewrite using `[hgdef, eval_map]`. Conclude with `eval₂_at_apply φ a`.

Establish `hevd : ∀ a : fixSub σ, g.derivative.eval (a : R) = φ (f.derivative.eval a)` using `fun a => by`. Rewrite using `[hgdef, derivative_map, eval_map]`. Conclude with `eval₂_at_apply φ a`. Establish `hcomp : (σ : R →+* R).comp φ = φ`. Use extensionality with `x`.

Conclude with `x.2`. Establish `hσev : ∀ b : R, σ (g.eval b) = g.eval (σ b)` using `fun b => by`. Rewrite using `[hgdef, eval_map, eval_map]`. Use `hom_eval₂ f φ (σ : R →+* R) b` as an intermediate fact. Rewrite `this` using `[hcomp]`.

Conclude with `this`. Establish `hg : g.Monic` using `hf.map φ`. Establish `h₁' : g.eval (a₀ : R) ∈ maximalIdeal R`. Rewrite using `[hev]`. Conclude with `(mem_max_sub σ _).1 h₁`.

Establish `h₂' : IsUnit (g.derivative.eval (a₀ : R))`. Rewrite using `[hevd]`. Conclude with `h₂.map φ`. Take `⟨b, hb, hba⟩` from `HenselianLocalRing.is_henselian g hg (a₀ : R) h₁' h₂'`. Establish `hσb : g.IsRoot (σ b)` using `by show g.eval (σ b) = 0`.

Rewrite using `[← hσev, hb.eq_zero, map_zero]`. Establish `hσa : σ (a₀ : R) = a₀` using `a₀.2`. Establish `hσba : σ b - a₀ ∈ maximalIdeal R`. Establish `e : σ b - a₀ = σ (b - a₀)` using `by rw [map_sub, hσa]`. Rewrite using `[e]`.

Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[notMem_maximalIdeal]`. Establish `hu` using `hn.map (σ.symm : R →+* R)`. Establish `hu' : IsUnit (b - (a₀ : R))` using `by simpa using hu`. Conclude with `(notMem_maximalIdeal.2 hu') hba`.

Establish `hfix : σ b = b` using `root_unique g a₀ (σ b) b hσb hb hσba hba h₂'`. Use `⟨⟨b, hfix⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show f.eval _ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `hev ⟨b, hfix⟩` as an intermediate fact.

Rewrite `this` using `[show ((⟨b, hfix⟩ : fixSub σ) : R) = b from rfl, hb.eq_zero]`. Conclude with `this.symm`. Rewrite using `[mem_max_sub]`. Conclude with `hba`.
-/
theorem hens_sub [HenselianLocalRing R] [IsLocalRing (fixSub σ)] : HenselianLocalRing (fixSub σ) where
  is_henselian f hf a₀ h₁ h₂ := by
    set φ : fixSub σ →+* R := (fixSub σ).subtype with hφ
    set g : R[X] := f.map φ with hgdef
    have hev : ∀ a : fixSub σ, g.eval (a : R) = φ (f.eval a) := fun a => by
      rw [hgdef, eval_map]; exact eval₂_at_apply φ a
    have hevd : ∀ a : fixSub σ, g.derivative.eval (a : R) = φ (f.derivative.eval a) := fun a => by
      rw [hgdef, derivative_map, eval_map]; exact eval₂_at_apply φ a
    have hcomp : (σ : R →+* R).comp φ = φ := by
      ext x; exact x.2
    have hσev : ∀ b : R, σ (g.eval b) = g.eval (σ b) := fun b => by
      rw [hgdef, eval_map, eval_map]
      have := hom_eval₂ f φ (σ : R →+* R) b
      rw [hcomp] at this
      exact this
    have hg : g.Monic := hf.map φ
    have h₁' : g.eval (a₀ : R) ∈ maximalIdeal R := by
      rw [hev]; exact (mem_max_sub σ _).1 h₁
    have h₂' : IsUnit (g.derivative.eval (a₀ : R)) := by
      rw [hevd]; exact h₂.map φ
    obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian g hg (a₀ : R) h₁' h₂'
    have hσb : g.IsRoot (σ b) := by
      show g.eval (σ b) = 0
      rw [← hσev, hb.eq_zero, map_zero]
    have hσa : σ (a₀ : R) = a₀ := a₀.2
    have hσba : σ b - a₀ ∈ maximalIdeal R := by
      have e : σ b - a₀ = σ (b - a₀) := by rw [map_sub, hσa]
      rw [e]
      by_contra hn
      rw [notMem_maximalIdeal] at hn
      have hu := hn.map (σ.symm : R →+* R)
      have hu' : IsUnit (b - (a₀ : R)) := by simpa using hu
      exact (notMem_maximalIdeal.2 hu') hba
    have hfix : σ b = b := root_unique g a₀ (σ b) b hσb hb hσba hba h₂'
    refine ⟨⟨b, hfix⟩, ?_, ?_⟩
    · show f.eval _ = 0
      apply Subtype.ext
      have := hev ⟨b, hfix⟩
      rw [show ((⟨b, hfix⟩ : fixSub σ) : R) = b from rfl, hb.eq_zero] at this
      exact this.symm
    · rw [mem_max_sub]
      exact hba

instance isLocalHom_sub : IsLocalHom (fixSub σ).subtype :=
  ⟨fun _ hx => isUnit_sub σ hx⟩

/- English proof (translation)
The claim follows from `Finite.of_injective _ (IsLocalRing.ResidueField.map (fixSub σ).subtype).injective`.
-/
theorem finite_sub [IsLocalRing R] [IsLocalRing (fixSub σ)] [Finite (ResidueField R)] :
    Finite (ResidueField (fixSub σ)) :=
  Finite.of_injective _ (IsLocalRing.ResidueField.map (fixSub σ).subtype).injective

end FixD

open FixD in
/- English proof (translation)
Introduce `R _ _ _ _ _ σ hσ ϖ hϖ hσϖ`. Establish `h : ϖ ∈ fixSub σ` using `(mem_fixSub σ ϖ).2 hσϖ`. Use `haveI hd := dvr_sub σ hϖ h`. Conclude with `⟨hd, hens_sub σ, finite_sub σ, fun h' => irr_sub σ hϖ h'⟩`.
-/
theorem fixedDVR : FixedDVR := by
  intro R _ _ _ _ _ σ hσ ϖ hϖ hσϖ
  have h : ϖ ∈ fixSub σ := (mem_fixSub σ ϖ).2 hσϖ
  haveI hd := dvr_sub σ hϖ h
  exact ⟨hd, hens_sub σ, finite_sub σ, fun h' => irr_sub σ hϖ h'⟩

end PI.SqPairLocal
